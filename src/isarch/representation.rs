use serde_json::{json, Value};

/// 保留旧编码字段的格式，新增可重放的精确表示；不推断助记符是否合法。
/// FmtVal 的位和掩码没有公共读取接口，因此读取其已有的定宽十六进制格式。
/// 含掩码的值表示尚未完整具体化，不能用其中的占位零生成指令。
pub(super) fn instruction_representations(mnemonic: &str, formatted_encoding: &str) -> Value {
    let incomplete = |reason: &str| {
        json!({
            "mnemonic": mnemonic,
            "encoding": {"status": "incomplete", "reason": reason},
            "insn": {"status": "incomplete", "reason": reason},
        })
    };
    if formatted_encoding.is_empty() {
        return incomplete("没有机器编码");
    }
    if formatted_encoding.starts_with('{') {
        return incomplete("机器编码含未具体化位");
    }
    let (width, digits) = formatted_encoding.split_once("'h").expect("具体机器编码必须是定宽十六进制");
    let width: u32 = width.parse().expect("机器编码位宽必须是整数");
    if !matches!(width, 16 | 32) {
        return incomplete("精确指令表示目前仅支持16或32位编码");
    }
    let digits = digits.replace('_', "");
    let value = u64::from_str_radix(&digits, 16).expect("机器编码必须是十六进制数");
    assert!(value < (1u64 << width), "编码值超出声明位宽");
    let hex = format!("0x{:0digits$x}", value, digits = (width / 4) as usize);
    let bits = format!("{:0width$b}", value, width = width as usize);
    let bytes =
        value.to_le_bytes()[..(width / 8) as usize].iter().map(|byte| format!("{byte:02x}")).collect::<String>();
    json!({
        "mnemonic": mnemonic,
        "encoding": {
            "status": "complete",
            "bit-length": width,
            "bits": bits,
            "hex": hex,
            "bytes-le": bytes,
        },
        "insn": {"status": "complete", "text": format!(".insn {}, {}", width / 8, hex)},
    })
}

#[cfg(test)]
mod tests {
    use super::instruction_representations;
    #[test]
    fn compressed_keeps_width_and_leading_zeroes() {
        let r = instruction_representations("c.nop", "16'h0001");
        assert_eq!(r["mnemonic"], "c.nop");
        assert_eq!(r["encoding"]["bit-length"], 16);
        assert_eq!(r["encoding"]["bits"], "0000000000000001");
        assert_eq!(r["encoding"]["hex"], "0x0001");
        assert_eq!(r["encoding"]["bytes-le"], "0100");
        assert_eq!(r["insn"]["text"], ".insn 2, 0x0001");
    }
    #[test]
    fn illegal_bf16_keeps_mnemonic_and_exact_encoding() {
        let r = instruction_representations("vfwmaccbf16.vf v1, f14, v1", "32'hee17_50d7");
        assert_eq!(r["mnemonic"], "vfwmaccbf16.vf v1, f14, v1");
        assert_eq!(r["encoding"]["hex"], "0xee1750d7");
        assert_eq!(r["encoding"]["bytes-le"], "d75017ee");
        assert_eq!(r["insn"]["text"], ".insn 4, 0xee1750d7");
    }
    #[test]
    fn unresolved_encoding_is_explicitly_incomplete() {
        let r = instruction_representations("fadd.s f0, f0, f0", "{32'h0000_0053, 32'b0000_0000}");
        assert_eq!(r["encoding"]["status"], "incomplete");
        assert_eq!(r["insn"]["status"], "incomplete");
        assert!(r["insn"].get("text").is_none());
    }
    #[test]
    fn missing_and_unsupported_encoding_are_incomplete() {
        for encoding in ["", "48'h123456789abc"] {
            let r = instruction_representations("unchanged", encoding);
            assert_eq!(r["encoding"]["status"], "incomplete");
            assert_eq!(r["mnemonic"], "unchanged");
        }
    }
    #[test]
    #[should_panic(expected = "编码值超出声明位宽")]
    fn encoding_never_truncates() {
        instruction_representations("c.nop", "16'h10001");
    }
}
