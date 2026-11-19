//! 将认证样本编译为 XiangShan 的独立测试程序。

use super::TestcaseOptions;
use isla_lib::executor::samples::Sample;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

mod layout;
mod sample;
pub use layout::check_exit_layout;
pub use sample::{Harness, PagingIsa, Platform, Region};

pub(super) const FAILURE_REASONS: [&str; 7] =
    ["unexpected_trap", "missing_trap", "rd", "mepc", "cause", "tval", "memory"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EntryMode {
    Mprv,
    S,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Access {
    Load,
    Store,
}

#[derive(Debug, Serialize)]
pub struct Instruction {
    pub access: Access,
    pub offset: i16,
    pub base: u8,
    pub register: u8,
    pub word: u32,
    pub width: u64,
    pub unsigned: bool,
    pub assembly: String,
}

#[derive(Debug, Serialize)]
pub struct Expected {
    pub cause: u64,
    pub tval: u64,
    pub rd: Option<u64>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Word {
    pub address: u64,
    pub value: u64,
    pub expected_value: u64,
}

#[derive(Debug, Serialize)]
pub struct Construction {
    pub walk: Vec<WalkSlot>,
    pub stop: StopReason,
    pub data: Option<DataCheck>,
    pub bytes: Vec<ByteOrigin>,
    pub undetermined: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct WalkSlot {
    pub level: usize,
    pub slot_pa: u64,
    pub pte_value: Option<u64>,
    pub source: SlotSource,
    /// 下一级表的物理基址。
    pub next: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SlotSource {
    Solved,
    Missing,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "reason", rename_all = "snake_case")]
pub enum StopReason {
    Leaf { level: usize, pa: u64 },
    Invalid { level: usize },
    NonCanonical,
    MissingBytes { level: usize, slot_pa: u64 },
    HoleExpectedFault,
    NoTranslation,
}

#[derive(Debug, Serialize)]
pub struct DataCheck {
    pub va: u64,
    pub leaf_pa: u64,
    pub width: u64,
    pub expected_bytes_match: Option<bool>,
}

#[derive(Debug, Default, Serialize)]
pub struct ByteOrigin {
    pub address: u64,
    pub solved: u8,
    pub unknown_old_filled: u8,
    pub zero_padded: u8,
    pub decoy: u8,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub instruction_fetch: Option<u8>,
}

#[derive(Debug, Serialize)]
pub struct Generated {
    pub registers: BTreeMap<String, u64>,
    pub satp: u64,
    pub status: u64,
    pub instruction: Instruction,
    pub expected: Expected,
    pub writes: Vec<Word>,
    pub pte_addresses: Vec<u64>,
    pub assembly: String,
    pub linker: String,
    pub construction: Construction,
}

#[derive(Debug, Serialize)]
pub struct Built {
    pub elf: PathBuf,
    pub symbols: BTreeMap<String, u64>,
    pub build_command: Vec<String>,
}

pub fn generate(sample: &Sample, platform: &Platform, mode: EntryMode) -> Result<Generated, String> {
    let mut generated = sample::prepare(sample, platform, mode).map_err(sample::PreparationError::into_detail)?;
    let mut entry = format!(
        "    li t0, {:#x}\n    csrw satp, t0\n    sfence.vma x0, x0\n    li t0, {:#x}\n    csrw mscratch, t0\n",
        generated.satp, generated.status
    );
    if mode == EntryMode::S {
        entry.push_str("    la t0, s_entry\n    csrw mepc, t0\n");
    }
    let mut register_setup = String::from("    la t0, initial_registers\n");
    let mut data = String::from(".section .rodata, \"a\", @progbits\n.balign 8\ninitial_registers:\n");
    let mut t0_offset = None;
    for (offset, (register, value)) in generated.registers.iter().enumerate() {
        writeln!(data, "    .dword {value:#x}").unwrap();
        if register == "x5" {
            t0_offset = Some(offset * 8);
        } else {
            writeln!(register_setup, "    ld {register}, {}(t0)", offset * 8).unwrap();
        }
    }
    if let Some(offset) = t0_offset {
        writeln!(register_setup, "    ld t0, {offset}(t0)").unwrap();
    }
    // 全部表读取都发生在 MPRV=0 的 M 态；交换保护 t0 的样本初值。
    register_setup.push_str("    csrrw t0, mscratch, t0\n    csrw mstatus, t0\n    csrrw t0, mscratch, t0\n");
    if mode == EntryMode::S {
        register_setup.push_str("    mret\ns_entry:\n");
    }
    let saved_rd = if generated.instruction.register == 31 { "x30" } else { "x31" };
    let capture = if generated.instruction.access == Access::Load {
        format!("    mv {saved_rd}, x{}\n", generated.instruction.register)
    } else {
        String::new()
    };
    let read_trap =
        "    li t0, 0x20000\n    csrc mstatus, t0\n    csrr s0, mcause\n    csrr s1, mtval\n    csrr s2, mepc\n";
    let mut payload = format!("    .4byte {:#010x}\n{capture}", generated.instruction.word);
    if mode == EntryMode::S {
        payload.push_str("s_return:\n    ecall\n    j fail_missing_trap\n");
    } else {
        payload.push_str(read_trap);
    }
    payload.push_str(if generated.expected.cause == 0 { "    j check_result\n" } else { "    j fail_missing_trap\n" });
    let mut trap_check = format!("{capture}{read_trap}");
    if generated.expected.cause == 0 {
        trap_check.push_str(if mode == EntryMode::S {
            "    la t0, s_return\n    bne s2, t0, fail_unexpected_trap\n    li t0, 9\n    bne s0, t0, fail_cause\n    bnez s1, fail_tval\n    j check_result\n"
        } else { "    j fail_unexpected_trap\n" });
    } else {
        writeln!(trap_check, "    la t0, payload_ins\n    bne s2, t0, fail_mepc\n    li t0, {}\n    bne s0, t0, fail_cause\n    li t0, {:#x}\n    bne s1, t0, fail_tval\n    j check_result", generated.expected.cause, generated.expected.tval).unwrap();
    }
    let result_check = match generated.expected.rd {
        Some(value) => format!("    li t0, {value:#x}\n    bne {saved_rd}, t0, fail_rd\n"),
        None => String::new(),
    };
    let mut memory_check =
        if generated.writes.is_empty() { String::from("    bne zero, zero, fail_memory\n") } else { String::new() };
    let linker = String::from("OUTPUT_ARCH(\"riscv\")\nENTRY(_start)\nSECTIONS {\n  .text.init 0x80000000 : { KEEP(*(.text.init)) }\n  . = ALIGN(8);\n  .rodata : { *(.rodata) }\n  ASSERT(. <= 0x80100000, \"代码与初始化表超出代码窗口\")\n  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) }\n}\n");
    // 高地址 ELF 段会扩大 emu 的初始映像，实测无法在预算内完成初始化。
    // 统一使用代码窗口内的地址/值表，通过骨架里的同一个循环写入所有样本内存。
    data.push_str("initial_memory:\n");
    for word in &generated.writes {
        writeln!(
            memory_check,
            "    li t0, {:#x}\n    ld t2, 0(t0)\n    li t1, {:#x}\n    bne t2, t1, fail_memory",
            word.address, word.expected_value
        )
        .unwrap();
        writeln!(data, "    .dword {:#x}\n    .dword {:#x}", word.address, word.value).unwrap();
    }
    data.push_str("initial_memory_end:\n");
    let mut assembly = include_str!("testcase/program.S").to_owned();
    for (name, value) in [
        ("entry_setup", entry),
        ("register_setup", register_setup),
        ("payload", payload),
        ("trap_check", trap_check),
        ("result_check", result_check),
        ("memory_check", memory_check),
        ("data", data),
    ] {
        // 空的 result_check 不额外占行，保证固定检查及出口与旧汇编一致。
        let placeholder = format!("{{{{{name}}}}}\n");
        assert_eq!(assembly.matches(&placeholder).count(), 1, "汇编骨架占位符必须唯一");
        assembly = assembly.replace(&placeholder, &value);
    }
    assert!(!assembly.contains("{{"), "汇编骨架仍有未替换占位符");
    generated.assembly = assembly;
    generated.linker = linker;
    Ok(generated)
}

/// 只负责 L1；这里不启动 emu，也不替换现有差分执行器。
pub fn build_case(
    sample: &Sample,
    platform: &Platform,
    options: &TestcaseOptions,
    output: &Path,
) -> Result<Built, String> {
    let generated = generate(sample, platform, options.entry_mode)?;
    build(&generated, options, output)
}

pub fn build(generated: &Generated, options: &TestcaseOptions, output: &Path) -> Result<Built, String> {
    std::fs::create_dir_all(output).map_err(|e| e.to_string())?;
    let output = std::fs::canonicalize(output).map_err(|e| e.to_string())?;
    let assembly = output.join("program.S");
    let linker = output.join("xiangshan.ld");
    let elf = output.join("program.elf");
    std::fs::write(&assembly, &generated.assembly).map_err(|e| e.to_string())?;
    std::fs::write(&linker, &generated.linker).map_err(|e| e.to_string())?;
    let arguments = vec![
        "-nostdlib".to_owned(),
        "-nostartfiles".into(),
        "-static".into(),
        "-fno-pic".into(),
        "-march=rv64gc".into(),
        "-mabi=lp64d".into(),
        format!("-Wl,-T,{}", linker.display()),
        "-Wl,-e,_start".into(),
        "-o".into(),
        elf.display().to_string(),
        assembly.display().to_string(),
    ];
    let compiled =
        Command::new(&options.compiler).args(&arguments).output().map_err(|e| format!("启动编译器失败：{e}"))?;
    let log = format!("{}{}", String::from_utf8_lossy(&compiled.stdout), String::from_utf8_lossy(&compiled.stderr));
    std::fs::write(output.join("build.log"), &log).map_err(|e| e.to_string())?;
    if !compiled.status.success() {
        return Err(format!("编译失败：{}\n{log}", compiled.status));
    }
    // 与旧 build_case 同样按 GCC 前缀寻找 binutils；不把命令或路径写死。
    let compiler = options.compiler.to_str().ok_or("编译器路径必须为 UTF-8")?;
    let prefix = compiler.strip_suffix("gcc").ok_or("编译器名必须以 gcc 结尾，以定位配套 nm/objdump")?;
    let mut symbols = BTreeMap::new();
    let nm = Command::new(format!("{prefix}nm")).arg("-n").arg(&elf).output().map_err(|e| e.to_string())?;
    if !nm.status.success() {
        return Err(format!("nm 失败：{}", String::from_utf8_lossy(&nm.stderr)));
    }
    let nm = String::from_utf8(nm.stdout).map_err(|e| e.to_string())?;
    std::fs::write(output.join("symbols.txt"), &nm).map_err(|e| e.to_string())?;
    for line in nm.lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        if fields.len() == 3 {
            let address = u64::from_str_radix(fields[0], 16).map_err(|e| e.to_string())?;
            if symbols.insert(fields[2].to_owned(), address).is_some() {
                return Err("出口静态检查：重复符号".into());
            }
        }
    }
    let disassembly = Command::new(format!("{prefix}objdump"))
        .args(["-d", "-M", "no-aliases"])
        .arg(&elf)
        .output()
        .map_err(|e| e.to_string())?;
    if !disassembly.status.success() {
        return Err(format!("objdump 失败：{}", String::from_utf8_lossy(&disassembly.stderr)));
    }
    let disassembly = String::from_utf8(disassembly.stdout).map_err(|e| e.to_string())?;
    std::fs::write(output.join("objdump.txt"), &disassembly).map_err(|e| e.to_string())?;
    check_exit_layout(&disassembly, &symbols)?;
    if symbols.get("trap_handler").ok_or("缺少 trap_handler")? % 4 != 0 {
        return Err("handler 未按 4 字节对齐".into());
    }
    let mut command = vec![compiler.to_owned()];
    command.extend(arguments);
    let built = Built { elf, symbols, build_command: command };
    super::io::write_json(&output.join("case.json"), &built);
    Ok(built)
}
