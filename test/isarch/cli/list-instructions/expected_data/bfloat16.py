# sail-riscv extension: bfloat16
# 6 instruction clauses

INSTRUCTIONS = {
    "FCVT_BF16_S": [
        "fcvt.bf16.s",
    ],
    "FCVT_S_BF16": [
        "fcvt.s.bf16",
    ],
    "VFNCVTBF16_F_F_W": [
        "vfncvtbf16.f.f.w",
    ],
    "VFWCVTBF16_F_F_V": [
        "vfwcvtbf16.f.f.v",
    ],
    "VFWMACCBF16_VF": [
        "vfwmaccbf16.vf",
    ],
    "VFWMACCBF16_VV": [
        "vfwmaccbf16.vv",
    ],
}
