# sail-riscv extension: Zicsr
# 2 instruction clauses

INSTRUCTIONS = {
    "CSRImm": [
        "csrrci",
        "csrrsi",
        "csrrwi",
    ],
    "CSRReg": [
        "csrrc",
        "csrrs",
        "csrrw",
    ],
}
