# sail-riscv extension: I
# 20 instruction clauses

INSTRUCTIONS = {
    "ADDIW": [
        "addiw",
    ],
    "BTYPE": [
        "beq",
        "bge",
        "bgeu",
        "blt",
        "bltu",
        "bne",
    ],
    "EBREAK": [
        "ebreak",
    ],
    "ECALL": [
        "ecall",
    ],
    "FENCE": [
        "fence",
    ],
    "FENCE_TSO": [
        "fence.tso",
    ],
    "ITYPE": [
        "addi",
        "andi",
        "ori",
        "slti",
        "sltiu",
        "xori",
    ],
    "JAL": [
        "jal",
    ],
    "JALR": [
        "jalr",
    ],
    "LOAD": [
        "lb",
        "lbu",
        "ld",
        "ldu",
        "lh",
        "lhu",
        "lw",
        "lwu",
    ],
    "MRET": [
        "mret",
    ],
    "RTYPE": [
        "add",
        "and",
        "or",
        "sll",
        "slt",
        "sltu",
        "sra",
        "srl",
        "sub",
        "xor",
    ],
    "RTYPEW": [
        "addw",
        "sllw",
        "sraw",
        "srlw",
        "subw",
    ],
    "SFENCE_VMA": [
        "sfence.vma",
    ],
    "SHIFTIOP": [
        "slli",
        "srai",
        "srli",
    ],
    "SHIFTIWOP": [
        "slliw",
        "sraiw",
        "srliw",
    ],
    "SRET": [
        "sret",
    ],
    "STORE": [
        "sb",
        "sd",
        "sh",
        "sw",
    ],
    "UTYPE": [
        "auipc",
        "lui",
    ],
    "WFI": [
        "wfi",
    ],
}
