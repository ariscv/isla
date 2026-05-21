# sail-riscv extension: B
# 21 instruction clauses

INSTRUCTIONS = {
    "CLMUL": [
        "clmul",
    ],
    "CLMULH": [
        "clmulh",
    ],
    "CLMULR": [
        "clmulr",
    ],
    "CLZ": [
        "clz",
    ],
    "CLZW": [
        "clzw",
    ],
    "CPOP": [
        "cpop",
    ],
    "CPOPW": [
        "cpopw",
    ],
    "CTZ": [
        "ctz",
    ],
    "CTZW": [
        "ctzw",
    ],
    "ORCB": [
        "orc.b",
    ],
    "REV8": [
        "rev8",
    ],
    "RORI": [
        "rori",
    ],
    "RORIW": [
        "roriw",
    ],
    "SLLIUW": [
        "slli.uw",
    ],
    "ZBA_RTYPE": [
        "sh1add",
        "sh2add",
        "sh3add",
    ],
    "ZBA_RTYPEUW": [
        "add.uw",
        "sh1add.uw",
        "sh2add.uw",
        "sh3add.uw",
    ],
    "ZBB_EXTOP": [
        "sext.b",
        "sext.h",
        "zext.h",
    ],
    "ZBB_RTYPE": [
        "andn",
        "max",
        "maxu",
        "min",
        "minu",
        "orn",
        "rol",
        "ror",
        "xnor",
    ],
    "ZBB_RTYPEW": [
        "rolw",
        "rorw",
    ],
    "ZBS_IOP": [
        "bclri",
        "bexti",
        "binvi",
        "bseti",
    ],
    "ZBS_RTYPE": [
        "bclr",
        "bext",
        "binv",
        "bset",
    ],
}
