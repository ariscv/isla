# sail-riscv extension: vector_crypto
# 35 instruction clauses

INSTRUCTIONS = {
    "VAESDF": [
        "vaesdf.vs",
        "vaesdf.vv",
    ],
    "VAESDM": [
        "vaesdm.vs",
        "vaesdm.vv",
    ],
    "VAESEF": [
        "vaesef.vs",
        "vaesef.vv",
    ],
    "VAESEM": [
        "vaesem.vs",
        "vaesem.vv",
    ],
    "VAESKF1_VI": [
        "vaeskf1.vi",
    ],
    "VAESKF2_VI": [
        "vaeskf2.vi",
    ],
    "VAESZ_VS": [
        "vaesz.vs",
    ],
    "VANDN_VV": [
        "vandn.vv",
    ],
    "VANDN_VX": [
        "vandn.vx",
    ],
    "VBREV8_V": [
        "vbrev8.v",
    ],
    "VBREV_V": [
        "vbrev.v",
    ],
    "VCLMULH_VV": [
        "vclmulh.vv",
    ],
    "VCLMULH_VX": [
        "vclmulh.vx",
    ],
    "VCLMUL_VV": [
        "vclmul.vv",
    ],
    "VCLMUL_VX": [
        "vclmul.vx",
    ],
    "VCLZ_V": [
        "vclz.v",
    ],
    "VCPOP_V": [
        "vcpop.v",
    ],
    "VCTZ_V": [
        "vctz.v",
    ],
    "VGHSH_VV": [
        "vghsh.vv",
    ],
    "VGMUL_VV": [
        "vgmul.vv",
    ],
    "VREV8_V": [
        "vrev8.v",
    ],
    "VROL_VV": [
        "vrol.vv",
    ],
    "VROL_VX": [
        "vrol.vx",
    ],
    "VROR_VI": [
        "vror.vi",
    ],
    "VROR_VV": [
        "vror.vv",
    ],
    "VROR_VX": [
        "vror.vx",
    ],
    "VSHA2MS_VV": [
        "vsha2ms.vv",
    ],
    "VSM3C_VI": [
        "vsm3c.vi",
    ],
    "VSM3ME_VV": [
        "vsm3me.vv",
    ],
    "VSM4K_VI": [
        "vsm4k.vi",
    ],
    "VWSLL_VI": [
        "vwsll.vi",
    ],
    "VWSLL_VV": [
        "vwsll.vv",
    ],
    "VWSLL_VX": [
        "vwsll.vx",
    ],
    "ZVKSHA2TYPE": [
        "vsha2ch.vv",
        "vsha2cl.vv",
    ],
    "ZVKSM4RTYPE": [
        "vsm4r.vs",
        "vsm4r.vv",
    ],
}
