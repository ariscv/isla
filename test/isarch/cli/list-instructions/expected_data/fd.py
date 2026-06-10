# sail-riscv extension: FD
# 61 instruction clauses

INSTRUCTIONS = {
    "C_FLD": [
        "c.fld",
    ],
    "C_FLDSP": [
        "c.fldsp",
    ],
    "C_FLW": [
        "c.flw",
    ],
    "C_FLWSP": [
        "c.flwsp",
    ],
    "C_FSD": [
        "c.fsd",
    ],
    "C_FSDSP": [
        "c.fsdsp",
    ],
    "C_FSW": [
        "c.fsw",
    ],
    "C_FSWSP": [
        "c.fswsp",
    ],
    "FCVTMOD_W_D": [
        "fcvtmod.w.d",
    ],
    "FLEQ_D": [
        "fleq.d",
    ],
    "FLEQ_H": [
        "fleq.h",
    ],
    "FLEQ_S": [
        "fleq.s",
    ],
    "FLI_D": [
        "fli.d",
    ],
    "FLI_H": [
        "fli.h",
    ],
    "FLI_S": [
        "fli.s",
    ],
    "FLTQ_D": [
        "fltq.d",
    ],
    "FLTQ_H": [
        "fltq.h",
    ],
    "FLTQ_S": [
        "fltq.s",
    ],
    "FMAXM_D": [
        "fmaxm.d",
    ],
    "FMAXM_H": [
        "fmaxm.h",
    ],
    "FMAXM_S": [
        "fmaxm.s",
    ],
    "FMINM_D": [
        "fminm.d",
    ],
    "FMINM_H": [
        "fminm.h",
    ],
    "FMINM_S": [
        "fminm.s",
    ],
    "FMVH_X_D": [
        "fmvh.x.d",
    ],
    "FMVP_D_X": [
        "fmvp.d.x",
    ],
    "FROUNDNX_D": [
        "froundnx.d",
    ],
    "FROUNDNX_H": [
        "froundnx.h",
    ],
    "FROUNDNX_S": [
        "froundnx.s",
    ],
    "FROUND_D": [
        "fround.d",
    ],
    "FROUND_H": [
        "fround.h",
    ],
    "FROUND_S": [
        "fround.s",
    ],
    "F_BIN_F_TYPE_D": [
        "fmax.d",
        "fmin.d",
        "fsgnj.d",
        "fsgnjn.d",
        "fsgnjx.d",
    ],
    "F_BIN_F_TYPE_H": [
        "fmax.h",
        "fmin.h",
        "fsgnj.h",
        "fsgnjn.h",
        "fsgnjx.h",
    ],
    "F_BIN_RM_TYPE_D": [
        "fadd.d",
        "fdiv.d",
        "fmul.d",
        "fsub.d",
    ],
    "F_BIN_RM_TYPE_H": [
        "fadd.h",
        "fdiv.h",
        "fmul.h",
        "fsub.h",
    ],
    "F_BIN_RM_TYPE_S": [
        "fadd.s",
        "fdiv.s",
        "fmul.s",
        "fsub.s",
    ],
    "F_BIN_TYPE_F_S": [
        "fmax.s",
        "fmin.s",
        "fsgnj.s",
        "fsgnjn.s",
        "fsgnjx.s",
    ],
    "F_BIN_TYPE_X_S": [
        "feq.s",
        "fle.s",
        "flt.s",
    ],
    "F_BIN_X_TYPE_D": [
        "feq.d",
        "fle.d",
        "flt.d",
    ],
    "F_BIN_X_TYPE_H": [
        "feq.h",
        "fle.h",
        "flt.h",
    ],
    "F_MADD_TYPE_D": [
        "fmadd.d",
        "fmsub.d",
        "fnmadd.d",
        "fnmsub.d",
    ],
    "F_MADD_TYPE_H": [
        "fmadd.h",
        "fmsub.h",
        "fnmadd.h",
        "fnmsub.h",
    ],
    "F_MADD_TYPE_S": [
        "fmadd.s",
        "fmsub.s",
        "fnmadd.s",
        "fnmsub.s",
    ],
    "F_UN_F_TYPE_D": [
        "fmv.d.x",
    ],
    "F_UN_F_TYPE_H": [
        "fmv.h.x",
    ],
    "F_UN_RM_FF_TYPE_D": [
        "fcvt.d.s",
        "fcvt.s.d",
        "fsqrt.d",
    ],
    "F_UN_RM_FF_TYPE_H": [
        "fcvt.d.h",
        "fcvt.h.d",
        "fcvt.h.s",
        "fcvt.s.h",
        "fsqrt.h",
    ],
    "F_UN_RM_FF_TYPE_S": [
        "fsqrt.s",
    ],
    "F_UN_RM_FX_TYPE_D": [
        "fcvt.l.d",
        "fcvt.lu.d",
        "fcvt.w.d",
        "fcvt.wu.d",
    ],
    "F_UN_RM_FX_TYPE_H": [
        "fcvt.l.h",
        "fcvt.lu.h",
        "fcvt.w.h",
        "fcvt.wu.h",
    ],
    "F_UN_RM_FX_TYPE_S": [
        "fcvt.l.s",
        "fcvt.lu.s",
        "fcvt.w.s",
        "fcvt.wu.s",
    ],
    "F_UN_RM_XF_TYPE_D": [
        "fcvt.d.l",
        "fcvt.d.lu",
        "fcvt.d.w",
        "fcvt.d.wu",
    ],
    "F_UN_RM_XF_TYPE_H": [
        "fcvt.h.l",
        "fcvt.h.lu",
        "fcvt.h.w",
        "fcvt.h.wu",
    ],
    "F_UN_RM_XF_TYPE_S": [
        "fcvt.s.l",
        "fcvt.s.lu",
        "fcvt.s.w",
        "fcvt.s.wu",
    ],
    "F_UN_TYPE_F_S": [
        "fmv.w.x",
    ],
    "F_UN_TYPE_X_S": [
        "fclass.s",
        "fmv.x.w",
    ],
    "F_UN_X_TYPE_D": [
        "fclass.d",
        "fmv.x.d",
    ],
    "F_UN_X_TYPE_H": [
        "fclass.h",
        "fmv.x.h",
    ],
    "LOAD_FP": [
        "flb",
        "fld",
        "flh",
        "flw",
    ],
    "STORE_FP": [
        "fsb",
        "fsd",
        "fsh",
        "fsw",
    ],
}
