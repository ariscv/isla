.option norvc
.section .text.init
.globl _start
_start:
    csrr t0, mstatus
    li t1, 0x600
    or t0, t0, t1
    csrw mstatus, t0
    # Clear medeleg: the default medeleg=0x1444 would delegate U-mode illegal traps to stvec=0
    csrw medeleg, x0
    # All traps enter the M-mode trap_handler; mepc vs payload distinguishes trap location
    la t0, trap_handler
    csrw mtvec, t0
    # Initialize ALL 32 vector registers to a known 0x55 pattern via
    # whole-register loads, so that no register is left untouched:
    .4byte 0xcc087057 # vsetivli zero, 16, e8, m1, ta, ma
    la t0, vreg_pattern
    .4byte 0x02828007 # vl1re8.v v0, (t0)
    .4byte 0x02828087 # vl1re8.v v1, (t0)
    .4byte 0x02828107 # vl1re8.v v2, (t0)
    .4byte 0x02828187 # vl1re8.v v3, (t0)
    .4byte 0x02828207 # vl1re8.v v4, (t0)
    .4byte 0x02828287 # vl1re8.v v5, (t0)
    .4byte 0x02828307 # vl1re8.v v6, (t0)
    .4byte 0x02828387 # vl1re8.v v7, (t0)
    .4byte 0x02828407 # vl1re8.v v8, (t0)
    .4byte 0x02828487 # vl1re8.v v9, (t0)
    .4byte 0x02828507 # vl1re8.v v10, (t0)
    .4byte 0x02828587 # vl1re8.v v11, (t0)
    .4byte 0x02828607 # vl1re8.v v12, (t0)
    .4byte 0x02828687 # vl1re8.v v13, (t0)
    .4byte 0x02828707 # vl1re8.v v14, (t0)
    .4byte 0x02828787 # vl1re8.v v15, (t0)
    .4byte 0x02828807 # vl1re8.v v16, (t0)
    .4byte 0x02828887 # vl1re8.v v17, (t0)
    .4byte 0x02828907 # vl1re8.v v18, (t0)
    .4byte 0x02828987 # vl1re8.v v19, (t0)
    .4byte 0x02828a07 # vl1re8.v v20, (t0)
    .4byte 0x02828a87 # vl1re8.v v21, (t0)
    .4byte 0x02828b07 # vl1re8.v v22, (t0)
    .4byte 0x02828b87 # vl1re8.v v23, (t0)
    .4byte 0x02828c07 # vl1re8.v v24, (t0)
    .4byte 0x02828c87 # vl1re8.v v25, (t0)
    .4byte 0x02828d07 # vl1re8.v v26, (t0)
    .4byte 0x02828d87 # vl1re8.v v27, (t0)
    .4byte 0x02828e07 # vl1re8.v v28, (t0)
    .4byte 0x02828e87 # vl1re8.v v29, (t0)
    .4byte 0x02828f07 # vl1re8.v v30, (t0)
    .4byte 0x02828f87 # vl1re8.v v31, (t0)
    li t1, 1
    .4byte 0x05137057 # vsetvli zero, t1, 0x51
    li t0, 0
    .4byte 0x00829073 # csrw vstart, t0
    li t0, 0
    .4byte 0x00a29073 # csrw vxrm, t0
    li t0, 0
    .4byte 0x00929073 # csrw vxsat, t0
    li t0, -1
    .4byte 0x3b029073 # csrw pmpaddr0, t0
    li t0, 0x1f
    .4byte 0x3a029073 # csrw pmpcfg0, t0
    la t0, payload
    csrw mepc, t0
    csrr t0, mstatus
    li t1, -6145
    and t0, t0, t1
    li t1, 0
    or t0, t0, t1
    csrw mstatus, t0
    mret
payload:
payload_ins:
    # payload under test: vmerge.vxm v2, v0, x0, v0
    .4byte 0x5c004157
    # XiangShan DiffTest STATE_GOODTRAP custom instruction.
    .4byte 0x0000006b
1:  j 1b
trap_handler:
    # No trap expected: any trap parks here (detected as timeout)
2:  j 2b
.section .data
.align 3
vreg_pattern:
    .byte 0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55,0x55
vector_initial_state:
    .dword 0
