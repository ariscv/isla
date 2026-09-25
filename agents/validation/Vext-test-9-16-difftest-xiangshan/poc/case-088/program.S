.option norvc
.section .text.init
.globl _start
_start:
    csrr t0, mstatus
    li t1, 0x600
    or t0, t0, t1
    csrw mstatus, t0
    li t1, 16
    .4byte 0x04037057 # vsetvli zero, t1, 0x40
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
    li x1, 0x7
    li x2, 0x4
    li x3, 0x4
    li x4, 0x4
    li x5, 0x4
    li x6, 0x4
    li x7, 0x4
    li x8, 0x4
    li x9, 0x4
    li x10, 0x4
    li x11, 0x4
    li x12, 0x4
    li x13, 0x4
    li x14, 0x4
    li x15, 0x4
    li x16, 0x4
    li x17, 0x4
    li x18, 0x4
    li x19, 0x4
    li x20, 0x4
    li x21, 0x4
    li x22, 0x4
    li x23, 0x4
    li x24, 0x4
    li x25, 0x4
    li x26, 0x800000000000000c
    li x27, 0x4
    li x28, 0x4
    li x29, 0x4
    li x30, 0x4
    li x31, 0x4
    # Isla: vsetvl x0, x26, x1
    .4byte 0x801d7057
    # XiangShan DiffTest STATE_GOODTRAP custom instruction.
    .4byte 0x0000006b
1:  j 1b
.section .data
.align 3
vector_initial_state:
    .dword 0
