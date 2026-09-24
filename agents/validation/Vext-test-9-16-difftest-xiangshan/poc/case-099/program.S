.option norvc
.section .text.init
.globl _start
_start:
    csrr t0, mstatus
    li t1, 0x600
    or t0, t0, t1
    csrw mstatus, t0
    li t1, 3
    .4byte 0x01037057 # vsetvli zero, t1, 0x10
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
    li x1, 0x14
    li x2, 0x14
    li x3, 0x14
    li x4, 0x14
    li x5, 0x14
    li x6, 0x14
    li x7, 0x14
    li x8, 0x14
    li x9, 0x14
    li x10, 0x14
    li x11, 0x14
    li x12, 0x14
    li x13, 0x14
    li x14, 0x14
    li x15, 0x14
    li x16, 0x14
    li x17, 0x14
    li x18, 0x14
    li x19, 0x14
    li x20, 0x14
    li x21, 0x14
    li x22, 0x14
    li x23, 0x14
    li x24, 0x14
    li x25, 0x14
    li x26, 0x14
    li x27, 0x14
    li x28, 0x14
    li x29, 0x14
    li x30, 0x14
    li x31, 0x14
    # Isla: vsetvl x0, x31, x0
    .4byte 0x800ff057
    # XiangShan DiffTest STATE_GOODTRAP custom instruction.
    .4byte 0x0000006b
1:  j 1b
.section .data
.align 3
vector_initial_state:
    .dword 0
