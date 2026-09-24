.option norvc
.section .text.init
.globl _start
_start:
    csrr t0, mstatus
    li t1, 0x600
    or t0, t0, t1
    csrw mstatus, t0
    li t1, 0
    .4byte 0x40037057 # vsetvli zero, t1, 0x400 (建立 VILL)
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
    li x1, 0x0
    li x2, 0x0
    li x3, 0x0
    li x4, 0x0
    li x5, 0x0
    li x6, 0x0
    li x7, 0x0
    li x8, 0x0
    li x9, 0x0
    li x10, 0x0
    li x11, 0x0
    li x12, 0x0
    li x13, 0x0
    li x14, 0x0
    li x15, 0x0
    li x16, 0x0
    li x17, 0x0
    li x18, 0x0
    li x19, 0x0
    li x20, 0x0
    li x21, 0x0
    li x22, 0x0
    li x23, 0x0
    li x24, 0x0
    li x25, 0x0
    li x26, 0x0
    li x27, 0x0
    li x28, 0x0
    li x29, 0x0
    li x30, 0x0
    li x31, 0x0
    # Isla: vsetvl x0, x31, x0
    .4byte 0x800ff057
    # XiangShan DiffTest STATE_GOODTRAP custom instruction.
    .4byte 0x0000006b
1:  j 1b
.section .data
.align 3
vector_initial_state:
    .dword 0
