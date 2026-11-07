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
    li t1, 20
    .4byte 0x00a37057 # vsetvli zero, t1, 0xa
    li t0, 2
    .4byte 0x00829073 # csrw vstart, t0
    li t0, 0
    .4byte 0x00a29073 # csrw vxrm, t0
    li t0, 0
    .4byte 0x00929073 # csrw vxsat, t0
payload:
    li x31, 0x1fffffe
payload_ins:
    # payload under test: vsm.v v0, (x31)
    .4byte 0x02bf8027
    # Sentinel illegal instruction: only reached if the payload above did NOT trap
    .4byte 0x00000000
1:  j 1b
trap_handler:
    csrr t0, mepc
    la t1, payload_ins
    bne t0, t1, 2f
    # payload trapped as expected -> GOODTRAP
    # XiangShan DiffTest GOODTRAP custom instruction (0x6b)
    .4byte 0x0000006b
2:  j 2b
.section .data
.align 3
vector_initial_state:
    .dword 0
