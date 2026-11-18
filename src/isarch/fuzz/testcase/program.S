.section .text.init
.globl _start
.option norvc
.option norelax
_start:
    li t0, 0x20008
    csrc mstatus, t0
    csrw satp, zero
    csrw medeleg, zero
    csrw mideleg, zero
    csrw mie, zero
    csrw mcause, zero
    csrw mtval, zero
    csrw mepc, zero
    csrw 0x30a, zero
    la t0, trap_handler
    csrw mtvec, t0
    li t0, -1
    csrw pmpaddr0, t0
    li t0, 0x1f
    csrw pmpcfg0, t0
    la t0, initial_memory
    la t3, initial_memory_end
    beq t0, t3, initial_memory_done
initial_memory_loop:
    ld t1, 0(t0)
    ld t2, 8(t0)
    sd t2, 0(t1)
    addi t0, t0, 16
    bne t0, t3, initial_memory_loop
initial_memory_done:
    fence rw, rw
{{entry_setup}}
{{register_setup}}
payload_ins:
{{payload}}
.balign 4
trap_handler:
{{trap_check}}
check_result:
{{result_check}}
check_memory:
{{memory_check}}
good_trap:
    li a0, 0
good_trap_ins:
    .4byte 0x0005006b
fail_unexpected_trap:
    li a0, 1
fail_unexpected_trap_trap:
    .4byte 0x0005006b
    j fail_unexpected_trap
fail_missing_trap:
    li a0, 1
fail_missing_trap_trap:
    .4byte 0x0005006b
    j fail_missing_trap
fail_rd:
    li a0, 1
fail_rd_trap:
    .4byte 0x0005006b
    j fail_rd
fail_mepc:
    li a0, 1
fail_mepc_trap:
    .4byte 0x0005006b
    j fail_mepc
fail_cause:
    li a0, 1
fail_cause_trap:
    .4byte 0x0005006b
    j fail_cause
fail_tval:
    li a0, 1
fail_tval_trap:
    .4byte 0x0005006b
    j fail_tval
fail_memory:
    li a0, 1
fail_memory_trap:
    .4byte 0x0005006b
    j fail_memory
{{data}}
