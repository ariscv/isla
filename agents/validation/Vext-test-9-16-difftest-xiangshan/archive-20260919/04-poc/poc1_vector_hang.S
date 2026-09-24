# PoC: several vector instruction families permanently stall the core
#       (no trap, no commit), independent of vstart / privilege mode.
# Build: riscv64-unknown-elf-gcc -nostdlib -nostartfiles -static -fno-pic \
#          -march=rv64gcv -mabi=lp64d -Wl,-T,link.ld -Wl,-e,_start -o poc.elf poc1_vector_hang.S
# Run:   ./build/emu -i poc.elf --no-diff          (VLEN=128, MinimalConfig)
# Note:  vstart=0 below; the same hang reproduces with any vstart value,
#        in M-mode or U-mode, with or without difftest.
.option norvc
.section .text.init
.globl _start
_start:
    # Minimal execution environment: enable the vector extension (mstatus.VS = Dirty)
    csrr t0, mstatus
    ori  t0, t0, 0x600
    csrw mstatus, t0

    vsetivli zero, 16, e8, m1, ta, ma   # SEW=8, LMUL=1, vl=16 (all-legal)
    csrw vstart, zero

    vid.v v0                    # <<< BUG TRIGGER: legal instruction, never
                                #     retires; nothing commits afterwards
                                #     (no trap is taken either).
    .4byte 0x0000006b           # GOODTRAP marker - never reached
1:  j 1b
