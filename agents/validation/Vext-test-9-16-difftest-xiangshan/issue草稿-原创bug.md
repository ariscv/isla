# 原创Bug Issue 草稿 v5(提交就绪,待审批)

日期:2026-09-19。v5 变更:**删除全部附件相关描述**,三份 issue 各自内嵌完整 PoC 源码 + 最小链接脚本,自包含可编译。PoC 终态(全部实测复现):
- poc1(24 行):两代 emu 挂死复现
- poc4(41 行,已精简 x1-x30 无关指令):mtval ABORT 复现
- poc5(86 行,保留全上下文——精简实验证明 U-mode/payload 段为必要要素):vreg ABORT 复现

═══════════════════════════════════════════
## Issue 1 → OpenXiangShan/XiangShan

**Title**: Several vector instruction families permanently stall the core (no trap, no commit)

**Labels**(模板自动): type: bug/reported, module: unknown

**Body**:

### Before start

- [x] I have read the [RISC-V ISA Manual](https://github.com/riscv/riscv-isa-manual) and [XiangShan Documents](https://docs.xiangshan.cc/zh-cn/latest), and I believe this is a XiangShan RTL issue. 我已经阅读过 [RISC-V 指令集手册](https://github.com/riscv/riscv-isa-manual) 和 [香山文档](https://docs.xiangshan.cc/zh-cn/latest),确认这应该是香山 RTL 的问题。
- [x] I have searched previous issues and PRs and did not find anything relevant. 我已经搜索过之前的 issue 和 PR,并没有找到相关的。
- [x] I have reproduced the issue using the latest commit on the default branch. 我已经使用默认分支最新的 commit 复现了问题。
- [x] If this report was generated with AI assistance (otherwise leave unchecked), I have verified the correctness of its content. 如果这是由 AI 生成的,我已经验证了内容的正确性。

### Branch

kunminghu-v3

### Describe the bug

Executing any instruction from a large set of vector families causes the core to stop committing entirely: the instruction never retires, no trap is taken, and nothing commits afterwards. Reproducible with `--no-diff` (pure RTL), in M-mode or U-mode, with `vstart = 0` or any other value — so it is neither a difftest artifact nor vstart-dependent.

Observed families (each verified by a PoC or by batch difftest runs): `vid.v`, `viota.m`, `vwsll.{vi,vv,vx}`, `vandn.{vv,vx}`, `vrol.*`, `vror.*`, `vnclip/vnclipu` (all forms), `vnsra/vnsrl` (all forms), `vadc/vmadc/vmsbc`, `vslide1up/vslide1down/vslidedown`, `vrgather.vv`, `vrev8.v`, `vaaddu`, and the whole widening arithmetic family `vwmacc/vwmul/vwmaccu/vwmaccsu/vwmulsu/vwmulu/vwadd*/vwsub*` (.vx/.vv/.wx/.vi forms).

### Expected behavior

A legal vector instruction in a legal vector state must either execute and retire, or raise an exception. An implementation may choose to trap unsupported instructions with illegal-instruction, but must not stall the pipeline forever.

### To Reproduce

1. Build emu: `NOOP_HOME=$(pwd) make emu CONFIG=MinimalConfig EMU_THREADS=4 SIM_ARGS=--fpga-platform -j$(nproc)`
2. Save the PoC below as `poc.S` and the linker script as `link.ld`, then compile:
   `riscv64-unknown-elf-gcc -nostdlib -nostartfiles -static -fno-pic -march=rv64gcv -mabi=lp64d -Wl,-T,link.ld -Wl,-e,_start -o poc.elf poc.S`
3. Run: `./build/emu -i poc.elf --no-diff --dump-commit-trace`
4. Observe: with `--dump-commit-trace` the last committed instruction is the `csrw vstart`; `vid.v` never commits and the GOODTRAP marker is never reached (verified 30+ s). Substituting `vwmacc.vx v0, x0, v2` (after `vsetvli zero, t1, e32, m1`) shows the same for the widening family.

PoC (VLEN=128):

```asm
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
```

Linker script (`link.ld`):

```
OUTPUT_ARCH("riscv")
ENTRY(_start)
SECTIONS {
  . = 0x80000000;
  .text.init : { KEEP(*(.text.init)) }
  . = ALIGN(0x1000); .text : { *(.text .text.*) }
  . = ALIGN(0x1000); .data : { *(.data .data.* .sdata .sdata.*) }
  .bss (NOLOAD) : { *(.bss .bss.* COMMON) }
  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) }
}
```

### Environment

- Hardware
  - CPU: AMD EPYC 7543 32-Core Processor (128 threads)
  - Memory (GB): 247
  - Storage (GB): 2000
- Software
  - Operating system: Ubuntu 26.04.1 LTS
  - gcc version: riscv64-unknown-elf-gcc (14.2.0+19) 14.2.0
  - java version: openjdk version "25.0.2" 2026-01-20
  - mill version: Mill Build Tool version 0.12.17
- Repo
  - XiangShan commit id: `c8d7b3a`
- Build & Run
  - Build command: `NOOP_HOME=$(pwd) make emu CONFIG=MinimalConfig EMU_THREADS=4 SIM_ARGS=--fpga-platform -j$(nproc)`
  - Run command: `./build/emu -i poc.elf --no-diff --dump-commit-trace`

### Additional context

Note on the build command: a default debug build of the current tree crashes during elaboration (`Rob.scala`, `perfDebugInfo.get`); `SIM_ARGS=--fpga-platform` keeps `--enable-difftest` from the default DEBUG args and works around it (irrelevant for this `--no-diff` report, included for reproducibility).

If some of the affected families are considered work-in-progress in the current vector unit, an illegal-instruction trap would still be the correct intermediate behavior — a silent permanent stall is not; the family list above may help close them out.

This report was prepared with AI assistance (Claude, Anthropic); reproduction steps and logs were verified against actual runs.

═══════════════════════════════════════════
## Issue 2 → OpenXiangShan/XiangShan

**Title**: vsm.v store access fault reports the base address in mtval instead of the first faulting byte

**Labels**(模板自动): type: bug/reported, module: unknown

**Body**:

### Before start

(四项勾选,与 Issue 1 逐字相同)

### Branch

kunminghu-v3

### Describe the bug

When `vsm.v` (vector mask store) triggers a store access fault, the DUT reports the store **base address** in mtval while NEMU reports the **first faulting byte** address.

Setup: SEW=16/LMUL=4, vl=20, `vstart=2` (so the mask store writes its remaining byte(s) starting at base+2), base `x31 = 0x1fffffe` where bytes `0x1fffffe..0x1fffff` are accessible and `0x2000000+` are not. Both sides take the same store access fault (mcause matches), then difftest aborts on mtval:

```
mtval different ... right = 0x0000000002000000, wrong = 0x0000000001fffffe
```

NEMU (`right`) = 0x2000000, the first byte actually being stored that faults; DUT (`wrong`) = 0x1fffffe, the base address of the store.

### Expected behavior

mtval on a vector store access fault should report the effective address of the first faulting byte being stored, matching the reference model.

### To Reproduce

1. Build emu: `NOOP_HOME=$(pwd) make emu CONFIG=MinimalConfig EMU_THREADS=4 SIM_ARGS=--fpga-platform -j$(nproc)`
2. Compile the PoC below (same command and `link.ld` as in the family-stall report; entry at 0x80000000)
3. Run: `./build/emu -i poc.elf --diff ready-to-run/riscv64-nemu-interpreter-so`
4. Observe the difftest abort at the vsm.v trap with the mtval diff above.

PoC:

```asm
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
    .4byte 0x00a37057 # vsetvli zero, t1, 0xa   (SEW=16, LMUL=4, tu, mu)
    li t0, 2
    .4byte 0x00829073 # csrw vstart, t0
    li t0, 0
    .4byte 0x00a29073 # csrw vxrm, t0
    li t0, 0
    .4byte 0x00929073 # csrw vxsat, t0
payload:
    li x31, 0x1fffffe           # store base: bytes ..0x1fffff accessible, 0x2000000+ not
payload_ins:
    vsm.v v0, (x31)             # <<< BUG TRIGGER: store access fault on both sides,
                                #     but mtval differs (DUT=base, NEMU=first faulting byte)
    .4byte 0x00000000           # Sentinel illegal instruction: only reached if the
                                #     payload above did NOT trap
1:  j 1b
trap_handler:
    csrr t0, mepc
    la t1, payload_ins
    bne t0, t1, 2f
    .4byte 0x0000006b           # payload trapped as expected -> GOODTRAP
2:  j 2b
```

(Linker script identical to the one included in the family-stall report.)

### Environment

- Hardware
  - CPU: AMD EPYC 7543 32-Core Processor (128 threads)
  - Memory (GB): 247
  - Storage (GB): 2000
- Software
  - Operating system: Ubuntu 26.04.1 LTS
  - gcc version: riscv64-unknown-elf-gcc (14.2.0+19) 14.2.0
  - java version: openjdk version "25.0.2" 2026-01-20
  - mill version: Mill Build Tool version 0.12.17
- Repo
  - XiangShan commit id: `c8d7b3a`
  - NEMU commit id (if difftest failed with NEMU): `ready-to-run @ 4cf9983 (bundled riscv64-nemu-interpreter-so)`
- Build & Run
  - Build command: `NOOP_HOME=$(pwd) make emu CONFIG=MinimalConfig EMU_THREADS=4 SIM_ARGS=--fpga-platform -j$(nproc)`
  - Run command: `./build/emu -i poc.elf --diff ready-to-run/riscv64-nemu-interpreter-so`

### Additional context

Guess: the vector store fault address for mask stores is taken from the store's base address (or first element) rather than the faulting element's byte address, in the vector store path.

This report was prepared with AI assistance (Claude, Anthropic); reproduction steps and logs were verified against actual runs.

═══════════════════════════════════════════
## Issue 3 → OpenXiangShan/difftest

**Title**: [BUG] DUT vector register writes never reach the REF state (vregs stuck at initial pattern)

**Labels**(模板自动): bug

**Body**(按 difftest bug_report.md 模板字段):

**Related component**: simulation framework

**Describe the bug**

With an emu built from the latest XiangShan kunminghu-v3 integrating the current difftest framework, vector register writes committed by the DUT are not reflected in the NEMU-side reference state. At a vector-register comparison point, the DUT shows the written value while the REF still shows its initial pattern.

Minimal PoC (VLEN=128, full source below): the program loads **all 32 vregs** with a 0x55 pattern via `vl1re8.v v0..v31`, then runs a short payload in U-mode. Difftest aborts at the first vreg comparison point during the load sequence:

```
v2_low  different ... right = 0xffffffff00000000, wrong = 0x5555555555555555
v2_high different ... right = 0xffffffffffffffff, wrong = 0x5555555555555555
```

The DUT side (`wrong`) shows the 0x55 pattern written by the guest; the NEMU side (`right`) never updates from its initial pattern. The same behavior appears with two different NEMU so builds (the bundled one and an older one), pointing to the vreg synchronization path rather than a specific REF build. Practical consequence: any guest workload that leaves part of the vreg file untouched — i.e. virtually every short vector test — cannot pass difftest.

**To Reproduce**

Steps to reproduce the behavior (no source modifications):
1. Clone XiangShan kunminghu-v3 with its bundled difftest submodule
2. Build with the command `NOOP_HOME=$(pwd) make emu CONFIG=MinimalConfig EMU_THREADS=4 SIM_ARGS=--fpga-platform -j$(nproc)`
3. Compile the PoC below (`riscv64-unknown-elf-gcc -nostdlib -nostartfiles -static -fno-pic -march=rv64gcv -mabi=lp64d -Wl,-T,link.ld -Wl,-e,_start -o poc.elf poc.S`; link script places the image at 0x80000000)
4. Run `./build/emu -i poc.elf --diff ready-to-run/riscv64-nemu-interpreter-so`
5. See the spurious `vXX_low/high different` abort shown above

PoC:

```asm
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
    .dword 0```

(Linker script: image at 0x80000000, `.text.init` first — same as the XiangShan reports.)

**Expected behavior**

Vector register writes committed by the DUT must be synchronized into the REF's architectural vreg state (as in earlier builds), so vreg comparisons reflect actual DUT behavior instead of the REF's initial pattern.

**Screenshots**

Not applicable; the difftest abort lines are quoted inline above.

**What you expect us (DiffTest developers) to do for you**

Confirm whether the vreg synchronization path (vreg diff bundle / DPIC) changed recently in a way that requires additional integration on the DUT side, or whether this is a framework regression; a pointer to the expected sync mechanism would help debugging on the emu side.

**Additional context**

Environment: AMD EPYC 7543 (128 threads), 247 GB RAM, Ubuntu 26.04.1 LTS, riscv64-unknown-elf-gcc 14.2.0, Verilator 5.038, mill 0.12.17, openjdk 25.0.2; XiangShan `c8d7b3a`, NEMU so `ready-to-run @ 4cf9983`.

Note for building: a default debug build of the current XiangShan tree crashes during elaboration (`Rob.scala`, `perfDebugInfo.get`); `SIM_ARGS=--fpga-platform` (which keeps `--enable-difftest`) works around it and reproduces this issue.

This report was prepared with AI assistance (Claude, Anthropic); reproduction steps and logs were verified against actual runs.

═══════════════════════════════════════════
(草稿完;`poc-final/` 保留三个 .S/.elf 与 link.ld 作为本地存档,issue 正文不引用附件)
