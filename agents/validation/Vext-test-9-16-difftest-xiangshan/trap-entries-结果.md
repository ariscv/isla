# Isla trap 条目(9,109 条)→ XiangShan DiffTest 补漏测试结果

日期:2026-09-18。承接 `验证报告.md`(上次只测了 10,799 条 `Retire_Success`,把 9,045 条 `Illegal_Instruction` 与 64 条 `Memory_Exception` 整体过滤,漏掉 trap 类用例)。

## 方法

- `difftest-xiangshan/pipeline.py` 升级为 trap-aware PoC:
  - 初始化清零 `medeleg`(emu 默认 0x1444 会把 U-mode 非法指令委托到 stvec=0)、设置 `mtvec=trap_handler`
  - payload 指令前加 `payload_ins:` 标签;预期 trap 的条目 payload 后放全零哨兵非法指令
  - handler 以 `mepc == payload_ins` 判定:payload 处 trap(与 Isla 预期一致)→ GOODTRAP;trap 在哨兵/初始化(未按预期 trap 或重建问题)→ 死循环由超时暴露
- 输入:`inputs/rv64_trap_entries.json`(101 个 `make solve` JSON 中全部 ret_val 匹配 `^(Illegal_Instruction|Memory_Exception)` 的条目,9,109 条,全部无 `vr*` 初值)
- 执行:`work/isla-trap-entries/elf/`(9,109 个 ELF),`emu --diff riscv64-nemu-interpreter-so`,timeout 30s,并行 48;逐条增量记录于 `work/isla-trap-entries/elf/results.ndjson`(9,109 行,断点可续)
- 分类明细:`work/isla-trap-entries/classified.json`;分析脚本 `difftest-xiangshan/analyze_trap_results.py`
- 复核手段:failure 日志含 difftest ABORT 差异行或超时 commit trace;关键样本再用 `--no-diff` 纯 RTL 复跑区分"RTL 问题"与"difftest 工具问题"

## 总体结果(经 2026-09-18 空载复证修正)

全量运行(-j48 满载,timeout 30s)得到的 2,952 条 failure 中,461 条 timeout 经空载复测:**399 条为满载假超时**(空载 --diff 全部 GOODTRAP,含下表原 A 类全部 294 条与 B 类 105 条),**仅 62 条空载 --no-diff/--diff 双重复证仍挂**。

| 类别 | 条数(复证后) | 结论 |
|---|---:|---|
| success | 6,157 + 399 假超时 = 6,556 | RTL 与 NEMU 一致且 trap 行为符合 Isla 预期 |
| **C. NEMU 报 illegal、RTL 执行(difftest ABORT)** | **201** | **RTL 漏检非法编码(#6410/#5772 族,补充 case)** |
| **D. vxsat 状态分歧(difftest ABORT)** | **2** | **RTL 不置 vxsat(#6555 补充,附 RTL 根因)** |
| **B. vstart 超界 + 译码检查未覆盖族 → 纯 RTL 挂死** | **62**(34 个指令形态) | **原创 RTL 活性 bug**(0/77 形态有既有报告) |
| E1. vstart>VLMAX 不 trap(payload 执行,哨兵暴露) | 2,251 | RTL+NEMU 均未实现,已知分歧(#6298,维护者称 unimplemented) |
| E2. vstart=VLMAX(LMUL=8)边界不 trap + vsm.v MMIO | 34 + 3 | 34 条 #6298 边界补充;3 条 vsm.v 为独立原创观察 |
| ~~A. 非法 trap 后 difftest 同步挂死~~ | ~~294~~ | **撤销:满载假超时,非 bug** |

## C 类:RTL 漏检非法编码(201 条,全部 vstart≤VLMAX)

现象:NEMU 抬 illegal(mcause=2, mtval=指令编码),XiangShan 直接执行并写回 vd → difftest `mode/mcause/mtval/vd` different → ABORT。
illegal 原因均为 **LMUL 寄存器组未对齐 / 寄存器组约束**类编码,对应 issue #6410(vmove-class misaligned groups,extends #5772,当前 closed/invalid)与已确认的 #5772(vmv4r 未对齐)。

| 指令族 | 条数 | 代表 PoC(case 目录) |
|---|---:|---|
| vmerge.vvm | 58 | `case-048`:vmerge.vvm v31, v1, v0, v0(LMUL=2, vd=v31 未对齐) |
| vmerge.vim | 46 | `case-007`:vmerge.vim v31, v1, 0x0, v0(LMUL=2) |
| vmerge.vxm | 46 | `case-108`:vmerge.vxm v1, v0, x20, v0(LMUL=2) |
| vmv.v.v | 24 | `case-202`:vmv.v.v v30, v2(LMUL=4, vd=v30 未对齐) |
| vmv.v.i | 12 | `case-158`:vmv.v.i v1, -0x2 |
| vmv.v.x | 12 | `case-246`:vmv.v.x v1, x25(LMUL=8) |
| vmv8r.v | 2 | `case-4799`:vmv8r.v v4, v0(vd 须 8 对齐) |
| vmv4r.v | 1 | `case-4805`:vmv4r.v v2, v0(vd 须 4 对齐) |

注:vmerge 族无一例 vd=v0(即不含 #5865 的 vd=v0+masked 形式);本类全部是组未对齐族。

## D 类:vxsat 不置位(2 条)

- `case-1750`:vnclipu.wv v31, v6, v23, v0.t(SEW=8/LMUL=1, vl=7, masked):RTL 与 NEMU 都执行指令,但饱和发生时 **RTL vxsat=0、NEMU vxsat=1** → difftest ABORT(vxsat/vcsr different)
- `case-1792`:vnclipu.wv v4, v28, v0, v0.t(同现象)
- 对照 #6555(vssubu.vx vxsat,报告者撤回)。difftest 视角是硬分歧,可单独提 PoC。

## B 类:vstart 超界时纯 RTL 挂死(167 条)

Sail 对 vstart>VLMAX 报 illegal;XiangShan 不但不 trap,还**停止提交**(连 `--no-diff` 纯 RTL 也无法完成,复核样本 30s 无前进)。分两档:
- vstart 巨大(>2^32,如 0x8000000000000000):76 条,代表 `case-4859`(vrev8.v)、`case-3829`(vid.v)
- vstart 小幅超界(≤2^32 但 >VLMAX):91 条,代表 `case-622`(vaadd.vv v31,v8,v12,v0.t,vstart=0x40 > VLMAX=16,mret 后 payload 永不提交)

对照 #6298(vstart 超界不 trap,维护者称 unimplemented feature)的**活性面**,以及 #6545(vsrl.vv v0.t 挂死,reported):本类把"超界 vstart 挂死"扩展到 vmacc/vaadd/vrev8/vid/vwsll/vnclip/vror 等大量指令族。**即使不 trap 属实现取舍,失去前进是活性缺陷。**

## A 类:difftest 同步挂死(294 条,工具问题)

vstart 在范围内、纯 RTL(`--no-diff`)能正常 trap→handler→GOODTRAP(复核 case-441/1089 等),但连接 NEMU 时 payload trap 后 handler 执行 1-2 条即停止提交,属 difftest/NEMU 同步路径卡死,归入 #5279/#5426 工具范畴,**不记 RTL bug**。
代表:`case-441`(vmacc.vv v4,v0,v4,LMUL=8 未对齐 illegal)。

## E 类:未按 Isla 预期 trap(2,288 条,多数已知)

- E1(2,251):vstart>VLMAX,payload 被 RTL+NEMU 一致执行(写回 vd)→ 哨兵暴露。RTL 与 NEMU 之间无分歧;与 Sail 的分歧即 #6298(已知,维护者立场 unimplemented)。
- E2(37,vstart 范围内):其中 vslideup/vslide1up/vslidedown/vrgather 族(规范明确要求 vstart≠0 时 illegal)约 14+ 条是**双模型一致漏检规范要求**的候选(RTL 与 NEMU 同错,difftest 无法报警,仅 Sail 侧可见);其余为 vstart=VLMAX 边界与 3 条 vsm.v(MMIO 地址 store 未 fault,与 Isla 分歧,归 MMIO 工具差异)。代表:`case-523`(vmadd.vv, vstart=0x80=VLMAX)。

## 复现命令

```bash
cd difftest-xiangshan
# 任一 PoC(以 case-1750 为例)
./xiangshan/build/emu -i work/isla-trap-entries/elf/case-1750/program.elf \
  --diff xiangshan/ready-to-run/riscv64-nemu-interpreter-so --dump-commit-trace
# 纯 RTL 复核
./xiangshan/build/emu -i work/isla-trap-entries/elf/case-622/program.elf --no-diff
# 汇总
python3 analyze_trap_results.py --ndjson work/isla-trap-entries/elf/results.ndjson
```

## 边界说明

- JSON 中 `mstatus` 字段不回放(沿用上次做法,仅设 VS=Dirty);Memory_Exception 条目的 mstatus 多为 VS=Off,Sail 不检查该位而 RTL/NEMU 检查,须开启 VS 才能测到访存行为
- 64 条 Memory_Exception 中 61 条 success(vsm.v 对 MMIO/未映射地址一致 access fault → handler → GOODTRAP),3 条 payload 未 fault(E2)
- `--vlen-bits 128` 与 emu 构建一致;trap 条目无 vr* 初值,无宽度冲突
