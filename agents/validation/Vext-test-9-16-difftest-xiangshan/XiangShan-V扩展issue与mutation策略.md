# XiangShan V 扩展 Issue 核验、真实 PoC 与 Mutation 策略

## 统计口径与结论

固定原始表89个去重Issue，不扩入正文引用。逐条元数据与评论按GitHub缓存核验；时间UTC。总89条、22作者，2024-04-16至2026-09-16，Open57/Closed32。关闭不代表确认。标签和维护者明确评论共同判定，确认状态与缺陷范围独立。

| 范围 | Issue数 | 口径 |
|---|---:|---|
| 已确认RTL/调试问题 | 28 | 含#6022重复根因映射，不等于28独立根因 |
| 已确认性能问题 | 1 | #4190，独立性能oracle |
| 已确认工具问题 | 2 | #5279 DiffTest、#5426 NEMU |
| 行为对齐/已有修复记录 | 1 | #5725，非RTL功能缺陷 |
| 部分确认/分支修复线索 | 2 | #2890历史混合、#6576分支相关 |
| 非确认/撤回/工具历史等 | 27 | 逐项保留证据强度 |
| 待确认 | 28 | 无充分维护者确认证据 |

### 作者统计

| 作者 | 数量 | Open | Closed | 首次～最后 |
|---|---:|---:|---:|---|
| lhb-sec | 20 | 19 | 1 | 2026-05-25～2026-09-11 |
| KnightGOKU | 14 | 10 | 4 | 2026-03-25～2026-05-10 |
| wndmll643 | 8 | 6 | 2 | 2026-07-21～2026-09-16 |
| youzi27 | 8 | 5 | 3 | 2025-11-29～2026-05-11 |
| jimmymtest | 6 | 6 | 0 | 2026-04-20～2026-04-22 |
| LeeHaofeng | 5 | 3 | 2 | 2026-06-07～2026-06-13 |
| zhangkanqi | 5 | 3 | 2 | 2026-04-06～2026-04-08 |
| camel-cdr | 4 | 0 | 4 | 2024-04-16～2025-01-16 |
| cesarus777 | 3 | 0 | 3 | 2025-12-24～2025-12-24 |
| nyh1 | 3 | 0 | 3 | 2026-05-28～2026-05-28 |
| maplejty814 | 2 | 2 | 0 | 2026-06-26～2026-06-29 |
| 0x1B05 | 1 | 1 | 0 | 2026-05-14～2026-05-14 |
| H-Y-B | 1 | 0 | 1 | 2024-11-29～2024-11-29 |
| Hoshi44 | 1 | 1 | 0 | 2026-04-05～2026-04-05 |
| I3eg1nner | 1 | 0 | 1 | 2025-12-26～2025-12-26 |
| Security-HC | 1 | 1 | 0 | 2026-06-26～2026-06-26 |
| WaltJr-OH | 1 | 0 | 1 | 2025-03-06～2025-03-06 |
| biquanha | 1 | 0 | 1 | 2026-03-19～2026-03-19 |
| cyyself | 1 | 0 | 1 | 2024-05-27～2024-05-27 |
| jlong299 | 1 | 0 | 1 | 2024-12-10～2024-12-10 |
| kds1123001 | 1 | 0 | 1 | 2026-08-24～2026-08-24 |
| msuadOf | 1 | 0 | 1 | 2026-08-24～2026-08-24 |

### 时间分布

| 月份 | 数量 |
|---|---:|
| 2024-04 | 1 |
| 2024-05 | 1 |
| 2024-07 | 1 |
| 2024-09 | 1 |
| 2024-11 | 1 |
| 2024-12 | 1 |
| 2025-01 | 1 |
| 2025-03 | 1 |
| 2025-11 | 1 |
| 2025-12 | 5 |
| 2026-03 | 3 |
| 2026-04 | 18 |
| 2026-05 | 21 |
| 2026-06 | 10 |
| 2026-07 | 8 |
| 2026-08 | 3 |
| 2026-09 | 12 |

## 全部89条Issue与确认证据

确认状态：confirmed=明确确认，fixed=有修复标签，partial=部分确认/分支线索，not_confirmed=非确认但应结合范围，reported=待确认。

| Issue/标题 | 作者 | 创建 | 状态 | 确认 | 范围 | 核验依据 |
|---|---|---|---|---|---|---|
| [#2890 Simulation hangs for longer running functions using the vector extension](https://github.com/OpenXiangShan/XiangShan/issues/2890) | camel-cdr | 2024-04-16 | closed | partial | 历史混合/部分确认 | [维护者给出RTL修复PR3140/commit1a0c5d且报告者验证；同帖后续还有nexus-am与VS配置问题，不整帖算单一RTL缺陷](https://github.com/OpenXiangShan/XiangShan/issues/2890#issuecomment-2220740793) |
| [#3012 Difftest failed on a RISC-V Vector memcpy workload with misaligned(in vlen granularity, not element) unit stride load](https://github.com/OpenXiangShan/XiangShan/issues/3012) | cyyself | 2024-05-27 | closed | not_confirmed | 工具/历史修复记录 | [作者cyyself：Fixed NEMU commit b9796f4ec8b8427b4fb995ec948ed345f1caeaf4](https://github.com/OpenXiangShan/XiangShan/issues/3012#issuecomment-2134233149) |
| [#3200 rvv-bench: XiangShan performance problems](https://github.com/OpenXiangShan/XiangShan/issues/3200) | camel-cdr | 2024-07-14 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/3200) |
| [#3488  Why does only one execution unit support vppu? & vcompress optimization suggestion](https://github.com/OpenXiangShan/XiangShan/issues/3488) | camel-cdr | 2024-09-03 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/3488) |
| [#3962 How to turn off vector instruction extension？](https://github.com/OpenXiangShan/XiangShan/issues/3962) | H-Y-B | 2024-11-29 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/3962) |
| [#4017 Store-load violation checking for vector instruction](https://github.com/OpenXiangShan/XiangShan/issues/4017) | jlong299 | 2024-12-10 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/4017) |
| [#4190 KunminghuV2Config doesn't seem to dual issue vector instructions](https://github.com/OpenXiangShan/XiangShan/issues/4190) | camel-cdr | 2025-01-16 | closed | confirmed | 性能/假依赖 | [维护者确认不必要vd依赖性能问题，PR4198修复且报告者回测；LMUL1解码限制另属设计取舍](https://github.com/OpenXiangShan/XiangShan/issues/4190#issuecomment-2597589506) |
| [#4368 Vector Configuration](https://github.com/OpenXiangShan/XiangShan/issues/4368) | WaltJr-OH | 2025-03-06 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/4368) |
| [#5279 Mismatch in vector store commit behavior under misaligned base address](https://github.com/OpenXiangShan/XiangShan/issues/5279) | youzi27 | 2025-11-29 | open | confirmed | 工具/差分测试 | [维护者 Yan-Muzi 明确："known bug of difftest"，非 RTL。](https://github.com/OpenXiangShan/XiangShan/issues/5279#issuecomment-3595092909) |
| [#5288 Unexpected interaction between vs1r.v and fence.i instructions](https://github.com/OpenXiangShan/XiangShan/issues/5288) | youzi27 | 2025-12-01 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5288) |
| [#5424 Mismatch for store commits on vector indexed segment store instructions](https://github.com/OpenXiangShan/XiangShan/issues/5424) | cesarus777 | 2025-12-24 | closed | not_confirmed | 工具/重复映射 | [Yan-Muzi：Please refer to #5279](https://github.com/OpenXiangShan/XiangShan/issues/5424#issuecomment-3689978534) |
| [#5425 Assertion failed at DCache on vector indexed segment store instructions](https://github.com/OpenXiangShan/XiangShan/issues/5425) | cesarus777 | 2025-12-24 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5425) |
| [#5426 v31_low different on vfredusum.vs](https://github.com/OpenXiangShan/XiangShan/issues/5426) | cesarus777 | 2025-12-24 | closed | fixed | 工具/参考模型 | [维护者 lewislzh 明确 NEMU bug、"RTL implementation is correct"。](https://github.com/OpenXiangShan/XiangShan/issues/5426#issuecomment-3692247360) |
| [#5449 VectorFloatFMA module operation alignment logic error](https://github.com/OpenXiangShan/XiangShan/issues/5449) | I3eg1nner | 2025-12-26 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5449) |
| [#5702 Vector memory access](https://github.com/OpenXiangShan/XiangShan/issues/5702) | biquanha | 2026-03-19 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5702) |
| [#5725 Behavior mismatch on RVV testcase (`vsetvl x0, x0, rs2` path)](https://github.com/OpenXiangShan/XiangShan/issues/5725) | KnightGOKU | 2026-03-25 | closed | fixed | 预期/行为对齐 | [维护者 huxuan0307 明确 "not a bug but a feature"；后来 NEMU 与 XiangShan 统一对 reserved 情形报非法。](https://github.com/OpenXiangShan/XiangShan/issues/5725#issuecomment-4132725504) |
| [#5739 `csrr vl` reads stale zero immediately after `vsetvli`](https://github.com/OpenXiangShan/XiangShan/issues/5739) | KnightGOKU | 2026-03-29 | closed | fixed | RTL | [GitHub `type: bug/fixed` 标签；无 tool 标签，按 XiangShan 已确认且已有修复标签记录。](https://github.com/OpenXiangShan/XiangShan/issues/5739) |
| [#5765 Difftest mismatch on tail bits of v0 after vlm.v](https://github.com/OpenXiangShan/XiangShan/issues/5765) | KnightGOKU | 2026-04-03 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5765) |
| [#5766 `vle8ff` fault-only-first followed by immediate `csrr vl` returns 0 on XiangShan, while Spike returns the expected `vl`](https://github.com/OpenXiangShan/XiangShan/issues/5766) | KnightGOKU | 2026-04-05 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5766) |
| [#5767 `vlseg2e8ff.v` with later-element fault triggers XiangShan internal critical error](https://github.com/OpenXiangShan/XiangShan/issues/5767) | KnightGOKU | 2026-04-05 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5767) |
| [#5768 Vector FP move/merge instructions missing `frm` reserved value check](https://github.com/OpenXiangShan/XiangShan/issues/5768) | Hoshi44 | 2026-04-05 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5768) |
| [#5769 Vector indexed segment store (vsuxseg*ei*) reports only base address in mtval on exception](https://github.com/OpenXiangShan/XiangShan/issues/5769) | zhangkanqi | 2026-04-06 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5769) |
| [#5770 Vector whole register load(vl2re32.v) partially updates destination on exception](https://github.com/OpenXiangShan/XiangShan/issues/5770) | zhangkanqi | 2026-04-06 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5770) |
| [#5772 vmv4r.v with misaligned registers dosen't raise illegal instruction exception](https://github.com/OpenXiangShan/XiangShan/issues/5772) | zhangkanqi | 2026-04-06 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5772) |
| [#5777 No instructions have been submitted for a long time. Could this be a case of deadlock?](https://github.com/OpenXiangShan/XiangShan/issues/5777) | zhangkanqi | 2026-04-07 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5777) |
| [#5790 Mismatch mcause and mtval when executing vssseg3e16.v](https://github.com/OpenXiangShan/XiangShan/issues/5790) | zhangkanqi | 2026-04-08 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5790) |
| [#5808 `vstart` mismatch after a minimal `vsse16.v` RVV testcase](https://github.com/OpenXiangShan/XiangShan/issues/5808) | KnightGOKU | 2026-04-14 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5808) |
| [#5809 `vmv.x.s` executes instead of raising illegal-instruction when `vsetvli` leaves `vtype.vill=1`](https://github.com/OpenXiangShan/XiangShan/issues/5809) | KnightGOKU | 2026-04-14 | closed | fixed | RTL | [GitHub `type: bug/fixed` 标签；无 tool 标签，按 XiangShan 已确认且已有修复标签记录。](https://github.com/OpenXiangShan/XiangShan/issues/5809) |
| [#5829 [Bug] vmv.x.s instruction fails to sign-extend when SEW < XLEN](https://github.com/OpenXiangShan/XiangShan/issues/5829) | jimmymtest | 2026-04-20 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5829) |
| [#5830 [BUG] `vfmv.f.s` fails to NaN-box 32-bit values when writing to a 64-bit floating-point registe](https://github.com/OpenXiangShan/XiangShan/issues/5830) | jimmymtest | 2026-04-20 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5830) |
| [#5831 [BUG] `vlse32.v` corrupts packed 32-bit element data under SEW=64, LMUL=8 mixed-EEW execution](https://github.com/OpenXiangShan/XiangShan/issues/5831) | jimmymtest | 2026-04-20 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5831) |
| [#5832 [BUG] `vl8re64.v` truncates upper 64-bit data in whole-register loads](https://github.com/OpenXiangShan/XiangShan/issues/5832) | jimmymtest | 2026-04-20 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5832) |
| [#5840 [BUG] `vzext.vf8` can compute the wrong zero-extended result for an active destination element.](https://github.com/OpenXiangShan/XiangShan/issues/5840) | jimmymtest | 2026-04-22 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5840) |
| [#5845 [Assertion Failure] XiangShan crashes in `LoadUnitS0` on a reduced `vmsbf.m -> vl1re64.v -> vlseg4e8.v` sequence](https://github.com/OpenXiangShan/XiangShan/issues/5845) | jimmymtest | 2026-04-22 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5845) |
| [#5865 XiangShan misses illegal-instruction trap for reserved masked `vmerge.vvm` with vd = v0](https://github.com/OpenXiangShan/XiangShan/issues/5865) | KnightGOKU | 2026-04-27 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5865) |
| [#5919 Reserved `vmv<nr>r.v` encodings are executed instead of being rejected](https://github.com/OpenXiangShan/XiangShan/issues/5919) | youzi27 | 2026-05-08 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5919) |
| [#5921 Incorrect `vstart` update after faulting vector indexed store](https://github.com/OpenXiangShan/XiangShan/issues/5921) | youzi27 | 2026-05-09 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5921) |
| [#5922 Incorrect handling of invalid `frm` for `vfmerge.vfm`](https://github.com/OpenXiangShan/XiangShan/issues/5922) | youzi27 | 2026-05-09 | closed | not_confirmed | 报告者重复/未独立确认 | [youzi27：This issue seems similar to #5768](https://github.com/OpenXiangShan/XiangShan/issues/5922#issuecomment-4411727439) |
| [#5927 Incorrect scalar result from `vmv.x.s` when SEW is smaller than XLEN](https://github.com/OpenXiangShan/XiangShan/issues/5927) | youzi27 | 2026-05-09 | closed | not_confirmed | 报告者重复/未独立确认 | [youzi27：This issue seems similar to #5829](https://github.com/OpenXiangShan/XiangShan/issues/5927#issuecomment-4412737115) |
| [#5928 Incorrect source element selection in `vsext`](https://github.com/OpenXiangShan/XiangShan/issues/5928) | youzi27 | 2026-05-09 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5928) |
| [#5929 `vloxseg5ei64.v` misses load access fault and commits destination vector registers](https://github.com/OpenXiangShan/XiangShan/issues/5929) | KnightGOKU | 2026-05-10 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/5929) |
| [#5930 `vle8ff.v` corrupts active loaded byte value](https://github.com/OpenXiangShan/XiangShan/issues/5930) | KnightGOKU | 2026-05-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5930) |
| [#5931 `vlseg2e32ff.v` loads wrong field0 data for misaligned fault-only-first segment load](https://github.com/OpenXiangShan/XiangShan/issues/5931) | KnightGOKU | 2026-05-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5931) |
| [#5932 `vluxseg5ei32.v` corrupts active destination data for indexed segment load](https://github.com/OpenXiangShan/XiangShan/issues/5932) | KnightGOKU | 2026-05-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5932) |
| [#5933 `vlsseg3e64.v` loads wrong active destination data for zero-stride segment load](https://github.com/OpenXiangShan/XiangShan/issues/5933) | KnightGOKU | 2026-05-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5933) |
| [#5934 `vlseg2e16.v` corrupts an active destination lane during masked segment load](https://github.com/OpenXiangShan/XiangShan/issues/5934) | KnightGOKU | 2026-05-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/5934) |
| [#5943 Incorrect `mtval` for faulting `vsse16.v` on kunminghu-v2](https://github.com/OpenXiangShan/XiangShan/issues/5943) | youzi27 | 2026-05-11 | open | confirmed | RTL | [confirmed 标签；维护者最终复现并明确 "I think this issue is a bug"。](https://github.com/OpenXiangShan/XiangShan/issues/5943#issuecomment-4437990329) |
| [#5958 Kunminghu-v2: LoadQueueReplay assertion on translated cross-page vector byte load/store](https://github.com/OpenXiangShan/XiangShan/issues/5958) | 0x1B05 | 2026-05-14 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/5958) |
| [#6015 Pipeline hangs on `vluxei32.v` when accessing unmapped physical addresses](https://github.com/OpenXiangShan/XiangShan/issues/6015) | lhb-sec | 2026-05-25 | open | confirmed | RTL | [维护者可复现并称 "indeed a bug"，后称已由 PR #6020 修复。](https://github.com/OpenXiangShan/XiangShan/issues/6015#issuecomment-4539489076) |
| [#6022 `vlse64.v` fails to trigger Load Access Fault upon illegal address access](https://github.com/OpenXiangShan/XiangShan/issues/6022) | lhb-sec | 2026-05-25 | closed | confirmed | RTL（重复根因） | [confirmed 标签；维护者称已由 PR #6020 修复的 vec-load hang，作为 #6015 同根因映射，不独计根因。](https://github.com/OpenXiangShan/XiangShan/issues/6022#issuecomment-4539692989) |
| [#6034 【BUG】 `vfsgnj.vv` incorrectly dirties `mstatus.FS`](https://github.com/OpenXiangShan/XiangShan/issues/6034) | nyh1 | 2026-05-28 | closed | not_confirmed | 预期/维护者否认 | [sinceforYy：We do not believe this is a bug；fflags功能正确](https://github.com/OpenXiangShan/XiangShan/issues/6034#issuecomment-4570036662) |
| [#6035 `vle32ff.v` fails to update exception CSRs upon Load Access Fault](https://github.com/OpenXiangShan/XiangShan/issues/6035) | lhb-sec | 2026-05-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6035) |
| [#6036 [Bug] vmv1r_vstart_ge_evl](https://github.com/OpenXiangShan/XiangShan/issues/6036) | nyh1 | 2026-05-28 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6036) |
| [#6037 [Bug] vmvnr_unaligned_regs](https://github.com/OpenXiangShan/XiangShan/issues/6037) | nyh1 | 2026-05-28 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6037) |
| [#6039 `vsetvl` with `rd=zero` causes core hang](https://github.com/OpenXiangShan/XiangShan/issues/6039) | lhb-sec | 2026-05-28 | open | reported | 未明 | [只有 reported；维护者回复尚未 review/fix，不能视作确认。](https://github.com/OpenXiangShan/XiangShan/issues/6039) |
| [#6042 `vle16.v` fault handling incorrectly sets `vstart` to `vl` instead of the faulting element index](https://github.com/OpenXiangShan/XiangShan/issues/6042) | lhb-sec | 2026-05-29 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6042) |
| [#6063 ```CVT16.scala``` fflags ```NV``` lost for ```vfrec7 -inf```](https://github.com/OpenXiangShan/XiangShan/issues/6063) | LeeHaofeng | 2026-06-07 | open | not_confirmed | 预期/格式问题 | [维护者说明fflags截断结果正确，仅代码格式问题，非功能bug](https://github.com/OpenXiangShan/XiangShan/issues/6063#issuecomment-4678966210) |
| [#6064 Copy-Paste Typo in Mux1H Default Condition — ```isvrgatherei16``` Repeated Instead of ```isvcompress``` in   VPermSrcTypeModule](https://github.com/OpenXiangShan/XiangShan/issues/6064) | LeeHaofeng | 2026-06-07 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6064) |
| [#6065 ```genVUopOffset``` uses wrong ```nf``` semantics](https://github.com/OpenXiangShan/XiangShan/issues/6065) | LeeHaofeng | 2026-06-07 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6065) |
| [#6066 VMask.scala ```shift``` truncation bug for ```SEW=8``` and large ```uopIdx```](https://github.com/OpenXiangShan/XiangShan/issues/6066) | LeeHaofeng | 2026-06-07 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6066) |
| [#6079 `vl1re16.v` incorrectly computes `vstart` on Load Access Fault](https://github.com/OpenXiangShan/XiangShan/issues/6079) | lhb-sec | 2026-06-10 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6079) |
| [#6085 `vsoxei32.v` fails to commit store](https://github.com/OpenXiangShan/XiangShan/issues/6085) | lhb-sec | 2026-06-11 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6085) |
| [#6093 ```VectorFloatAdder.scala``` overflow rounding uses wrong normal-path GRS bits](https://github.com/OpenXiangShan/XiangShan/issues/6093) | LeeHaofeng | 2026-06-13 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6093) |
| [#6151 [Performance] VSegmentUnit: segment instructions with vl=0 stall the memory unit hundreds of cycles instead of retiring immediately](https://github.com/OpenXiangShan/XiangShan/issues/6151) | maplejty814 | 2026-06-26 | open | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6151) |
| [#6152 [RVV] vzext.vf4 / vsext.vf4 writes zero to high 64-bit (elements 2..3)](https://github.com/OpenXiangShan/XiangShan/issues/6152) | Security-HC | 2026-06-26 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6152) |
| [#6168 [Bug] debug watchpoint trigger lost on FOF non-first element](https://github.com/OpenXiangShan/XiangShan/issues/6168) | maplejty814 | 2026-06-29 | open | confirmed | RTL/调试触发器 | [维护者确认known issue，计划后续修复](https://github.com/OpenXiangShan/XiangShan/issues/6168#issuecomment-4913753242) |
| [#6262 XS bug-report — vlseg to unmapped page deadlocks (VSegmentUnit)](https://github.com/OpenXiangShan/XiangShan/issues/6262) | wndmll643 | 2026-07-21 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6262) |
| [#6289 AMO deadlocks after `vse32.v` store access fault](https://github.com/OpenXiangShan/XiangShan/issues/6289) | lhb-sec | 2026-07-27 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6289) |
| [#6292 vstart set to wrong element on a page-faulting vector load (for debugging assistance)](https://github.com/OpenXiangShan/XiangShan/issues/6292) | wndmll643 | 2026-07-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6292) |
| [#6293 `vle64ff.v` misses Load Access Fault on misaligned access to I/O PMA region](https://github.com/OpenXiangShan/XiangShan/issues/6293) | lhb-sec | 2026-07-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6293) |
| [#6295 `vle32ff.v` corrupts destination vector register on Load Access Fault](https://github.com/OpenXiangShan/XiangShan/issues/6295) | lhb-sec | 2026-07-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6295) |
| [#6296 Vector store reports wrong `mcause` in M-mode](https://github.com/OpenXiangShan/XiangShan/issues/6296) | lhb-sec | 2026-07-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6296) |
| [#6298 XiangShan misses illegal-instruction trap for out-of-range vstart](https://github.com/OpenXiangShan/XiangShan/issues/6298) | lhb-sec | 2026-07-28 | open | not_confirmed | 未实现功能/维护者否认 | [维护者明确unimplemented feature, not a bug](https://github.com/OpenXiangShan/XiangShan/issues/6298#issuecomment-5542251829) |
| [#6302 XiangShan does not trap on vector instruction with reserved vsew encoding](https://github.com/OpenXiangShan/XiangShan/issues/6302) | lhb-sec | 2026-07-28 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6302) |
| [#6399 `mtval` mismatch on scalar store access fault after a vector store access fault](https://github.com/OpenXiangShan/XiangShan/issues/6399) | lhb-sec | 2026-08-21 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/6399) |
| [#6407 Vector load doesn't trigger illegal instruction trap when VSEW is invalid](https://github.com/OpenXiangShan/XiangShan/issues/6407) | kds1123001 | 2026-08-24 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6407) |
| [#6410 vmove-class instructions (vmv.v.*, vmerge.*) with misaligned register groups don't raise illegal instruction (test-matrix confirmed, extends #5772)](https://github.com/OpenXiangShan/XiangShan/issues/6410) | msuadOf | 2026-08-24 | closed | not_confirmed | 预期/无效/重复 | [标签为 invalid、已答复问题或 duplicate；关闭本身不构成确认。](https://github.com/OpenXiangShan/XiangShan/issues/6410) |
| [#6467 StoreQueue `deqPtr > rdataPtr` assertion fails at the physical-queue wrap boundary under vector stores](https://github.com/OpenXiangShan/XiangShan/issues/6467) | wndmll643 | 2026-09-02 | closed | confirmed | RTL | [weidingliu：indeed a bug of deqPtr update；We fixed it in #6474](https://github.com/OpenXiangShan/XiangShan/issues/6467#issuecomment-5522852062) |
| [#6475 Legal segmented store `vsseg3e32.v` triggers `robEntries uopNum is overflow!` (ROB uop-count underflow) — deterministic assertion abort on kunminghu-v3](https://github.com/OpenXiangShan/XiangShan/issues/6475) | wndmll643 | 2026-09-03 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6475) |
| [#6482 Stale mtval after consecutive same-direction RVV memory access faults](https://github.com/OpenXiangShan/XiangShan/issues/6482) | lhb-sec | 2026-09-04 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/6482) |
| [#6486 Legal segmented store `vsseg2e16.v` silently commits wrong store data (0 instead of the source value) — vector store-data unit emits 0 for a field on kunminghu-v3](https://github.com/OpenXiangShan/XiangShan/issues/6486) | wndmll643 | 2026-09-04 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6486) |
| [#6536 `vmadc.vi` zeroes mask-destination tail bits](https://github.com/OpenXiangShan/XiangShan/issues/6536) | lhb-sec | 2026-09-09 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6536) |
| [#6540 `stval` mismatch on a scalar store **page** fault after a vector store **page** fault (S-mode) — kunminghu-v2](https://github.com/OpenXiangShan/XiangShan/issues/6540) | wndmll643 | 2026-09-10 | open | confirmed | RTL | [GitHub `type: bug/confirmed` 标签；无 tool 标签，按 XiangShan 已确认 RTL/实现问题记录。](https://github.com/OpenXiangShan/XiangShan/issues/6540) |
| [#6543 `vdiv.vx` with a zero divisor deadlocks the core](https://github.com/OpenXiangShan/XiangShan/issues/6543) | lhb-sec | 2026-09-10 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6543) |
| [#6544 `vcpop.m` is incorrectly reported as an illegal instruction when `LMUL=8` and `vs2` is not group-aligned](https://github.com/OpenXiangShan/XiangShan/issues/6544) | lhb-sec | 2026-09-10 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6544) |
| [#6545 `vsrl.vv` with `v0.t` mask hangs and never writes back the destination register](https://github.com/OpenXiangShan/XiangShan/issues/6545) | lhb-sec | 2026-09-10 | open | reported | 未明 | [无 confirmed/fixed 标签且缓存评论没有明确维护者确认；WIP/reported/closed 均不作确认依据。](https://github.com/OpenXiangShan/XiangShan/issues/6545) |
| [#6555 `vssubu.vx` (vector fixed-point unsigned saturating subtract) does not set `vxsat` when it saturates — kunminghu-v3](https://github.com/OpenXiangShan/XiangShan/issues/6555) | wndmll643 | 2026-09-11 | closed | not_confirmed | 报告者撤回/实现定义 | [报告者：implementation-defined behavior, not a bug，关闭Issue](https://github.com/OpenXiangShan/XiangShan/issues/6555#issuecomment-5642683809) |
| [#6561 Incorrect `mstatus.VS` Dirty update for `vl=0` vector memory instructions](https://github.com/OpenXiangShan/XiangShan/issues/6561) | lhb-sec | 2026-09-11 | open | confirmed | RTL | [confirmed 标签；维护者说明已在 PR #6570 修复，报告者回测通过。](https://github.com/OpenXiangShan/XiangShan/issues/6561#issuecomment-5661448507) |
| [#6576 `mtval` is not written on a load access fault taken by a vector strided load (`vlse32.v`) — kunminghu-v3](https://github.com/OpenXiangShan/XiangShan/issues/6576) | wndmll643 | 2026-09-16 | open | partial | RTL/分支相关修复线索 | [维护者认为v2由PR6548修复，v3计划移植；分支相关线索单列，不视为当前v3已完整确认/修复](https://github.com/OpenXiangShan/XiangShan/issues/6576#issuecomment-5692218398) |

## 确认及部分确认条目的PoC索引

| Issue | 范围 | 类别 | 实际材料 |
|---|---|---|---|
| [#2890](https://github.com/OpenXiangShan/XiangShan/issues/2890) | 历史混合/部分确认 | 历史长程序/混合问题 | 原帖代码/静态片段，类别按实际证据单列 |
| [#4190](https://github.com/OpenXiangShan/XiangShan/issues/4190) | 性能/假依赖 | 性能/假依赖 | 原帖完整C/汇编benchmark可读；展示LMUL2循环节选 |
| [#5279](https://github.com/OpenXiangShan/XiangShan/issues/5279) | 工具/差分测试 | 工具/差分提交比较 | 正文日志/附件证据；本轮未提取可执行汇编，不以日志冒充源码 |
| [#5426](https://github.com/OpenXiangShan/XiangShan/issues/5426) | 工具/参考模型 | 工具/参考模型 | 正文日志/附件证据；本轮未提取可执行汇编，不以日志冒充源码 |
| [#5725](https://github.com/OpenXiangShan/XiangShan/issues/5725) | 预期/行为对齐 | 预期/行为对齐 | 正文日志/附件证据；本轮未提取可执行汇编，不以日志冒充源码 |
| [#5739](https://github.com/OpenXiangShan/XiangShan/issues/5739) | RTL | 配置 CSR | 已核对原帖目标触发代码节选 |
| [#5765](https://github.com/OpenXiangShan/XiangShan/issues/5765) | RTL | mask-tail | 已核对原帖目标触发代码节选 |
| [#5766](https://github.com/OpenXiangShan/XiangShan/issues/5766) | RTL | FOF | 已核对原帖目标触发代码节选 |
| [#5767](https://github.com/OpenXiangShan/XiangShan/issues/5767) | RTL | FOF | 已核对原帖目标触发代码节选 |
| [#5768](https://github.com/OpenXiangShan/XiangShan/issues/5768) | RTL | 非法编码/源码条件 | 只有RTL译码条件作为实现证据；未取得可执行PoC |
| [#5772](https://github.com/OpenXiangShan/XiangShan/issues/5772) | RTL | 非法编码 | 公开附件完整汇编源码已取得；PPT展示关键节选 |
| [#5809](https://github.com/OpenXiangShan/XiangShan/issues/5809) | RTL | 非法编码 | 已核对原帖目标触发代码节选 |
| [#5829](https://github.com/OpenXiangShan/XiangShan/issues/5829) | RTL | 数据/标量扩展 | 已核对原帖目标触发代码节选 |
| [#5830](https://github.com/OpenXiangShan/XiangShan/issues/5830) | RTL | 数据/标量扩展 | 公开正文/评论含代码或日志 |
| [#5831](https://github.com/OpenXiangShan/XiangShan/issues/5831) | RTL | 合法内存 | 公开正文/评论含代码或日志 |
| [#5832](https://github.com/OpenXiangShan/XiangShan/issues/5832) | RTL | 合法内存 | 公开正文/评论含代码或日志 |
| [#5840](https://github.com/OpenXiangShan/XiangShan/issues/5840) | RTL | 数据/标量扩展 | 公开正文/评论含代码或日志 |
| [#5865](https://github.com/OpenXiangShan/XiangShan/issues/5865) | RTL | 非法编码 | 公开正文/评论含代码或日志 |
| [#5928](https://github.com/OpenXiangShan/XiangShan/issues/5928) | RTL | 数据/标量扩展 | 公开正文/评论含代码或日志 |
| [#5930](https://github.com/OpenXiangShan/XiangShan/issues/5930) | RTL | FOF | 公开正文/评论含代码或日志 |
| [#5931](https://github.com/OpenXiangShan/XiangShan/issues/5931) | RTL | FOF | 公开正文/评论含代码或日志 |
| [#5932](https://github.com/OpenXiangShan/XiangShan/issues/5932) | RTL | 合法内存 | 公开正文/评论含代码或日志 |
| [#5933](https://github.com/OpenXiangShan/XiangShan/issues/5933) | RTL | 合法内存 | 已核对原帖目标触发代码节选 |
| [#5934](https://github.com/OpenXiangShan/XiangShan/issues/5934) | RTL | 合法内存 | 公开正文/评论含代码或日志 |
| [#5943](https://github.com/OpenXiangShan/XiangShan/issues/5943) | RTL | 异常链/故障地址 | 公开正文/评论含代码或日志 |
| [#6015](https://github.com/OpenXiangShan/XiangShan/issues/6015) | RTL | 访存活性 | 正文含HTML反汇编；附件为1个ELF，未附汇编源码 |
| [#6022](https://github.com/OpenXiangShan/XiangShan/issues/6022) | RTL（重复根因） | 访存活性 | 重复根因映射；以#6015真实反汇编代表，不把错误日志当代码 |
| [#6168](https://github.com/OpenXiangShan/XiangShan/issues/6168) | RTL/调试触发器 | 调试触发器/静态实现证据 | 静态RTL代码分析；原帖明确PoC仍在调试，尚未提供可执行PoC |
| [#6399](https://github.com/OpenXiangShan/XiangShan/issues/6399) | RTL | 异常链/故障地址 | 已核对原帖目标触发代码节选 |
| [#6467](https://github.com/OpenXiangShan/XiangShan/issues/6467) | RTL | 流水队列/压力序列 | 公开附件含ELF、源代码/反汇编及波形；正文给出故障指令与前置压力条件 |
| [#6482](https://github.com/OpenXiangShan/XiangShan/issues/6482) | RTL | 异常链/故障地址 | 正文含目标指令列表；附件静态核实为98个ELF，未附汇编源码 |
| [#6540](https://github.com/OpenXiangShan/XiangShan/issues/6540) | RTL | 异常链/故障地址 | 公开正文/评论含代码或日志 |
| [#6561](https://github.com/OpenXiangShan/XiangShan/issues/6561) | RTL | 配置 CSR | 已核对原帖目标触发代码节选 |
| [#6576](https://github.com/OpenXiangShan/XiangShan/issues/6576) | RTL/分支相关修复线索 | 访存异常/分支相关修复线索 | 原帖代码/静态片段，类别按实际证据单列 |

## 按真实触发代码分组与Mutation建议

代码均为原始材料的保真节选；不宣称包含独立运行所需全部初始化。RTL条件、日志、二进制和汇编源码分别标明。Mutation为本报告建议，不冒充原issue结论。

### 工具/差分提交比较（#5279）

暂无单列可执行代码示例，见逐项索引实际材料类型。仅实现条件、日志、附件或重复映射；不把它们冒充可执行PoC

Mutation建议：保留原始 commit trace/附件，比较器按 RVV store 的 byte-enable 与提交粒度建立规范，不把差分器问题归 RTL。


### 工具/参考模型（#5426）

暂无单列可执行代码示例，见逐项索引实际材料类型。仅实现条件、日志、附件或重复映射；不把它们冒充可执行PoC

Mutation建议：对 rounding mode（尤其 RDN）做 reference A/B 与 RTL 独立执行对照，升级参考模型后回归。


### 预期/行为对齐（#5725）

暂无单列可执行代码示例，见逐项索引实际材料类型。仅实现条件、日志、附件或重复映射；不把它们冒充可执行PoC

Mutation建议：根据触发指令、初值、期望与观察点做受约束变异。


### 配置 CSR（#5739、#6561）

**PoC：配置后立即读取 vl**

https://github.com/OpenXiangShan/XiangShan/issues/5739

```asm
li t6, 0x600
csrs mstatus, t6
li a0, 16
vsetvli t1, a0, e8, m1, ta, ma
csrr t2, vl
```

预期 t1=t2=16，原始故障为 t2=0。
维护者定位 VL bypass 错误并给出修复 PR #5743。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5739。展示原始代码节选，不是独立可运行的完整测试。
**PoC：vl=0 时的 VS 状态副作用**

https://github.com/OpenXiangShan/XiangShan/issues/6561

```asm
main:
  csrwi vcsr, 4
  csrwi vstart, 0
  vsetivli zero, 0, e64, m1, tu, ma

  fmv.x.d s7, fa0
  csrrw t2, sstatus, s7
  vsseg4e32.v v13, (t6), v0.t
```

初值 fa0=0xffffffffbf361d42，使 VS=Clean。
本例 vstart=0、vl=0，观察 VS 是否错误变 Dirty，不能忽略 vstart 条件。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/6561。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：生成 `vsetvli/vsetivli -> csrr vl` 与 `VS=Clean + vl=0 memory-op` 两指令序列，检查 CSR 可见性与 Dirty 位。


### mask-tail（#5765）

**PoC：mask load 后完整读回**

https://github.com/OpenXiangShan/XiangShan/issues/5765

```asm
li a0, 16
vsetvli t0, a0, e8, m1, tu, mu
vmv.v.i v0, 0

li a0, 10
vsetvli t0, a0, e8, m1, tu, mu
la a1, mask_data
vlm.v v0, (a1)
la a2, out_data
vsm.v v0, (a2)
```

mask_data 与 expected_data 均为 .byte 0x80, 0x03。
原程序逐字节比较读回数据，省略初始化、比较循环和 trap handler。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5765。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：交叉 vl、tu/ta、mu/ma，先写 v0 全寄存器哨兵，再 vlm/vsm 比较全部尾位。


### FOF（#5766、#5767、#5930、#5931）

**PoC：FOF 后立即读取缩短的 vl**

https://github.com/OpenXiangShan/XiangShan/issues/5766

```asm
li a0, 8
vsetvli t3, a0, e8, m1, tu, mu
vmv.v.i v8, 0

la a1, deny_start
addi a1, a1, -7

vle8ff.v v8, (a1)
csrr t4, vl
la t0, observed_vl
sw t4, 0(t0)
```

原程序用 PMP 将 deny_start 至 deny_end 设为不可访问。
前 7 字节可访问，第 8 字节 fault：期望读取 vl=7，原报告得到 0。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5766。展示原始代码节选，不是独立可运行的完整测试。
**PoC：FOF segment 的后元素 fault**

https://github.com/OpenXiangShan/XiangShan/issues/5767

```asm
li a0, 8
vsetvli t3, a0, e8, m1, tu, mu
vmv.v.i v16, 0
vmv.v.i v17, 0

la a2, deny_start
addi a2, a2, -12

vlseg2e8ff.v v16, (a2)
csrr t4, vl
```

同样使用 PMP deny 区，nf=2，每元素占 2 字节，故障落在后续元素。
原报告触发内部 critical error，期望按 FOF 语义处理。省略 PMP 初始化和 handler。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5767。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：以 PMP/PMA 边界控制首元素与后续元素 fault，检查 vl、vstart、目的寄存器及不发生内部 assertion。


### 非法编码/源码条件（#5768）

暂无单列可执行代码示例，见逐项索引实际材料类型。仅实现条件、日志、附件或重复映射；不把它们冒充可执行PoC

Mutation建议：根据触发指令、初值、期望与观察点做受约束变异。


### 非法编码（#5772、#5809、#5865）

**PoC：非法 vtype 后执行向量指令**

https://github.com/OpenXiangShan/XiangShan/issues/5809

```asm
vsetvli x21, x21, 992
csrr x23, vl
csrr x22, vtype
vmv.x.s x21, v16
```

原日志：vl=0，vtype=0x8000000000000000（vill=1）。
预期 mcause=2、mtval=0x43002ad7。原故障却提交了 x21 写回。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5809。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：按编码字段构造 vill、reserved frm、vd=v0 mask、寄存器组未对齐；trap handler 检查 mcause=2。


### 数据/标量扩展（#5829、#5830、#5840、#5928）

**PoC：窄整数移到标量后的符号扩展**

https://github.com/OpenXiangShan/XiangShan/issues/5829

```asm
vsetivli x0, 2, e64, m1, ta, ma
vmv.v.i  v9, 0

vsetivli x0, 1, e32, m1, tu, mu
la       x10, data_word
vle32.v  v9, (x10)
vmv.x.s  x15, v9

li       x16, 0xffffffffe01d7b92
li       gp, 1
beq      x15, x16, exit
li       gp, 2
```

data_word 的值为 0xe01d7b92，预期 x15 为其 XLEN 符号扩展。
省略 VS/FS 初始化、trap handler、退出和数据段，其余扩展类按完整目标结果比较。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5829。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：枚举 SEW=8/16/32 与符号位、NaN-box、高半 lane 哨兵；在目标指令后读回标量/浮点/向量结果。


### 合法内存（#5831、#5832、#5932、#5933、#5934）

**PoC：零 stride 的 segment load**

https://github.com/OpenXiangShan/XiangShan/issues/5933

```asm
li      x9, 0x8fffffb8
li      x10, 0x3803444b2551a2ae
sd      x10, 16(x9)
li      x10, 0x1000
sd      x10, 24(x9)

# ... original intervening instructions omitted ...

li      x8, 0x8fffffcd
vlsseg3e64.v v18, (x8), x19
```

原始触发状态：SEW=64、LMUL=1、x19=0，base 未对齐。
节选保留关键内存写入与目标指令，其余前置代码见原帖，逐 field 比较 active 数据。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/5933。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：变异 EEW/SEW/LMUL、stride=0、indexed、segment nf、mask 与每 lane 唯一哨兵，核对 active lane/存储数据。


### 异常链/故障地址（#5943、#6399、#6482、#6540）

**PoC：向量异常后的标量异常**

https://github.com/OpenXiangShan/XiangShan/issues/6399

```asm
vsetivli x0, 4, e32, m1, ta, ma
vsse32.v v11, (t4), s1
li a5, 0x0000020000000000
li t2, 0x917af882bf50788e
srl t6, t2, a5
sb sp, -1918(t6)
```

向量 store 与后续标量 store 依次触发 access fault。
原程序通过 handler 恢复执行，检查第二次 mtval 为本次地址，不能残留第一次地址。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/6399。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：生成 vector fault -> mret 跳过 -> 同方向 vector/scalar fault；分别断言 mtval/stval 为第二个有效地址。


### 访存活性（#6015、#6022）

**PoC：未映射地址上的 indexed load 挂死**

https://github.com/OpenXiangShan/XiangShan/issues/6015

```asm
80001234:  fcvt.d.l    fa7, a7
80001238:  sha256sum0  s7, a7
8000123c:  aes64ds     sp, s6, s7
80001240:  vluxei32.v  v25, (a1), v17
80001244:  aes64ks2    s4, s4, a4
```

a1=0x4ff0b1eb，VL=4，SEW=32，LMUL=1，各索引地址落入未映射区域。
观察异常与提交进度，原报告有 15000 周期无提交。附件提供 ELF，不是汇编源码。
完整性：原帖：github.com/OpenXiangShan/XiangShan/issues/6015。展示原始代码节选，不是独立可运行的完整测试。

Mutation建议：对未映射/PMP deny 的 indexed/strided 地址施压；以 commit progress 和周期上限作 oracle。


### 流水队列/压力序列（#6467）

https://github.com/OpenXiangShan/XiangShan/issues/6467

```asm
vse16.v v10, (t1)
```

完整性：正文原始故障指令节选；t1=0x80060050，完整压力前序见附件，不是独立可运行PoC

Mutation建议：按维护者建议以跨cache line大量store造成Sbuffer L1 miss eviction，再执行inactive向量store；变异队列wrap、mask和提交时序，观察deqPtr/rdataPtr不变量与store实际字节地址。


### 调试触发器/静态实现证据（#6168）

暂无单列可执行代码示例，见逐项索引实际材料类型。不以日志或静态RTL条件冒充独立汇编程序

Mutation建议：FOF后元素fault与watchpoint trigger组合，观察trigger命中、vl/vstart和异常优先级；需要独立debug oracle。


### 性能/假依赖（#4190）

https://github.com/OpenXiangShan/XiangShan/issues/4190

```asm
vsetvli t0, x0, e32, m2, ta, ma
        li a0, LOOP
        csrr a1, cycle
1:
.rept UNROLL
vadd.vv v8,v16,v24
vadd.vv v10,v18,v26
vadd.vv v12,v20,v28
vadd.vv v14,v22,v30
.endr
        addi a0, a0, -1
        bnez a0, 1b
        fence.i
        csrr a0, cycle
        sub a0, a0, a1
```

完整性：UNROLL=8、LOOP=64，节选原始LMUL2测时循环，不含main/构建文件

Mutation建议：保持相同工作量，改变LMUL和无用vd依赖链；测cycle/吞吐，不与功能差分失败混计。


### 历史长程序/混合问题（#2890）

暂无单列可执行代码示例，见逐项索引实际材料类型。不以日志或静态RTL条件冒充独立汇编程序

Mutation建议：复现时固定分支、配置、nexus-am版本、VS状态与DRAMsim3；拆分长程序失效点后建立单根因回归。


### 访存异常/分支相关修复线索（#6576）

暂无单列可执行代码示例，见逐项索引实际材料类型。不以日志或静态RTL条件冒充独立汇编程序

Mutation建议：分别在v2/v3运行同一strided-load fault条件，检查mtval；记录修复PR与实际分支版本。


## 附件与复核限制

- #5772附件完整`vmv4r_illInstr.S`已读取，保存在JSON。
- #6015附件为1个ELF，正文HTML有反汇编；未执行。
- #6482附件为98个ELF与3目录，正文计数正确，未附可读源码。
- #5768只有RTL译码条件；#6168原帖明确PoC仍在调试。二者不能伪装可执行PoC。
- 代码来源是正文/评论/公开附件；未运行复现，不把维护者修复声明自动当作当前分支已合并。
- 原始快照与全量GitHub缓存位于 `/tmp/vext-ppt-research-20260917`。


## 维护者/报告者原文证据摘录

表内核验依据为中文概述；以下引用为对应评论原文。标签快照不代表最终结论，最终判定优先考虑后续明确评论。

### #2890

概述：维护者给出RTL修复PR3140/commit1a0c5d且报告者验证；同帖后续还有nexus-am与VS配置问题，不整帖算单一RTL缺陷

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/2890#issuecomment-2220740793)

> We have fixed the issue at this commit(1a0c5d77fed8b13a9fa5f70d1f25d808a311dd7b) in this pull requests (https://github.com/OpenXiangShan/XiangShan/pull/3140). This will later be integrated into the master.
### #3012

概述：作者cyyself：Fixed NEMU commit b9796f4ec8b8427b4fb995ec948ed345f1caeaf4

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/3012#issuecomment-2134233149)

> Fixed [https://github.com/OpenXiangShan/NEMU/commit/b9796f4ec8b8427b4fb995ec948ed345f1caeaf4](https://github.com/OpenXiangShan/NEMU/commit/b9796f4ec8b8427b4fb995ec948ed345f1caeaf4) .
### #4190

概述：维护者确认不必要vd依赖性能问题，PR4198修复且报告者回测；LMUL1解码限制另属设计取舍

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/4190#issuecomment-2597589506)

> The above issue has been fixed by https://github.com/OpenXiangShan/XiangShan/pull/4198
### #5279

概述：维护者 Yan-Muzi 明确："known bug of difftest"，非 RTL。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5279#issuecomment-3595092909)

> It is a known bug of difftest. We have not really figured out how to compare store commits of vector stores. We may fix this in the future.
### #5424

概述：Yan-Muzi：Please refer to #5279

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5424#issuecomment-3689978534)

> Please refer to #5279.
### #5426

概述：维护者 lewislzh 明确 NEMU bug、"RTL implementation is correct"。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5426#issuecomment-3692247360)

> Thanks for the issue report. This is indeed a bug in the NEMU simulator (the RTL implementation is correct)：
> The RISC-V Vector specification states that for the vfredusum instruction, when an operand is masked off, it may be treated as -0 if the rounding mode is not RDN; for RDN, the operand needs to be treated as +0. NEMU’s handling of the RDN case was incorrect. A fix has been submitted.
### #5725

概述：维护者 huxuan0307 明确 "not a bug but a feature"；后来 NEMU 与 XiangShan 统一对 reserved 情形报非法。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5725#issuecomment-4132725504)

> Thank you for your bug report. As described in the vector section of the specification, the vsetvl[i] instruction is reserved when rs1 = x0 and rd = x0. Since there is no explicit description of how to implement reserved, the hardware can implement it in any reasonable way. In other words, this is not a bug but a "feature".
### #5922

概述：youzi27：This issue seems similar to #5768

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5922#issuecomment-4411727439)

> This issue seems similar to #5768 , so I will close it. Sorry for the confusion.
### #5927

概述：youzi27：This issue seems similar to #5829

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5927#issuecomment-4412737115)

> This issue seems similar to #5829  , so I will close it. Sorry for the confusion.
### #5943

概述：confirmed 标签；维护者最终复现并明确 "I think this issue is a bug"。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/5943#issuecomment-4437990329)

> @youzi27 Ah ha,  I finally reproduce this issue, I think this issue is a bug, which was introduced by (https://github.com/OpenXiangShan/XiangShan/commit/2bec9bddf90fa1ddd2690f344ef3f34e4346bb9e#diff-6db620258edc695befb5c4de9a76e239e89ff74d881e35a4ab978f931efb21aeR119) .
### #6015

概述：维护者可复现并称 "indeed a bug"，后称已由 PR #6020 修复。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6015#issuecomment-4539489076)

> Thank you for your report! That's indeed a bug caused by `d38fc34`, we will fix it later!
### #6022

概述：confirmed 标签；维护者称已由 PR #6020 修复的 vec-load hang，作为 #6015 同根因映射，不独计根因。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6022#issuecomment-4539692989)

> This is a known issue caused by a vec load hang; we have already fixed it.https://github.com/OpenXiangShan/XiangShan/pull/6020
### #6034

概述：sinceforYy：We do not believe this is a bug；fflags功能正确

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6034#issuecomment-4570036662)

> We do not believe this is a bug.
### #6063

概述：维护者说明fflags截断结果正确，仅代码格式问题，非功能bug

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6063#issuecomment-4678966210)

> Here `fflags0` is `5` bits, and the result after `Cat` is truncated to exactly `0`, so although it looks wrong, the result is correct.
> We will fix the formatting issue in the `kunminghu-v3` branch later.
### #6168

概述：维护者确认known issue，计划后续修复

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6168#issuecomment-4913753242)

> This is a known issue. We are evaluating the specific matters for subsequent fixes. Thank you for your point.
### #6298

概述：维护者明确unimplemented feature, not a bug

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6298#issuecomment-5542251829)

> I must claim that this issue just report a unimplemented feature, not a bug.
### #6467

概述：weidingliu：indeed a bug of deqPtr update；We fixed it in #6474

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6467#issuecomment-5522852062)

> 1. That's indeed a bug of `deqPtr` update, and it's the first time to be observed.
> 2. The asymmetric `dataQueue.io.empty` gate between the `deqPtr` (:1272) and `rdataPtr` (:1302) inactive skips is intentional. We fixed it in #6474
### #6555

概述：报告者：implementation-defined behavior, not a bug，关闭Issue

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6555#issuecomment-5642683809)

> Thanks for your reply. While re-analyzing some other bug, I found out that this is an implementation-defined behavior, not a bug. Closing the issue.
### #6561

概述：confirmed 标签；维护者说明已在 PR #6570 修复，报告者回测通过。

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6561#issuecomment-5661448507)

> If the value of the `vstart` register is 0, a `vector store` instruction will not alter the vector state and therefore will not generate a `DirtyVS`; if the value of the `vstart` register is not 0, all successfully executed vector instructions will reset `vstart` to `0` upon completion, thereby altering the vector state and generating a `DirtyVS`.
> I have fixed this in this PR. [https://github.com/OpenXiangShan/XiangShan/pull/6570](https://github.com/OpenXiangShan/XiangShan/pull/6570)
> I successfully ran the test cases locally.
### #6576

概述：维护者认为v2由PR6548修复，v3计划移植；分支相关线索单列，不视为当前v3已完整确认/修复

[原评论](https://github.com/OpenXiangShan/XiangShan/issues/6576#issuecomment-5692218398)

> I think this issue has been fixed in `kunminghu-v2`. See PR https://github.com/OpenXiangShan/XiangShan/pull/6548.
> Vector support for `kunminghu-v3` is still under development, and we'll apply the corresponding fixes to v3 in the future.
