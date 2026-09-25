# trap 条目候选 bug 的 GitHub 原创性核查(逐条 case)

日期:2026-09-18。核查对象 = `trap-entries-结果.md` 中的候选 bug,按"指令形态 × 触发条件"逐条 case 到 OpenXiangShan/XiangShan(及 NEMU)issue 检索,判定原创性。口径:**已有 issue 明确报告该行为的算"已发现",我们的 PoC 只算补充 case;无命中才算原创**。GitHub 状态以 2026-09-18 `gh` 实查为准。

## 最终结论(经空载复证修正后)

| # | 候选 bug | 规模(复证后) | 原创性 | 一句话 |
|---|---|---:|---|---|
| 1 | **vstart 超界 + 译码检查未覆盖族 → 核停止提交(纯 RTL 挂死)** | **62 条 / 34 个指令形态**(vwsll/vandn/vid.v/vrol/vror/vslide1/narrowing 族等) | **原创**(逐条 0 命中,0/77 形态有专属报告) | 唯一全新的 RTL 活性 bug;#6298 只覆盖"执行不 trap",未覆盖"挂死" |
| 2 | masked vnclipu.wv SEW=16 饱和不置 vxsat | 2 条 + RTL 根因定位(VIAluMisc sat 位未按字节复制 × VIAluFix 字节粒度 AND) | **#6555 补充**(其正文点名 vnclip* 家族;但我们的根因+奇元素构造是增量) | 给 #6555 追加 PoC + 根因 |
| 3 | LMUL 组未对齐编码漏检(NEMU illegal / RTL 执行) | 201 条 / 8 族 | **#6410/#5772/#5919 补充**(vmerge.vim/.vxm 变体、vmv8r.v 为未实测的增量) | 已知家族的规模化 PoC |
| 4 | vsm.v 对 MMIO/未映射地址 store 不 fault(双侧一致) | 3 条 | **原创观察(环境/PMA 类)** | 与 #6482/#1078/#5279 均不同 |
| 5 | vstart=VLMAX(LMUL=8)边界不 trap(双侧一致) | 34 条 | **#6298 边界补充** | 与 #6298 同一 Sail 检查缺失 |
| — | ~~difftest 工具挂死~~ | ~~294 条~~ | **撤销(满载假超时)** | 空载 --diff 全部 GOODTRAP |

注:全量以 -j48 满载、timeout 30s 运行,461 条 timeout 中 **399 条为满载假超时**(空载复测 GOODTRAP,含原 A 类全部 294 条与 B 类 105 条);仅 62 条空载 --no-diff/--diff 双重复证仍挂。教训:**timeout 类判定必须空载复证后方可定案**。

## 汇总判定(过程记录,部分已被上表修正)

| 候选 bug | case 数 | 判定 | 依据 |
|---|---:|---|---|
| B. vstart>VLMAX 时核完全停止提交(纯 RTL 也挂死;**空载重测后修正为 62 条真挂/105 条满载假超时**) | 真挂 62 条(其余 105 条空载正常 trap) | **原创(活性层面,逐条 0/77 形态有专属报告;真挂族 = 译码检查未覆盖的 vshf/vppu/vfix 等)** | 双通道检索(gh search 全文 + 全库 6518 项本地匹配):无 "vstart 导致挂死" 报告;#6298 只覆盖"不 trap 且正常提交",维护者称 unimplemented;#6545 的挂死由 masked vsrl.vv v0.t 触发,通篇未提 vstart,不同根因;#6036(vmv1r vstart≥evl)DUT 继续前进无挂死;其余 deadlock 类(#6543/#6289/#6262/#6015/#6303/#6209)触发条件均不涉 vstart;历史 PR #2248 曾加 vstart illegal 检查、PR #3249 截断 vstart 写入 |
| E2. vstart=VLMAX(LMUL=8)边界:Sail 报 illegal、RTL+NEMU 执行(双侧一致) | ~20 个指令形态 / 34 条 PoC | **#6298 范畴边界补充,不算独立原创**(已修正,见下方"规范与 Sail 语义依据") | 规范仅要求 8 族在 vstart≠0 时 illegal(归约/vcpop/vfirst/vmsbf/vmsif/vmsof/viota/vcompress),slide/gather/vid **不在清单**;E2 各条 Sail 报 illegal 的真实原因是 `get_start_element()` 的超界检查(vstart > 8·VLEN/SEW−1),其触发条件 vstart=VLMAX 且 LMUL=8 恰好触上界——与 #6298 同一主题(vstart out-of-range 不 trap)的边界情形;XiangShan/NEMU 仓库无逐指令专属报告,但按口径归为 #6298 补充 |
| C. LMUL 寄存器组未对齐编码漏检(NEMU illegal、RTL 执行) | 8 个指令族 / 201 条 PoC | **已发现,补充 case** | 见下方逐族表 |
| D. masked vnclipu.wv 饱和不置 vxsat | 1 个形态 / 2 条 PoC | **部分已发现** | #6555(open,维护者 2026-09-11 评论"vector WIP 暂不处理")正文"Systematic"节点名 `vnclip*`:"A fix should cover … (vssubu/vsaddu/vssub/vsadd/vnclip*/vsmul, …), whose saturation must set vxsat";其实测 PoC 是无 mask 的 vssubu.vx,我们的 `vnclipu.wv + v0.t` 是该家族首个独立复现 → 建议 #6555 追加 PoC,不新开 |
| ~~A. 双侧一致的向量 illegal trap 后 difftest 同步挂死~~ | ~~294 条~~ | **判定撤销:满载假超时** | 空载 --diff 重测 294 条**全部 GOODTRAP**——满载(-j48)下 30s 完不成初始化+执行造成假 timeout,并非 difftest 工具 bug;此前的"原创工具 bug"结论作废 |

注:本地快照(2026-09-16)记录 #6555 为 closed/报告者撤回;今日实查为 **open** 且有维护者 WIP 评论,以实查为准。

## 规范与 Sail 语义依据(2026-09-18 核查,规范取冻结 RVV 1.0 riscv/riscv-v-spec)

- **vstart≠0 时规范强制 illegal 的仅 8 族**:归约(§11 "Vector reduction operations raise an illegal instruction exception if vstart is non-zero")、vcpop.m(L4196)、vfirst.m(L4218)、vmsbf.m(L4259)、vmsif.m(L4295)、vmsof.m(L4332)、viota.m(L4383)、vcompress.vm(L4797)。**vid.v、vslide/vslide1、vrgather 不在清单**——slide 族 vstart≥vl 是 "performs no operation"(L4533)。
- **超界 vstart** 规范表述(§6 L560):大于当前 vtype 最大元素索引的 vstart 值为 **reserved**,NOTE "recommended that implementations trap … not required"。
- **Sail 报 illegal 的确切机制**:
  1. 上述 8 族挂 `not(assert_vstart(0)) → Illegal`(vext_mask_insts.sail:98/137/178/223/268/318、vext_utils_insts.sail:191/196、vext_fp_utils_utils.sail:46/51);vcompress 用 `start_element != 0`(vext_arith_insts.sail:2158)
  2. 超界检查在 `get_start_element()`(vext_utils_insts.sail:274-284):`if start_element > 2^(3+vlen_exp−SEW_pow)−1 then Err(())`,即 **vstart > 8·VLEN/SEW−1(只依赖 SEW,不看当前 LMUL/vl)** → 共享路径 `return Illegal_Instruction()`;源码注释即引规范 reserved 并留 TODO "bound might be incorrect"(PR#755)
  3. CSR 写 vstart 不 trap 且截断 vlen_exp 位(vext_regs.sail:407-413);Isla 在 pre-state 直接符号化 vstart 绕过截断,因此超界值能进入执行并触发上述 Err
- **对 E2 的推论**:E2 各条(vstart=VLMAX、LMUL=8)恰好 vstart=8·VLEN/SEW > 上界−1 触发 Sail 检查;LMUL<8 时 vstart=VLMAX 不触发。故 E2 是 #6298(vstart out-of-range 不 trap)的边界情形,非独立 bug。
- **对 B 的补充**:viota.m 等规范 8 族在 B 类条目中(vstart 超界必 ≠0)有双重违法性(超界 reserved + vstart≠0 强制 illegal),但 B 的核心是挂死活性问题,原创性判定不受影响。

## C 类逐族判定(8 个指令族)

| 指令族 | PoC 数 | 判定 | 覆盖证据 |
|---|---:|---|---|
| vmerge.vvm | 58 | 已覆盖 | #6410 测试矩阵明确列出 vmerge.vvm @ e16m2/m4/e64m2(vd misaligned → executes, no trap) |
| vmerge.vim | 46 | 类级覆盖,变体未实测 | #6410 正文声明 "every FuType.vmove instruction (… vmerge.*) bypasses the check",通配涵盖;矩阵只实测了 vvm,无 vim 条目 → 补充 case |
| vmerge.vxm | 46 | 类级覆盖,变体未实测 | 同上 |
| vmv.v.v | 24 | 已覆盖 | #6410 矩阵点名 vmv.v.v @ e32m2(vd=v3) |
| vmv.v.x | 12 | 已覆盖 | #6410 矩阵点名 vmv.v.x @ e32m2 |
| vmv.v.i | 12 | 已覆盖 | #6410 矩阵点名 vmv.v.i @ e32m2 |
| vmv8r.v | 2 | 泛称覆盖 | #5919 标题 "Reserved vmv\<nr\>r.v encodings" nr 含 8,但正文笼统无逐条证据;#6037(closed COMPLETED)实测的是 vmv2r.v → 基本算补充 case |
| vmv4r.v | 1 | 已覆盖 | #5772 实测 vmv4r.v v12, v22(bug/confirmed,仍 open) |

**#6410 关闭理由**:维护者 huxuan0307 "Not a bug at kunminghu-v2/v3"(成员 Squareless-XD 称 illegal-instruction 相关修复已在开发版完成将合入 v3),按 invalid 关闭——**不是"设计如此"**。

## B 类逐指令形态核查(77 形态)

检索方法:每形态 `gh search issues --repo OpenXiangShan/XiangShan "<mnemonic>"` + 全量 `vstart`/`hang`/`stop committing` 关键词交叉核验。**后 39 形态已完成(0/39 有专属报告);前 38 形态核查中**。

### 后 39 形态结论(全部"无专属报告")

| 指令 | 结论 | 备注(命中的无关 issue) |
|---|---|---|
| vwaddu.vx / vwmul.vx / vnmsac.vv / vmul.vv / vremu.vv / vaadd.vv / vmadd.vx / vasub.vx / vaaddu.vx / vmulhsu.vx / vslide1down.vx / vnsrl.wi / vnsrl.wx / vctz.v / vmsne.vi / vadc.vim / vmseq.vv / vmsle.vv / vrgatherei16.vv / vmseq.vx / vmsne.vx / vmsleu.vx / vsbc.vxm / vwmulsu.vv / vwmulsu.vx / vabdu.vv / vabd.vv | 无专属报告 | 零命中 |
| vnclipu.wi / vnclip.wi / vnclip.wv | 无专属报告 | 仅 #6555 vxsat(白名单) |
| vclmulh.vx | 无专属报告 | #5769/#5780 无关 |
| vfmv.s.f | 无专属报告 | #5768(frm)、#5830(vfmv.f.s 数据)、#6410(白名单) |
| vslidedown.vi | 无专属报告 | #3488 性能 |
| vrgather.vi | 无专属报告 | #3200/#3488 性能 |
| vrgather.vv | 无专属报告 | 最接近 #2890(2021 早期 RVV 基准挂死,程序含 vrgather.vv 但**无 csrw vstart**,已关闭的基础功能问题) |
| vmsbc.vx | 无专属报告 | #5831(vlse32 数据)模糊无关 |
| vwadd.wv / vwsub.wv | 无专属报告 | #5932/#5931 数据错 |
| vwmul.vv / vwmul.vx | 无专属报告 | 仅 #5921(fault 后 vstart 数值错) |

**全量交叉核验**(30 条 vstart 命中 + 全部 hang 类):vstart 类 issue 全是"fault 后 vstart 数值错误"(#6292/#6079/#6042/#5921/#5808)或 #6298(不 trap);挂死类(#6262/#6289/#6543(vdiv 除零)/#6209/#3773/#5777/#2890/#6545)触发条件均与 vstart 超界无关。**0/39 有专属报告。**

### 前 38 形态结论(全部"无专属报告",双通道检索:gh search 全文 + 全库 6518 项本地匹配 + 标题/正文兜底扫描)

| 指令 | 结论 | 备注(命中的无关 issue) |
|---|---|---|
| vwsll.vx / vslidedown.vx / vrol.vx / vror.vx / vslide1up.vx / vwmulu.vv / vandn.vx / vror.vi / vnmsac.vx / vnsra.wx / vror.vv / vwmacc.vv / vwmaccsu.vx / vwmulu.vx / vnmsub.vx / vnsra.wv / vnsrl.wv / vnclip.wx / vnclipu.wx / vbrev8.v / vslideup.vi / vrev8.v / vmsltu.vv / vwsll.vv / vmsgtu.vx / vmsbc.vxm / vwmaccsu.vv / vwsubu.wv / vwsubu.vx | 无专属报告 | 全库零命中 |
| vclmulh.vv | 无专属报告 | #5769 正文附带提及(主题 vsuxseg mtval) |
| viota.m | 无专属报告 | 仅 #2890(rvv-bench 长程序挂死,汇编含 viota.m 但无 vstart 写入) |
| vslideup.vx | 无专属报告 | #5931 随机指令附带提及 |
| vid.v | 无专属报告 | #4190 性能 |
| vwsll.vi | 无专属报告 | #5773 commit log 提及(主题 flh 异常) |
| vmsgt.vx | 无专属报告 | 零命中(代表 case-6545 与 issue #6545 纯编号巧合) |
| vmadc.vim | 无专属报告 | #6536 是 vmadc.vi tail 位数据 bug(非挂死、无 vstart) |
| vrgather.vx | 无专属报告 | #6064 是 isvrgatherei16/isvcompress Mux1H 拼写笔误(静态源码问题) |
| vwsub.vv | 无专属报告 | #5931 附带提及 |

**兜底佐证**:全库 hang/deadlock 标题的向量类 issue 仅 #6545(vsrl masked)/#6543(vdiv 除零)/#6015/#6262/#6039/#6289/#2890/#5777,无一为"csrw vstart 超界后执行向量指令挂死";vstart 直接相关的只有 #6298。历史背景:PR #3249(wdata≥VLEN 只写 vstart 低 7 位)、PR #2248(曾为向量算术加 vstart illegal 检查)。**0/38 有专属报告。**

**B 类 77 形态合计:0/77 有专属报告 → 系统性活性 bug(vstart 超界后执行向量指令致核停止提交)完全未被报告,167 条 PoC 均为新颖发现。**

## E2 类逐条核查(37 条,已完成:0 条被既有 issue 覆盖)

判定口径提醒:虽然逐条检索 0 命中,但其中 34 条 vstart 类的根因主题(vstart 触发 Sail `get_start_element()` 超界检查而 RTL/NEMU 不 trap)与 **#6298 属同一缺失**,按口径记为 **#6298 的边界补充 case**(vstart=VLMAX、LMUL=8 恰触 Sail 上界 8·VLEN/SEW);vsm.v 3 条为独立的 MMIO/PMA 建模差异观察(原创,归环境/工具类)。

| case | 指令 | 检索结论 |
|---|---|---|
| case-1113 / case-1179 | vasubu.vx | 无覆盖(仅 #5931 段加载,无关;NEMU 空) |
| case-523 / case-818 | vmadd.vv / vmadd.vx | 无覆盖(两仓库 "vmadd" 空) |
| case-3764 | vmsgt.vi | 无覆盖 |
| case-6574 | vmsgtu.vx | 无覆盖 |
| case-6631 | vmsleu.vx | 无覆盖 |
| case-5467 | vmsltu.vv | 无覆盖 |
| case-662 | vmulhu.vv | 无覆盖 |
| case-734 | vnmsac.vx | 无覆盖 |
| case-1039 | vremu.vx | 无覆盖 |
| case-4187 / case-4324 | vrgather.vi | 无覆盖(#5780/#3200/#3488/#2890 均非 vstart 行为) |
| case-6866 / case-6875 | vrgather.vx | 无覆盖 |
| case-4617 / case-6990 | vrsub.vi / vrsub.vx | 无覆盖(#5922 vfmerge frm,无关) |
| case-5566 / case-6707 / case-6721 | vsbc.vvm / vsbc.vxm | 无覆盖("vsbc" 两仓库空) |
| case-1137 / case-1152 / case-905 / case-947 | vslide1up.vx(4 条) | 无覆盖("vslide1up" 两仓库空) |
| case-4251 / case-4262 | vslidedown.vi | 无覆盖(#3488 性能;NEMU #768 为 vslide 译码表冗余错误 PR#770 修复,非 vstart 语义) |
| case-4218 / case-4421 | vslideup.vi | 无覆盖(#5931/#3488 无关) |
| case-6879 / case-6891 / case-6892 / case-6960 | vslideup.vx(4 条) | 无覆盖 |
| case-4737 / case-4740 / case-4755 | vsm.v v0,(x31)(MMIO store 未 fault) | 无覆盖(#6482 是 fault 触发但 mtval 陈旧;NEMU #1078 是 funct3 保留编码译码;#5279 白名单)——**独立原创观察** |
| case-7056 | vsmul.vx | 无覆盖(#6555 是 vssubu vxsat;NEMU #1077 是 vmv\<nr\>r 保留 NREG) |
| case-4626 | vsrl.vi | 无覆盖(#6545 白名单是 vsrl.vv v0.t 挂起,非 illegal 缺失) |

宽谱排除:"vstart" 全量 30 条命中中最接近的只有 #6298(超界+单侧)与 #6036/NEMU#1077(vmv\<nr\>r),其余均为 fault 后 vstart 数值问题;"vstart illegal"/"non-zero vstart" 两仓库无结果。

## 重要修正:B 类"A/B 类 timeout"复核受满载干扰(2026-09-18 空载重测)

全量 9,109 条以 -j48 满载运行,timeout=30s;no-payload-commit 的 461 条 timeout 判定**有一部分是负载假象**。空载复核(同 ELF、`--no-diff`、40s)结果:

- **167 条 B 类(vstart>VLMAX + no-payload-commit)中:105 条空载 --no-diff 正常 GOODTRAP**(payload 被译码层 `vstartIllegal = isVArith && vstart≠0` 检查干净 EX_II → handler → GOODTRAP,满载下 30s 完不成造成假 timeout);**62 条空载 --no-diff 仍挂死**(真 RTL 活性 bug)。真挂的指令族(vslide1up/vslide1down、vnsrl/vnsra/vnclip/vnclipu、vandn、vid.v、vmsne.vi、vaaddu.vx 等)不在译码检查覆盖内(`FuType.vecArith = vecOPI++vecOPF` 不含这些执行单元所在的族),真正执行后落入 DecodeUnitComp 的 vstart 重启机制(uop0.flushPipe/lastUop.blockBackward/强制 isDependOldVd,`Rob.scala:747` 仅在 dirtyVs 提交时清 vstart)→ 超界 vstart 下 ROB 写回等待无法满足 → 零提交。
- 代表:case-4859(vrev8.v, vstart=2^63)、case-3802/3829(vid.v)空载 --no-diff 仍挂;case-622/1089(vstart=0x40,vaadd.vv/vasub.vx)空载正常。
- **62 条真挂的逐形态分布**:vwsll.vx(10)、vandn.vx(3)、vid.v(3)、vrol.vx(3)、vror.vi(3)、vror.vx(3)、vwsll.vi(3)、vslide1up.vx(2)、vnclip.wx(2)、vnclipu.wx(2)、vmadc.vim(2)、vwsll.vv(2)、vmsgt.vx(2)、vmsbc.vxm(2)、以及各 1 条的 vaaddu.vx/vslide1down.vx/vnsrl.wi/vnclipu.wi/vnsrl.wv/vnsra.wx/vnsrl.wx/vmsne.vi/vadc.vim/vrev8.v/vror.vv/vmseq.vv/vmsltu.vv/vrgather.vv/vslidedown.vx/vwmacc.vv/vwmaccsu.vx/vwadd.wv/vwaddu.vx/vwmul.vx(清单:`work/isla-trap-entries/rerun-b/no_diff_results.json`)。
- A 类 294 条的空载 --diff 重测进行中(此前"工具挂死"定性同样基于满载复核,需重证)。

## RTL 源码根因定位

### B 类:vstart 挂死机制(源码实证)

- 译码层检查存在:`VecExceptionGen.scala:279-280` `vstartIllegal = isVArith && (vstart =/= 0.U)` → EX_II;FU 层双保险 `FuncUnit.scala:299-307`、`VecNonPipedFuncUnit.scala:46-54`。
- **检查覆盖不全**:`FuType.scala:117` `vecArith = vecOPI++vecOPF`,不含 vmove/向量访存/vshf/vppu/vfix 等族 → 这些族 vstart≠0 时真正执行(agent 实测 vmv.v.i + vstart=0x40 正常提交,精确复现 #6298)。
- 执行后的挂死链:`DecodeUnitComp.scala:204-207,1983`(vstart 重启机制)+ `Rob.scala:747`(仅 dirtyVs 提交清 vstart)→ 超界 vstart 时写回等待无法满足 → 头部零提交(62 条空载实证)。

### D 类:vnclip/vnclipu SEW=16 narrowing 的 vxsat 位错配(已闭环)

- **位置**:`yunsuan/.../VectorALU/VIAluMisc.scala:371-376` + `xiangshan/.../fu/wrapper/VIAluFix.scala:172-176,182`
- **机制**:SEW=16 时每 64b 模块的 `nClipSat` 仅 2 位有效(bit0=模块内元素0、bit1=元素1,未按字节复制);而 `VIAluFix` 把 vxsat 与**字节粒度**的 `activeEn` 做 AND(每 16b 元素占 2 个 active 位)。奇数元素的 sat 位(1/5/9/13)与其 active 位(2,3/6,7/10,11/14,15)**永不重叠**,AND 后恒 0——凡饱和只发生在奇数下标(4k+1/4k+3)的 active 元素上,vxsat 就不置位。masked 时 active 子集小,更易"只有奇元素饱和"而暴露;旧路径 `VFixPoint64b.scala:264` 用 `Fill(2,…)` 做了字节复制(正确写法),新 VIAluMisc 路径漏掉。sel8/sel32 天然对齐,仅 SEW=16 narrowing(vnclip/vnclipu)受影响。
- **推论**:unmasked 同样会丢(只要饱和元素仅为奇数下标);本次 unmasked 样本未分歧只是全 active 时偶元素通常也饱和。→ 给 #6555 追加 PoC 时可附此根因与"偶元素不饱和"的加强构造。

### B 类:vstart 超界挂死根因(核查中,待填充)
