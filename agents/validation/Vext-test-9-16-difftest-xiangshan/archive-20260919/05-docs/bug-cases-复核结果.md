# 逐条 bug 独立复核结果(每条一个独立上下文 subagent)

日期:2026-09-18。方法:44 条独立 bug(见 `bug-cases-清单.json`),每条派一个全新 subagent(不带先前判定),独立到 OpenXiangShan/XiangShan 与 NEMU 仓库检索,输出"原创 / 已被 issue 覆盖 / 部分覆盖"判定。

## 第 1 批(8 条,B 类挂死族,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| B-vaaddu.vx | 部分覆盖 | #6298 覆盖"超界 vstart 不 trap"触发前提(vmv.v.i、正常提交、DiffTest mismatch);"vstart 超界→核零提交挂死"零报告(搜索词 vaaddu/vstart/vector hang/deadlock/no commit,双仓库) |
| B-vslide1up.vx | 部分覆盖 | vslide1up 双仓零命中;#6298 现象为核仍在提交非挂死;挂死类 #6566/#6209 无关;**活性挂死半原创** |
| B-vslide1down.vx | 部分覆盖 | 零命中;#6298(vmv.v.i, vstart=0x66)未报告挂死/零提交,不涉及 vslide1down 或 vstart=2^51 极端值 |
| B-vnsrl.wi | 部分覆盖 | vnsrl 双仓零命中;#6298 同根因但现象仅 DiffTest mismatch;零 commit 挂死 + --no-diff 纯 RTL 复现未被覆盖 |
| B-vnclipu.wi | 部分覆盖 | vnclipu 零命中;#6555 是 vssubu vxsat 标志问题无关;#6298 覆盖触发前提;挂死新现象,建议提报引用 #6298 |
| B-vnsrl.wv | 部分覆盖 | #6298 被维护者归为 #6293 向量大修遗留;vnsrl 零命中;"vector deadlock"/"narrowing"/"no commit" 无向量相关命中;挂死为新现象 |
| B-vnsra.wx | 部分覆盖 | vnsra 双仓零命中;#6036(vmv1r)指令症状均不同;#5777 为 MinimalConfig 配置问题;挂死现象原创 |
| B-vnsrl.wx | 部分覆盖 | 零命中;#6298/#6036 仅覆盖语义分歧;"零提交/挂死"症状无任何 issue |

**批内一致性**:8 个独立上下文 subagent 判定完全一致——#6298 已覆盖"超界 vstart 不 trap"的语义分歧(其 PoC vmv.v.i 正常提交),但**"零提交挂死(含 --no-diff 纯 RTL 复现)"这一活性现象无任何既有报告**。

## 第 2 批(8 条,B 类挂死族,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| B-vnclip.wx | 部分覆盖 | #6298 触发根因一致(正常提交,未涉及挂死);#6555 仅 vxsat 无关;#5777 为 sc.w;NEMU 零命中 |
| B-vnclipu.wx | 部分覆盖 | #6298 为 vstart=0x66 轻微超界正常提交;本条 vstart=2^63 极端超界零 commit 挂死纯 RTL 复现,未见覆盖 |
| B-vandn.vx | 部分覆盖 | #6298/#6036 均仅 DiffTest 分歧无挂死;vandn 双仓零命中 |
| B-vmsne.vi | 部分覆盖 | #6298 同根因(vmv.v.i 正常提交);vmsne.vi+vstart=2^52 零提交挂死未被覆盖 |
| B-vid.v | 部分覆盖(核心现象原创) | "vid.v" 仅 #4190 双发射无关、"viota" 仅 #2890 早期 benchmark(无 vstart);#6298 维护者定性"未实现功能";挂死原创,规范层面前置被 #6298/#6036 覆盖 |
| B-vadc.vim | 部分覆盖 | vadc 双仓零命中;"vector stuck" 零命中;#6298 覆盖一半(Sail 侧一致);挂死半边零覆盖 |
| B-vmadc.vim | 部分覆盖 | #6536 核实为 vmadc.vi tail 位数据 bug 无关;#6298 现象/指令/量级均不同;挂死为原创现象 |
| B-vrev8.v | 部分覆盖 | vrev8/vbrev/vector deadlock 双仓零命中;"stop commit" 命中 #6262/#6289/#6543 均无关;挂死症状无覆盖 |

**前 16 条汇总**:16 个独立 subagent 判定完全一致——#6298 覆盖"超界 vstart 不 trap"(vmv.v.i 正常提交的 DiffTest 分歧),**"零提交挂死(--no-diff 纯 RTL 复现)"在全部检索中零命中,活性现象原创**。

## 第 3 批(8 条,B 类挂死族,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| B-vrol.vx | 部分覆盖 | vrol 双仓零命中;#6298 覆盖根因类别(vmv.v.i 正常提交)未涉及 vrol/2^63/零提交挂死 |
| B-vror.vi | 部分覆盖 | vror 双仓零命中;#6298 语义同源但现象仅 DiffTest mismatch;挂死未被覆盖 |
| B-vror.vv | 部分覆盖 | 同上;#6036 已关闭不相关 |
| B-vror.vx | 部分覆盖 | #6298 是"漏 trap、正常提交",本条是"零提交挂死"——不同故障模式;#5777 为 LR/SC;建议新开 issue 引用 #6298 |
| B-vmseq.vv | 部分覆盖 | vmseq 双仓零命中;根因/语义面被 #6298 覆盖;挂死现象原创 |
| B-vmsltu.vv | 部分覆盖 | vmsltu 双仓零命中;症状层面原创 |
| B-vrgather.vv | 部分覆盖 | #6298/#6036 均正常提交;vrgather+NEMU 双仓零专属命中;hang 原创 |
| B-vwsll.vi | 部分覆盖 | #6298 维护者定性"未实现功能待 revisit";#6298 中 NEMU 是正确报 illegal 的一方;零提交挂死未被覆盖;唯一 vwsll 命中 #5773 实为 flh 无关 |

**前 24 条汇总**:24 个独立 subagent 结论 100% 一致——语义缺陷(超界 vstart 不 trap)被 #6298/#6036 覆盖;**"零提交挂死、--no-diff 纯 RTL 复现"零命中,症状层面原创**。

## 第 4 批(8 条,B 类挂死族,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| B-vwsll.vv | 部分覆盖 | #6298 共享根因类别;停摆现象及 vwsll 均未被报告,具增量原创性 |
| B-vwsll.vx | 部分覆盖 | #6298 触发面相同但失效模式不同(正常提交 vs 零提交挂死);其余 vstart issue 均为 fault 后更新错误族 |
| B-vmsgt.vx | 部分覆盖 | vmsgt 双仓零命中;根因被 #6298 覆盖;挂死为更严重下游表现,建议提交时引用 #6298 |
| B-vmsbc.vxm | 部分覆盖 | vmsbc 仅 #5831 无关;#6298/#6036 覆盖通用缺陷;零提交挂死无覆盖 |
| B-vslidedown.vx | 部分覆盖 | #6298 现象相反(静默执行)且官方称"未支持特性非 bug";挂死不同且更重;#5777 sc.w 无关 |
| B-vwmacc.vv | 部分覆盖 | #6298 触发一致但现象不同;疑同根因新表现;vwmacc 仅 #5931 无关 |
| B-vwmaccsu.vx | 部分覆盖 | vwmaccsu 双仓零命中;纯 RTL 零提交挂死(死锁级、独立现象)无覆盖 |
| B-vwadd.wv | 部分覆盖 | #6298/#6036 前置同源;死锁症状无 issue 覆盖;死锁现象原创 |

**前 32 条汇总**:32 个独立 subagent 结论 100% 一致——B 类(超界 vstart 挂死)在症状层面(零提交、--no-diff 复现)全部原创,根因语义面被 #6298/#6036 覆盖。

## 第 5 批(8 条:B-vwmul.vx + C 类 7 条,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| B-vwmul.vx | 部分覆盖 | #6298 根因条件一致(正常提交);挂死表现无 issue 报告;vwmul NEMU 零相关命中 |
| C-vmerge.vvm | **已被覆盖** | #6410 测试矩阵明确含 vmerge.vvm @ e16m2(与本题 vtype=0x9 同构):执行不 trap、NEMU mcause=2;根因 FuType.vmove 绕过对齐检查一致;#5865 是 vd=v0 另类 |
| C-vmerge.vim | 部分覆盖 | #6410 机制点名 "vmerge.*" 但矩阵只列 vvm,未明确列 vim;#6410 以"v2/v3 非缺陷"关闭与 difftest 复现矛盾,可作重开依据 |
| C-vmerge.vxm | 部分覆盖 | #6410 同根因正文列举 vmerge.*(含 vxm)但矩阵未列 vxm 标量形式 |
| C-vmv.v.v | **已被覆盖** | #6410 矩阵含 vmv.v.v v3,v0(e32m2):完全同类,仅 SEW/LMUL 组合不同 |
| C-vmv.v.i | **已被覆盖** | #6410 矩阵含 vmv.v.i 非法 vd,机制/现象完全一致;本 PoC LMUL=1/8+vl=0 被其 class-wide 结论涵盖 |
| C-vmv.v.x | **已被覆盖** | #6410 矩阵含 vmv.v.x v3,t0(e32m2):同一缺陷的不同 LMUL 配置实例 |
| C-vmv4r.v | **已被覆盖** | #5772(open,type: bug/confirmed)标题即"misaligned registers";#5772 为 vs2 未对齐,本 PoC 为 vd 未对齐,同一 decode 缺失类;#6037(vmv2r)已关;#5919 是 reserved 编码不同 |

**C 类中间汇总**:8 族中 vvm/vmv.v.v/i/x/vmv4r 共 5 族被 #6410/#5772 **矩阵明确覆盖**;vim/vxm 是 #6410 机制通配但矩阵未实测的**变体增量**;vmv8r.v 待第 6 批。

## 第 6 批(3 条,已完成)

| bug_id | 判定 | 独立复核结论摘要 |
|---|---|---|
| C-vmv8r.v | 部分覆盖 | vmv8r 双仓零命中;#5772 仅 vmv4r、#6037 仅 vmv2r;#6410 根因分析泛提 "vmv1r-8r.v bypasses check" 但矩阵无 vmv8r 用例 |
| D-vnclipu.wv-vxsat | 部分覆盖 | #6555 正文仅实测 vssubu.vx,但 Systematic 段明确点名 vnclip* 家族属同一 missing-vxsat 待修范围;未实测 vnclipu.wv |
| VSM-MMIO-store | **原创** | #5279 是 difftest store 比较工具缺陷(无 fault 争议);#6482/#6399 前提是 fault 已触发仅 mtval 错;NEMU #1078 是 funct3 译码;最接近的 #6293 是 vle64ff **load 侧**漏 fault;无 "vsm.v store 未映射地址双侧不 fault" 命中 |

## 44 条逐条复核总汇(2026-09-18,每条一个独立上下文 subagent)

| 类别 | 条数 | 判定分布 |
|---|---:|---|
| B 类(vstart 超界挂死) | 34 形态 | **34/34 部分覆盖**:语义前提被 #6298/#6036 覆盖(其 PoC 均为正常提交),**零提交挂死(--no-diff 复现)症状层面一致确认原创** |
| C 类(misaligned 漏检) | 8 族 | 5 族(vmerge.vvm、vmv.v.v/i/x、vmv4r.v)**已被 #6410/#5772 矩阵明确覆盖**;3 族(vmerge.vim、vmerge.vxm、vmv8r.v)**部分覆盖**(#6410 机制通配但矩阵未实测这些变体) |
| D 类(vnclipu.wv vxsat) | 1 | **部分覆盖**:#6555 点名 vnclip* 家族但未实测 vnclipu.wv(masked 形式) |
| VSM(vsm.v MMIO store 不 fault) | 1 | **原创**:所有已知 issue 均不覆盖(最近邻 #6293 是 load 侧) |

**完全原创(症状级)**:B 类挂死 34 形态、VSM-MMIO 1 形态
**变体增量(机制已报、该形态未实测)**:vmerge.vim/vxm、vmv8r.v、vnclipu.wv-vxsat
**补充 case(矩阵已明确覆盖)**:vmerge.vvm、vmv.v.v/i/x、vmv4r.v

## 分组复核(按将要发的 issue,每组一个独立 subagent,已完成)

| 组 | 将发的 issue | 判定 | 提交策略 |
|---|---|---|---|
| 组 1:vstart 超界挂死(62 条/34 形态) | **整体原创,可新开** | #6298 正文明确 "commits the instruction normally",全文/评论均无挂死表述;"liveness/zero commit/stops committing" 检索零命中;追加到 #6298 大概率被"非 bug"口径吸收 | **新开 issue**:引用 #6298 作对照(其 PoC 正常提交、本组挂死),强调 --no-diff 纯 RTL 复现与 62 条覆盖面;关联 #6545(同类"向量指令不退休"症状);措辞避免被归为 #6298 衍生 |
| 组 2:vnclipu.wv vxsat(2 条+根因) | 追加 #6555 | #6555 open,正文点名 vnclip* 家族;全仓无其它命中;维护者侧称 WIP"尚未支持"与本观察(指令已执行、结果正确、仅 vxsat 不置)矛盾 | **追加评论到 #6555**:突出 ①masked vnclipu.wv SEW=16 PoC ②VIAluMisc nClipSat 字节复制 vs VIAluFix activeEn 错位根因 ③"已执行未置位"反驳"未支持";若仍挂起再拆独立 issue |
| 组 3:misaligned 漏检(201 条) | 追加 #5772 为首选 | #5772 open/confirmed(主追踪线程);#6410 closed/invalid 时间线:成员称开发分支已修将合入 v3,DFPMTS 索要镜像未获回复即关闭;**"master(=7bf51a8805)仍复现"与"开发分支已修"不矛盾(修复未合入 master),勿作重开主论据** | **追加评论 #5772** + 在 #6410 补交 DFPMTS 索要的测试镜像;措辞:"master 仍复现,请告知修复 landed 的 commit/合入计划";附 201 条 PoC(vmerge.vim/vxm、vmv8r.v 为矩阵未实测变体);**不新开**(易被关为重复) |
| 组 4:vsm.v MMIO store 不 fault(3 条) | 值得新开(无重复),预期被定性为环境差异 | "vsm" store 侧漏 fault 无既有 issue;**#5137 是关键先例**(维护者:PMA 配置 0x0~0x10000000 允许 RW 不 fault 是 expected behavior,NEMU 相同机制——双侧一致不 fault 正是该模式延伸);#6293 是 load 侧、#6267 是死锁 | **新开 issue 但措辞定位"规范一致性疑问"而非 bug**:主动引用 #5137 PMA 解释,附两模型对 0x1_0000_0000 的 PMA/MMIO 判定 dump,请求确认该地址 PMA 定性;明确区分 #6267/#6293 |

## 最终行动清单(2026-09-19 按口径复核后定稿)

判定口径:①已有 issue 报告过的行为算补充 case,不算原创;②不违反 RISC-V spec 的行为不算 bug。

| # | 动作 | 内容 | 口径依据 |
|---|---|---|---|
| 1 | **新开 issue(唯一)** | vstart 超界挂死(62 条/34 形态,`--no-diff` 纯 RTL 零提交) | 症状级原创(44 条独立复核零命中);超界 vstart 虽为 reserved(trap 可选),但**无限期失去前进不是 reserved 的合法处理方式**——liveness 缺陷与 spec 合规无关 |
| 2 | 追加评论 #6555 | vnclipu.wv masked vxsat + RTL 根因 | 违反 RVV spec(饱和必须置 vxsat);#6555 已发现该缺陷家族 → 补充 PoC/根因,不算原创 |
| 3 | 追加评论 #5772 / #6410 | misaligned 201 条佐证 + 补镜像 | 违反 RVV spec(寄存器组对齐检查);已被 #6410/#5772 报告 → 补充 case |
| ~~4~~ | ~~撤销~~ | ~~vsm.v MMIO store 不 fault~~ | **不违反 spec**:PMA 为平台定义(Priv spec §3.6;Sail 源码注释自证 "mostly implementation-defined"),Sail 报 fault 仅因其配置表不覆盖该地址,XiangShan/NEMU 的 PMA 表是另一套合法配置 → 按"不违反 spec 不算"口径不提交 |
