# 当前任务

- 2026-11-08 [fuzz 第 7 步](../agents/path_merge_call_support/fuzz-step7.md)：E2 四场景各 1000 例完成：3093 agree、907 条 R-XS-001、0 新分歧；5000 个 corpus entry 重新认证、3800 个 A/B 命中与唯一性均 100%，四场景确定性通过；Rust 1149、Python 142+9 通过，九个运行目录无所属残留；首次 Sv48 STORE 的 3 个超时、16 个取消原件保留并完整重跑。

- 2026-11-08 [fuzz 第 6a 步](../agents/path_merge_call_support/fuzz-step6a.md)：枚举允许集合已实现；四场景 E2 5000 个 corpus entry 的第 0 步与独立检查全通过，122 条 DAG 重读一致；Sv39 LOAD 1359/200/26，E0 samples 逐字节一致，Rust 1148/0/6；Sv48 LOAD 首轮超时、单进程 64 线程完成。

- 2026-11-08 [fuzz 第 5 步](../agents/path_merge_call_support/fuzz-step5.md)：实现与 8000 例对照完成，0 新分歧、0 基础设施失败；两个场景均未同时达成新增桶与已知问题耗时两项收益目标，未调参过拟合；Rust 1142、Python 127+6 通过，1000 例硬件重跑的 50 个正式产物逐字节相同，无所属进程残留。

- 2026-11-08 [fuzz 第 4 步](../agents/path_merge_call_support/fuzz-step4.md)：确定性并行生成完成，STORE/LOAD 的 2000 例验收每千个生成 37.5/43.9 秒，约提速 26.2/22.1 倍；300 例跨线程逐字节相同；历史分歧 14/14 窄规则命中、正常 corpus entry 200/200 agree，真实 300 例为 251 agree、49 已知分歧、0 新分歧；Rust 1138、Python 原有 127 与新增 6 项通过，取消和超时清理通过。

- 2026-11-08 [fuzz 第 3 步](../agents/path_merge_call_support/fuzz-step3.md)：A/B 11400/11400 经认证命中目标、多样性 100%；两场景三初值的覆盖对照、同初值逐字节复验及 DAG 重读完成；1134 项测试通过，普通循环 STORE/LOAD 为 993.1/982.0 秒每千个。未接 emu、未改 Python；后续为 worker 闭环，生成串行是当前瓶颈。

- 2026-11-08 [fuzz 第 2 步](../agents/path_merge_call_support/fuzz-step2.md)：正式子命令、五个 trait、corpus 认证和 P1b 回放完成；四场景 2836 个 corpus entry、5000 个 mutant 与 P1b 零差异，60 个产物重复运行逐字节相同；1128 项测试通过，保留 partial／errors=5/7；未接 emu。 后续为架构第 3 步。

- 2026-11-08 [fuzz 第 1 步](../agents/path_merge_call_support/fuzz-step1.md)：完成耗时拆分、当前路径静态证明、快档与输入队列并行。380 个 corpus entry＋1000 个 mutant 两档在 1／32 线程下逐字段零差异，三个负对照均零接纳；整批纯判定墙钟提速 8.30／65.75 倍，CPU 成本缩减 8.35／5.95 倍，1115 通过／0 失败／6 项既有忽略。仍保留全部路径扫描、条件不足时调用认证档及原 partial／errors=5；后续为架构第 2 步，本轮不扩功能。

- 2026-11-08 [fuzz M0](../agents/path_merge_call_support/fuzz-m0.md)：基于 78b04e3 完成隐藏参数常驻路径原型；32/1 线程下 26 路径恢复、1380 正例完整字段零差异、三个负对照零接纳；最终构建和 1109 项测试通过。32 线程变异体纯判定 234.141 秒，历史重新探索批次 266.366 秒；整批未显著提速，保留 partial／errors=5。

- 2026-11-07 [judge 模式](../agents/path_merge_call_support/judge-mode.md)：基于 ae1a335，已实现并通过工作区测试；ecfg4b 2836 种子的五项验证与三个零接纳负对照通过；2836 行完整样本再喂入 J1 全部通过；保留原 partial/排除域终止。

- 2026-11-05 [路径合并区域化推演](../agents/path_merge_call_support/status.md)：主体完成并提交（HEAD 36433cf）。函数级 `pte_is_invalid` 分叉 10 条→合并 1 条（Z3 等价检查 23/23）；Sv39 LOAD 合并 52 条路径完整结束，分叉模式 1800 秒未结束（8705 条已输出）。`isla-lib` 全量 682 通过、12 失败与 HEAD 基线相同。待办：Sv39 级覆盖等价性对照、后处理枚举实现。
- 2026-11-06 [Sv39 页表分布求解](../agents/path_merge_call_support/status.md)：合并 20 条路径、枚举 448 秒得 16592 类／样本（分叉 861 秒），形状 104 种，103 种与分叉一致，2 项代表值差异；方向 A 1509/1509、方向 B 40/40 通过（B 仅抽样）。HEAD 6c943c5。

- 2026-11-05 [可选执行统计](../agents/execution_stats/status.md)：完成实现及限定验证；`ISLA_STATS=1` 输出合并统计与前 30 个分叉位置，cargo check、9 个定向测试通过。未跑 Sv39／完整 CLI 输出对照，改动未提交。

- 2026-11-04 [Review 37 四组修复](../agents/review37/status.md)：进行中；完整复现补丁已应用，失败基线 3/8 通过，最终验证待执行。

- 2026-11-04 [Review 36 五组修复](../agents/review36/status.md)：完成；F1～F5 已修复，最终审查 8/8、边界 6/6、核心 574/574、内存模型 33/33、工作区 807 项通过，扩展 feature 637/637 及格式检查通过。额外 MRET 退出 0、4 条，但保留基线 partial／1 条 Poison 路径。改动未提交，未执行全部 ISA clause。


- 2026-11-04 [Review 35 七项修复](../agents/review35/status.md)：完成。F1～F7 已修复；复现 20/20、核心 9/9、内存集成 11/11、核心全量 574/574、内存模型 33/33、应用全量 152/152、扩展 feature 全量 637/637、MRET 4 条及格式检查全部通过。改动未提交，未执行全部 ISA clause。

- 2026-11-04 [Review 34 三个缺陷修复](../agents/review34/status.md)：完成。复现补丁已应用，两个 P1 与一个 P2 已修复；Review 34 核心 7/7、内存复现 1/1、Review 33 筛选 10/10、内存模型 32/32、`isla-lib` 全量 560/560、`isla` 全量 151/151、`itrace,smtperf` 全量 623/623、MRET smoke 4 条及格式检查全部通过。改动未提交，未执行全部 ISA clause。

- 2026-11-04 [Review 33 两个 P1 修复](../agents/review33/status.md)：完成。复现补丁已应用，两个生产修复及旧写侧错误类型断言修订已验证；Review 33 单元 4/4、内存模型 31/31、`isla-lib` 全量 553/553、`isla` 全量 150/150、MRET smoke 4 条及格式检查均通过。改动未提交，未执行全部 ISA clause。


## 2026-11-06 分量诊断（测量与设计完成）

edee95d + 只读环境变量诊断，count/-T 64：Sv39 LOAD 16592 类（49s）、Sv48 LOAD 122654 类（454s）、Sv48 STORE 51638 类（97s），全部完整结束。原约束图每路径 1 分量；候选分组 Sv39 20/20 路径守卫域可乘，两个 Sv48 场景各 6 条路径不可乘，均有原求解器确认的缺失组合 UNSAT。未实现生产分解或紧凑输出；片段域与完整状态组合仍待验证。isla-lib 709 通过／既有 12 失败／6 忽略，格式检查与指定 target_f7 构建通过。[结果与设计](../agents/path_merge_call_support/enumeration.md)、[机器记录](../agents/path_merge_call_support/component-results.json)、[状态和下一步](../agents/path_merge_call_support/status.md)。
