# 议题入口

- 2026-11-08 [fuzz 第 8 步](path_merge_call_support/fuzz-step8.md)：PPN 软偏好默认关闭，A/B 优先清零叶 PTE[53:46]、类要求时显式保留并计数；四场景×两初值×开关各 500 例，已知 emu 时间占比 27.28%→0.05%，开启组 1 条 R-XS-001、0 新分歧；覆盖下降照实列出。A/B 命中与唯一性 100%，42 的八组确定性通过；Rust 1150、Python 142+11，无所属残留。

- 2026-11-08 [fuzz 第 7 步](path_merge_call_support/fuzz-step7.md)：E2 四场景各 1000 例完成：3093 agree、907 条 R-XS-001、0 新分歧；5000 个 corpus entry 重新认证、3800 个 A/B 命中与唯一性均 100%，四场景确定性通过；Rust 1149、Python 142+9 通过，九个运行目录无所属残留；首次 Sv48 STORE 的 3 个超时、16 个取消原件保留并完整重跑。

- 2026-11-08 [fuzz 第 6a 步](path_merge_call_support/fuzz-step6a.md)：枚举允许集合已实现；四场景 E2 5000 个 corpus entry 的第 0 步与独立检查全通过，122 条 DAG 重读一致；Sv39 LOAD 1359/200/26，E0 samples 逐字节一致，Rust 1148/0/6；Sv48 LOAD 首轮超时、单进程 64 线程完成。

- [fuzz 第 5 步：字段覆盖反馈与真实对照](path_merge_call_support/fuzz-step5.md)：8000 例完成，0 新分歧；STORE 降低已知耗时但新增桶减少，LOAD 新增桶略增但已知耗时占比上升，收益目标未同时达成；Rust 1142、Python 127+6 通过，1000 例硬件重跑的 50 个产物逐字节相同，无所属进程残留。

- [fuzz 第 4 步：并行生成与三方闭环](path_merge_call_support/fuzz-step4.md)：STORE/LOAD 生成约提速 26.2/22.1 倍；历史分歧 14/14 归类，正常 200/200 一致，真实 300 例为 251 一致、49 已知分歧、0 新分歧；Rust 1138 项通过。

- [fuzz 第 3 步：路径引导与 DAG](path_merge_call_support/fuzz-step3.md)：11400 个 A/B 全部经认证命中目标，多样性 100%，两场景确定性及 DAG 重读通过，1134 项测试通过；当前生成串行，不接 emu。

- [fuzz 第 2 步：正式入口与 P1b 回放](path_merge_call_support/fuzz-step2.md)：四场景 5000 个 mutant 零差异，2836 个 corpus entry 通过认证，60 个产物逐字节稳定，1128 项测试通过。

- [fuzz 第 1 步：耗时与快档](path_merge_call_support/fuzz-step1.md)：2026-11-08 完成；1380 例两档零差异、负对照零接纳；1／32 线程墙钟提速 8.30／65.75 倍，1115 项测试通过。

- [fuzz M0 常驻 judge](path_merge_call_support/fuzz-m0.md)：2026-11-08 完成；32/1 线程下 1380 正例零差异、三个负对照零接纳；恢复语义在本批一致，构建与 1109 项测试通过，整批未显著提速。

- [枚举分量诊断与紧凑样本设计](path_merge_call_support/status.md)：2026-11-06 三场景完整 count；Sv39 候选守卫域可乘，Sv48 各有 6 条路径被原求解器反例否定；仅测量和设计。

- [可选执行统计](execution_stats/status.md)：2026-11-05 合并尝试／拒绝原因和分叉位置直方图已实现，cargo check 与 9 个定向测试通过，未跑 Sv39。

- [Review 37 修复](review37/status.md)：Constrained 数组一致性、区域遮蔽分派、整数绝对值边界及浮点转换格式。

- [Review 36 修复](review36/status.md)：设备写分派、Constrained 生成器、整数边界与回绕排除检查。


- [Review 35 修复](review35/status.md)：宽地址数组索引、向量越界、符号解包错误路径和寄存器过滤。

- [Review 34 修复](review34/status.md)：菱形推测解包、具体内存初值与向量越界路径。

- [Review 33 修复](review33/status.md)：寄存器向量构造子选择与自约束内存普通读。
- 可复用代码事实见 [findings.md](findings.md)，其他既有议题继续按各自目录维护。
