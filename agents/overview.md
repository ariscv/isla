# 议题入口

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
