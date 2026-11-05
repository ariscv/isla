# 当前任务

- 2026-11-05 [可选执行统计](../agents/execution_stats/status.md)：完成实现及限定验证；`ISLA_STATS=1` 输出合并统计与前 30 个分叉位置，cargo check、9 个定向测试通过。未跑 Sv39／完整 CLI 输出对照，改动未提交。

- 2026-11-04 [Review 37 四组修复](../agents/review37/status.md)：进行中；完整复现补丁已应用，失败基线 3/8 通过，最终验证待执行。

- 2026-11-04 [Review 36 五组修复](../agents/review36/status.md)：完成；F1～F5 已修复，最终审查 8/8、边界 6/6、核心 574/574、内存模型 33/33、工作区 807 项通过，扩展 feature 637/637 及格式检查通过。额外 MRET 退出 0、4 条，但保留基线 partial／1 条 Poison 路径。改动未提交，未执行全部 ISA clause。


- 2026-11-04 [Review 35 七项修复](../agents/review35/status.md)：完成。F1～F7 已修复；复现 20/20、核心 9/9、内存集成 11/11、核心全量 574/574、内存模型 33/33、应用全量 152/152、扩展 feature 全量 637/637、MRET 4 条及格式检查全部通过。改动未提交，未执行全部 ISA clause。

- 2026-11-04 [Review 34 三个缺陷修复](../agents/review34/status.md)：完成。复现补丁已应用，两个 P1 与一个 P2 已修复；Review 34 核心 7/7、内存复现 1/1、Review 33 筛选 10/10、内存模型 32/32、`isla-lib` 全量 560/560、`isla` 全量 151/151、`itrace,smtperf` 全量 623/623、MRET smoke 4 条及格式检查全部通过。改动未提交，未执行全部 ISA clause。

- 2026-11-04 [Review 33 两个 P1 修复](../agents/review33/status.md)：完成。复现补丁已应用，两个生产修复及旧写侧错误类型断言修订已验证；Review 33 单元 4/4、内存模型 31/31、`isla-lib` 全量 553/553、`isla` 全量 150/150、MRET smoke 4 条及格式检查均通过。改动未提交，未执行全部 ISA clause。
