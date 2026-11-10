# M0 / M1 验收记录

完成设计稿实施计划步 0–5：M0 现状测量、M1-a 汇合点修正、M1-b 槽位活跃性截断、差分与回滚原子性，以及 M0 补测。设计稿、IR 和旧日志只读；没有运行 isarch、make solve 或长时动态实测，没有执行 git 写操作。

## 实现范围

- `RegionOptions::filter_assertion_failures` 默认关闭，仅区域查询启用；失败尾部保留在区域中。完整 CFG 继续用于活跃性、边界读取和声明位置，终止证明与静态效应上界不变。
- 活跃性记录读取及赋值目标，只在 `Decl` / `Init` 截断；`Init` 右侧读取保留。地址逃逸、区域外同名声明、RETURN 及基态已有槽位的保护保持有效。
- 差分测试揭示原执行器会在死臂处理前以 `exit` 拒绝 `Exit(AssertionFailure)`；仅对正在区域推演的断言失败跳过该通用拒绝，让既有臂事务处理死亡。普通推演、显式 Exit 和 MatchFailure 保留原行为。
- 未更改路径缓存、RegionMergeRecord、FastFacts 或 DAG 格式；未实现 M2。

## TDD 与测试结果

- M1-a：`m1a-red.log` 记录新循环区域测试以 HasBackEdge 失败；实现后区域测试通过。
- M1-b：`m1b-red.log` 记录重新声明截断和普通赋值目标两个测试均失败；实现后全库单元测试通过。
- 跳转形态断言死臂：`step5-debug.log` 记录因通用 Exit 检查而拒绝；补齐执行层处理后差分通过。
- `step5.log`：60 项区域合并测试通过、5 项忽略；覆盖三轮循环、晚进入合并、两种断言形态、真/假/符号条件、单/双死臂、悲观符号断言拒绝及槽位/寄存器状态和事件。
- 扩展 `region_merge_inner_commit_then_outer_rollback_with_assertion`：两种形态均先确认内层实际提交，再验证外层回滚后约束域、事务深度、寄存器、局部槽位、事件和合并记录无泄漏。
- `cargo fmt --check` 与 `git diff --check` 通过。
- 基线 HEAD：`daf61c04dac3a157d057e852f5c922578aee3fa3`，在任何生产代码修改前运行并记录基线。
- `cargo test -p isla-lib`：基线单元测试 809 通过、6 忽略；修改后单元测试 819 通过、7 忽略、0 失败。两者均随后因 `smt_initialization` 集成测试失败而退出 101。
- `cargo test --no-fail-fast`（顶层）：基线及修改后均为 232 通过、7 失败；其余顶层测试目标及文档测试通过。使用 `--no-fail-fast` 收集全部目标结果。

| 测试包 | 失败测试完整名称 | 对比 |
| --- | --- | --- |
| isla-lib | `smt_initialization` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_f5_继承策略与固定前置权限` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_压缩编码回环与构造子校验` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_向量段store编码回环` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_回环拒绝amoswapq非法编码` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_回环拒绝ldu非法编码` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_回环放行合法load编码` | 基线及修改后均失败 |
| isla | `isarch::exec::tests::encdec_guard_非位向量编码报错` | 基线及修改后均失败 |

新增失败名单为空。`smt_initialization` 的 `executor` 子场景在 `isla-lib/src/smt.rs:2254` 报错：Z3 4.13.3.0 的 tactic Default 不支持随机种子参数 seed / random_seed；顶层 7 项均因根目录缺少 `rv64d.ir` 失败。未为改变验收结果而修改这些既有问题。日志分别为 `baseline-isla-lib.log`、`final-isla-lib.log`、`baseline-isla.log`、`final-isla.log`。

## M0 结论及后续边界

10 个 clause，共 98 个按 clause 分组的入口条目，拒绝权重 11395，遗漏权重 0。现状已无环 10548，有回边 847；M1 后新增无环 837，仍有环 10。新增无环中静态预检通过 222，被 callee_state_write 拒绝 615。全部 M1 无环区域中预检通过 768，因 accrue_fflags 写 fcsr 被拒 10617；直接被调函数与权重见 m0.md，逐节点证据见 m0.json。

静态通过不保证动态合并成功或实测加速。区域死臂使 assertion_filtered_paths 计数减少，按已审核设计接受此口径变化。动态短时对照、长时实测、缓存重新生成以及 M2 留给后续阶段。
