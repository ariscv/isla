# vector_update 改纯验收记录

基线为 `cbd25fc3`。只修改当前工作树，没有执行 git 写操作或 isarch 长时实测；输出和临时文件均位于本工作树。

## TDD

- `red.log`：生产代码修改前，四项新增测试均失败。效应预检拒绝、区域没有进入动态候选、类型错误未包含全部实参，均符合预期。
- 合并用例沿用已有区域局部槽位规则，在臂内消费更新后的普通向量；不要求扩大汇合点处的向量值合并能力。`preflight-red.log` 记录最终用例在旧 `WritesState` 分类下失败。
- `green.log`：最终四项新增测试全部通过。

新增测试位于 `isla-lib/src/executor/tests/region_global_state_tests.rs`：

1. `region_m2_vector_update_preflight_and_merge`：打开 `region_global_state`，通过静态预检，两条分叉路径合为一条；求解器证明返回值等于分支条件，且与普通分叉的结果和覆盖等价。
2. `region_m2_vector_update_symbolic_length_rollback`：先确认原语返回 `SymbolicLength`，再确认区域已通过预检，以 `retry_operand` 动态拒绝。
3. `region_m2_vector_update_out_of_bounds_rollback`：先确认原语返回 `OutOfBounds`，再确认区域已通过预检，以 `incompatible_state` 动态拒绝。
4. `region_m2_vector_update_invalid_index_retains_arguments`：类型错误消息包含完整实参和原有源码位置。

两个错误用例均检查：事务深度恢复为零，迹长度不变，寄存器、向量和索引保持原值，临时槽位、合并记录和推演状态不泄漏，任务队列为空，份额不变，分支条件与合法/越界索引的组合仍全部可满足。

既有实现证据：`symbolic_length::fork_retry_operand` 在区域内需要真实分叉时返回 `RetryOperand`；`region_merge::execute_region` 的错误分支回滚臂事务并将普通执行错误归为 `IncompatibleState`；`region_merge::try_region` 在执行失败时再回滚整个区域事务。

## 最终检查与失败对比

- `cargo fmt --check`、`git diff --check` 通过。
- `cargo test -p isla-lib`：单元测试从 830 项通过变为 834 项通过，均为 0 失败、7 忽略；随后均仅因 `smt_initialization` 失败而退出 101。原因相同：Z3 4.13.3.0 的默认策略不支持随机种子参数。
- 顶层 `cargo test`：前后均为 233 项通过、7 项失败，均退出 101。7 项均因根目录缺少 `rv64d.ir` 失败。
- 完整失败名单和各测试目标汇总见 `test-comparison.json`，新增失败为空。原始日志为 `baseline-lib.log`、`baseline-top.log`、`final-lib.log`、`final-top.log`。
- 使用 16 个构建任务；临时目录为本目录下的 `tmp/`。

## M0 同测量复测

`measurement.log` 记录 `regions_loop_merge_real_ir_measurement` 通过；使用 M0 相同 IR、配置、快照、入口与权重，并打开 `region_global_state`。报告脚本逐项核对输入和区域分类一致。

可通过权重从 8969 增至 11385，新增 2416；预检拒绝权重从 2416 降至 0；仍有环权重保持 10。逐 clause 数字与复现方法见 `../m0.md` 的“vector_update 改纯后预检”，原始结果见 `../vector-update.json`。这是静态预检结果，不代表动态合并成功数或实际加速。
