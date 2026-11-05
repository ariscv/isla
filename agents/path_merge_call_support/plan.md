# 路径合并：让分支臂支持函数调用（计划，未实施）

## 目标
合并分支臂时，臂内可以正常调用 Sail 函数（字段读取器、`currentlyEnabled`、`is_prefetch_access`、构造器等），语义与普通路径完全一致；不在 `simulate_diamond_arm` 里另写一份调用逻辑。

## 现状与依据（2026-11-05，单次 60 秒 Sv39 观测）
- 合并尝试 736 次、成功 0 次；臂内 `call` 被拒 336 次，另有 `impure_binary` 168（`range_subset`）。见 `agents/execution_stats/result-20261105-sv39-60s.md`。
- 根因：`simulate_diamond_arm`（executor.rs）是一个独立的小解释器，没有调用、返回、`have_exception` 边、限制记账。给它补调用等于第二次实现主循环语义。

## 技术路径（已定）
让每个臂通过真实主循环 `run_loop_inner` 执行，到达"入口栈深度下 pc == join_pc"为止；退休 `simulate_diamond_arm`。

规则：
1. 停止条件：入口栈深度下 `pc == join_pc`。离开 `[start, join)` 区间（在入口深度）即拒绝候选；被调函数内部不受区间限制，但所有深度共享同一个步数预算。
2. 臂内出现分叉：用拒绝型 fork sink，把它转成候选拒绝。臂内的嵌套合并由主循环 Jump 处理自然发生，需限制递归深度。
3. 可观察副作用（访存、非局部寄存器写、异常）：拒绝候选。纯被调函数必须能通过。
4. `try_merge_diamond` 目前合并依赖 `write_set`、`modified_vars`、`register_reads`（仅小解释器填写）。真实主循环要么在赋值处记录它们，要么改成对臂前后帧做通用差分（变量、let、寄存器、栈）。实施前必须选定其一并写入本文件；不在主循环每处赋值里零散挂钩。
5. 每一项在事务内不安全的主循环行为都要有书面规则（拒绝或事务化）：`last_z3_reset` 定时重置、`fork_sink.submit`、`Run::Dead/Exit/End`、`limit_handler`/`PathTimeout`、迹事件（读写内存/寄存器、announce）。
6. 需要把 `tid/task_id/task_fraction/timeout/stop_conditions/task_state` 传入 `try_merge_diamond`（调用点处已有）。

## 已读代码得到的风险
- 合并后半段（executor.rs `try_merge_diamond` 后半）强依赖两臂的 `write_set`、`register_reads` 及事件顺序（`order_transaction_register_reads`、事后补发 `WriteReg`）。所以这不是"小改"，而是中等到较大的重构；第 4 条是关键设计点。
- 共享代码已有 `speculative` 模式（`register_reads.is_some()`，executor.rs 约 625 行），说明部分投机读取语义在真实路径已有基础。

## 验收
1. 函数级 `pte_is_invalid`（可跑完）：不合并 N 条路径；合并后 1 条；Z3 证明合并返回值等价于各 fork 路径结果的析取；对 flag/ext 位暴力枚举核对。
2. 60 秒 Sv39：`successes > 0`（端到端确认，不作为主要证据）。
3. 现有 `stats`/`diamond`/`path_merging` 测试保持通过。
4. 已知 HEAD 即失败的 5 个 `merge` 测试（`internal_vector_init_after_merge`、`monomorphize_machine_integer_after_merge_does_not_crash`、`internal_vector_update_retries_merged_index`、`review21_merged_overflow_path`、`adversarial_merge_machine_index_width`）先写入 `agents/findings.md`，避免算到本改动头上。

## 未决
- 第 4 条的选择（赋值处记录 vs 前后帧差分）。
- `range_subset` 的不纯二元运算是什么原语、真实循环下是否直接可用。
- 臂内 `have_exception` 边在纯函数调用后恒为假，需确认真实循环下不会被当作越界。
