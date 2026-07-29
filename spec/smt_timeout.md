# Z3 timeout wrapper 与 thread-interrupt 规范

## 目标

direct wrapper 保持 commit `2b90ece465874524e4b60c639efbf90b976add69` 的 SMT 语义。可选的 `smt-thread-interrupt` 仅为受保护的 Z3 调用增加软中断 deadline，其余逻辑与 direct 相同。

## 构建实现

| 构建 | feature | 行为 |
| --- | --- | --- |
| direct | 默认 | 直接调用 Z3；timeout 配置不会改变直接调用行为 |
| thread-interrupt | `smt-thread-interrupt` | 对 CheckSat、CheckSatAssuming 和 ModelEval 的 Z3 调用安装 watchdog；deadline 后调用 `Z3_interrupt` 并等待该调用自行返回 |

不再提供 `--z3-interrupt-grace`。thread-interrupt 是软中断：若 Z3 不响应 `Z3_interrupt`，调用线程仍会等待。

## 调用边界

feature 差异集中于 `timeout_z3_*` 调用边界。公共 `Solver`/`Model` 保持 direct Z3 的逻辑模型；`get_var` 和 `get_exp` 不直接选择 feature，而是通过统一的模型求值路径进入对应 wrapper。

当前受保护的 operation：

- `Z3_solver_check`
- `Z3_solver_check_assumptions`
- `Z3_model_eval`

timeout 返回结构化的 `ExecError::Smt(SmtError::Timeout)`，其中包含 source location、operation、limit、operation wall time 和按需 SMT2 dump。普通 Z3 结果和既有 `ExecError` 语义保持不变。

## CLI 与验证

- 非零 `--smt-timeout` 只配置 deadline，不选择调用实现；
- `scripts/run.mk` 的 `Z3_TIMEOUT_IMPL` 仅接受 `direct` 或 `thread_interrupt`；
- 重点回归测试为 `cargo test --test smt_contract` 和 `cargo test --test smt_thread_interrupt --features smt-thread-interrupt`。
