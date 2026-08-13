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

feature 差异集中于 `timeout_Z3_*` 调用边界。公共 `Solver`/`Model` 保持 direct Z3 的逻辑模型；`get_var` 和 `get_exp` 不直接选择 feature，而是通过统一的模型求值路径进入对应 wrapper。

当前受保护的 operation：

- `Z3_solver_check`
- `Z3_solver_check_assumptions`
- `Z3_model_eval`

`Z3_solver_get_model`、`Z3_model_to_string`、`Z3_solver_to_string` 和
`Z3_benchmark_to_smtlib_string` 不属于软中断调用边界，直接使用 `z3-sys` API。

timeout 返回结构化的 `ExecError::Smt(SmtError::Timeout)`，其中包含 source location、operation、limit、operation wall time 和按需 SMT2 dump。普通 Z3 结果和既有 `ExecError` 语义保持不变。

## 路径级 SMT 用时统计与超时诊断

每次受保护调用都会把 `(operation, source location, wall, 是否被中断)` 记进线程局部的
`timeout::SmtCallStats`（调用次数、累计耗时、最慢一次、被中断次数与耗时）。统计与 feature
无关、始终开启；`executor::run_loop` 在每条路径开始执行时清零，因此它就是"这条路径的"统计。

路径撞上 `--timeout` 预算（`executor::PathTimeout`）时，executor 用
`timeout::PathTimeoutDiagnostic` 把统计和预算一起输出到 `SYM_EXEC` 日志（itrace 构建下同时
记进 trace），并给出原因判定：

| 判定 | 触发条件 | 含义 |
| --- | --- | --- |
| `SmtOperationTimeouts` | 被中断调用的累计耗时 ≥ 路径预算的 50% | 少数操作打满 `--smt-timeout`，放宽 `--timeout` 无效 |
| `SlowSmtSolving` | SMT 累计耗时 ≥ active_wall 的 70% | 时间由正常求解累积而成，确实需要更多路径预算 |
| `ExecutorWork` | 其余 | 瓶颈在 executor 解释执行，不在求解器 |

`--smt-timeout` 未配置（direct 构建）时不会有调用被中断，判定只会落在后两类。

## CLI 与验证

- 非零 `--smt-timeout` 只配置 deadline，不选择调用实现；
- `scripts/run.mk` 的 `Z3_TIMEOUT_IMPL` 仅接受 `direct` 或 `thread_interrupt`；
- 重点回归测试为 `cargo test --test smt_contract` 和 `cargo test --test smt_thread_interrupt --features smt-thread-interrupt`。
