# VVTYPE 无 itrace 性能剖析

## 结论

关闭 itrace 后，程序的用户态 CPU 时间仍由 Z3 主导。当前主要瓶颈不是 itrace、日志或 Rust 解释器本身，而是大量 `check_sat_with` 查询，尤其是 primop 为了证明符号整数是唯一常量而进行的候选枚举。

| 采样窗口 | Z3 | libc | isarch/Rust 自耗时 | 说明 |
| --- | ---: | ---: | ---: | --- |
| 启动后 0–2 分钟，现有调试参数 | 87.94% | 9.93% | 0.29% | 94,573 个样本，无丢样 |
| 启动后 0–2 分钟，关闭 probe/trace/debug | 88.60% | 9.61% | 0.11% | 96,672 个样本，无丢样 |
| 启动后 3–4 分钟，现有调试参数 | 89.07% | 9.06% | 0.46% | 60,166 个样本；perf 报告 7 个数据块丢失，但样本丢失计数为 0 |

`libc` 中较大的自耗时为：

- `pthread_mutex_lock`：早期 3.65%，晚期 2.98%。调用栈主要落在 Z3 内部和 Z3 context/solver 操作。
- `memmove`：早期 2.11%，晚期 2.29%。
- malloc/free/realloc 相关函数合计约 3%。

## 主要调用路径

晚期窗口的累计调用链占比为：

| 调用路径 | 累计占比 | 说明 |
| --- | ---: | --- |
| `Solver::check_sat_with` | 40.62% | 进入 `Z3_solver_check_assumptions` |
| `proven_symbolic_i128` | 38.63% | 为符号整数逐个尝试候选常量 |
| `executor::run_loop` | 22.75% | 普通 symbolic branch 两侧可满足性查询等；与上面的调用链有重叠 |
| `try_concretize_bool_exp` | 6.71% | 对 symbolic 布尔表达式最多做两次查询 |
| `concretize_branch_condition` | 0.77% | branch limit 触发后的具体化查询 |
| `probe::args_info` | 0.22% | `--probe-all` 的 trace 克隆和 taint 计算 |
| `Ast::simplify` | 0.17% | SMT AST 简化 |

这些是累计调用链，占比会互相包含，不能相加。例如 `proven_symbolic_i128` 内部调用 `check_sat_with`。

`proven_symbolic_i128` 的候选序列共有 517 个不同值。若当前符号不是唯一常量，且位宽允许表示这些值，一次调用可能执行数百次 `sym != candidate` 的 SMT 查询。该函数又被 `pow2`、`max_int`、`min_int`、`zeros`、shift/length 等多个 primop 调用。

普通 symbolic branch 在执行限制判断之前，也会先分别查询 true 和 false 是否可满足。因此现有 branch 百分比限制主要减少后续路径数量，不能避免当前分支点已经发生的两次 SMT 查询。

## 调试参数对照

60 秒硬件计数器结果：

| 指标 | `--probe-all --trace-all --debug=fmlgcsra` | 仅 `--debug=r` |
| --- | ---: | ---: |
| 平均使用 CPU | 47.31 核 | 48.93 核 |
| cycles | 6.820e12 | 6.564e12 |
| instructions | 1.747e12 | 1.717e12 |
| IPC | 0.26 | 0.26 |
| minor/page faults | 9.22M | 9.56M |
| 完成路径 | 20 | 21 |

去掉 probe/trace/debug 后吞吐只提高约 5%，不同运行的路径组合会产生噪声，因此不能把这个数字当成稳定基准。但结合 CPU 栈可确定：这些调试参数不是数量级变慢的主因。低至 0.26 的 IPC、约 89% 的 Z3 cycles 和大量内存分配更能解释当前长路径。

## 长尾与并行度

全程 gperftools 采样使用内部 5 分钟 deadline，程序在 11 分 09 秒后才正常退出：

- 完成 72 条路径。
- 平均使用 27.38 核，明显低于早期 47–49 核，也低于 `-T 64`。
- 峰值 RSS 约 5.19 GiB。
- 记录约 70.6M minor faults。

这表明墙钟长尾由两部分组成：活跃路径中的 Z3 查询，以及不同路径完成时间不均、共享 deadline 后排空队列造成的并行度下降。后者是墙钟时间问题，不会表现为某个 Rust 函数的高 CPU 自耗时。

## 原始数据

- `perf_current/perf.data`：现有调试参数，0–2 分钟。
- `perf_minimal/perf.data`：关闭 probe/trace/debug，0–2 分钟。
- `perf_late/perf.data`：现有调试参数，第 3–4 分钟。
- `stat_current/stat.csv`、`stat_minimal/stat.csv`：60 秒硬件计数器。
- `cpu.prof_4`：gperftools 全程样本。

本次 release 构建没有启用 `itrace` feature，各隔离输出目录也没有生成 itrace 文件。
