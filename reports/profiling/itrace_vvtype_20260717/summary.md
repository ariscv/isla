# VVTYPE 开启 itrace 的性能剖析与对照

## 总结

开启 itrace 后，CPU 热点结构没有发生根本变化：Z3 仍占用户态 cycles 的约 88%，itrace writer 自身没有形成明显的 CPU 热点。性能损失主要表现为 libc 内存操作和锁占比上升、平均并行度下降，以及每条路径记录、复制和最终输出 itrace 带来的累计成本。

在内部 5 分钟 deadline 的同参数全程采样中：

| 指标 | 无 itrace | 开启 itrace | 变化 |
| --- | ---: | ---: | ---: |
| 墙钟时间 | 11:09.21 | 12:07.22 | +8.7% |
| 完成路径 | 72 | 66 | -8.3% |
| 有效吞吐 | 0.1076 路径/秒 | 0.0908 路径/秒 | -15.6% |
| 平均 CPU | 27.38 核 | 25.80 核 | -5.8% |
| 峰值 RSS | 5.19 GiB | 5.31 GiB | +2.3% |
| 文件系统输出计数 | 105,168 | 162,544 | +54.6% |
| itrace 输出 | 0 | 28.37 MB / 602,611 行 | 新增 |

## 用户态 CPU 占比

| 采样窗口 | 配置 | Z3 | libc | isarch/Rust |
| --- | --- | ---: | ---: | ---: |
| 0–2 分钟 | 无 itrace | 87.94% | 9.93% | 0.29% |
| 0–2 分钟 | 开启 itrace | 88.45% | 9.45% | 0.26% |
| 3–4 分钟 | 无 itrace | 89.07% | 9.06% | 0.46% |
| 3–4 分钟 | 开启 itrace | 87.55% | 10.27% | 0.43% |

itrace 的 writer、`submit_path` 和 `record` 等符号直接累计占比低于 0.01%。这不表示 itrace 没有成本：逐指令记录与路径复制大多内联到 executor，并将成本体现为 `memmove`、allocator、锁、缓存/内存压力和更低的有效并行度。

晚期 libc 自耗时变化：

| 函数 | 无 itrace | 开启 itrace |
| --- | ---: | ---: |
| `pthread_mutex_lock` | 2.98% | 3.53% |
| `memmove` | 2.29% | 2.65% |
| `_int_malloc` | 0.85% | 1.06% |
| `_int_free` | 0.60% | 0.65% |

## 路径吞吐和 itrace 增长

| 窗口 | 无 itrace 完成路径 | itrace 完成路径 | itrace 大小 |
| --- | ---: | ---: | ---: |
| 60 秒 | 20 | 20 | 1.10 MB / 22,989 行 |
| 0–2 分钟 | 37 | 35 | 3.73 MB / 77,798 行 |
| 0–4 分钟 | 66 | 59 | 8.31 MB / 174,324 行 |
| 5 分钟 deadline 加队列排空 | 72 | 66 | 28.37 MB / 602,611 行 |

60 秒硬件计数器中，开启 itrace 后 cycles 增加约 3.4%，IPC 从 0.26 降到 0.23。单个短窗口的路径组合存在随机差异，因此吞吐应结合完整运行判断；全程有效吞吐下降约 15.6%。

## itrace 成本来源

启用 `tracetool` 后，executor 每执行一条 IR 指令都会：

1. 克隆当前 backtrace。
2. 向当前路径的 `Vec<ItracePerInstr>` 追加一条记录。
3. 在 fork 的 freeze/unfreeze 过程中克隆整个 `ItracePerPath`，包括此前所有逐指令记录。
4. 路径结束或 timeout 时，把全部记录渲染成文本并交给异步 writer。

因此成本不是固定的每路径常数，而会随路径长度和 fork 时已有的记录数量增长。短期 profiling 测到的是约 5%–15% 的吞吐损失；对于运行数小时后才到达的深路径，路径向量复制和最终渲染可能进一步放大。当前 0–4 分钟采样没有复现十倍变慢，因此不能仅凭本次短窗口确认 `<1s -> 10s` 全部由 itrace 引起。

## SMT 热点是否变化

开启 itrace 后主要 SMT 调用路径仍相同：

- `Solver::check_sat_with`
- `proven_symbolic_i128`
- `executor::run_loop` 中的 symbolic branch 查询
- `try_concretize_bool_exp`

晚期累计调用链中，`proven_symbolic_i128` 约 31.62%，`run_loop` 约 22.70%，`try_concretize_bool_exp` 约 5.75%。这些累计占比会互相包含，不能相加。关闭或开启 itrace 都没有改变“Z3 查询是第一瓶颈”这一结论。

## 原始数据

- `perf_current/perf.data`：开启 itrace，0–2 分钟。
- `perf_late/perf.data`：开启 itrace，第 3–4 分钟。
- `stat_current/stat.csv`：开启 itrace，60 秒硬件计数器。
- `full_run/`：内部 5 分钟 deadline 的完整运行、JSON、itrace 和 gperftools 样本。
- 对照数据位于 `../noitrace_vvtype_20260717/`。
