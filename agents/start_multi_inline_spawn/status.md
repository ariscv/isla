# start_multi_inline_spawn 状态

## 当前修改热点

- `isla-lib/src/executor.rs`
  - 给 `MultiRuntime` 增加默认关闭的观测字段。
  - 设置 `ISLA_MULTI_STATS=1` 且 `start_multi(...)` 自然结束时，会输出 submitted、spawned、queued、completed、peak_active、max_queue、run_ms、collect_ms。
  - 该统计不改变调度语义；100 秒 timeout 杀进程时不会打印最终统计。

- `isla-lib/src/isarch_exec.rs`
  - `run_symbolic_execute(...)` 从 `execute_ir_function_with_checkpoint(...)` 切到 `execute_ir_function_with_checkpoint_multi_thread(...)`。
  - 原调用固定走 `start_single(...)`，导致 `zCLMUL` 虽然路径爆炸，但日志全为 `tid:0`，CPU 接近单核。

- `agents/start_multi_inline_spawn/run_cpu_profile.sh`
  - 修正 `wait` 失败时 `run_exit_code` 被 `! wait` 取反成 `0` 的记录问题。
  - 后续 timeout 终止时 summary 应能正确记录非零退出码。

## 观测结果

- 单线程 helper 版本：
  - 命令：`env ISLA_MULTI_STATS=1 TIMEOUT_SECS=100 agents/start_multi_inline_spawn/run_cpu_profile.sh zclmul_stats`
  - 结果文件：`agents/start_multi_inline_spawn/out/zclmul_stats_20260424_144009.*`
  - 平均 CPU：`96.91%`
  - 峰值 CPU：`101.00%`
  - `log` 中完成路径均为 `tid:0`。

- multi helper 版本：
  - 命令：`env ISLA_MULTI_STATS=1 TIMEOUT_SECS=100 agents/start_multi_inline_spawn/run_cpu_profile.sh zclmul_multi_stats`
  - 结果文件：`agents/start_multi_inline_spawn/out/zclmul_multi_stats_20260424_144241.*`
  - 平均 CPU：`4877.11%`
  - 峰值 CPU：`8572.00%`
  - `log` 中观测到 `60` 个不同 `tid`。

## 当前判断

- `zCLMUL` 可以作为路径爆炸指令观察 `start_multi` 并行度。
- 当前低 CPU 的首要原因不是 inline spawn 调度器没有能力并行，而是 `isarch_exec.rs` 调试路径之前没有进入 `start_multi`。
- `println!`/`eprintln!` 会使用全局 stdout/stderr 锁；在多线程 collector 大量打印路径状态时，会形成串行区，影响完成路径的吞吐。
- 但本次单核瓶颈的主因不是终端锁，而是单线程入口；切到 multi helper 后，即使仍保留大量打印，CPU 已能提升到数十核级别。

## 后续关注

- 如果要继续提高多线程版本上限，应优先减少 collector 中每条路径的同步输出和全局 `Arc<Mutex<AssemGen_Json>>` 临界区。
- 可将路径级详细打印改成环境变量控制，或每线程缓冲后批量写入，减少 stdout/stderr 锁争用。
