# 带 SMT 的全符号 LOAD／STORE（2026-11-20）

## 输入和运行

在 `perf/smt-long-20261120` 独立工作树上构建冻结的 `isarch`。Sail-RISC-V 主线为 `6dc62eaf`。简报写的两个 `20261120` 输入目录在准备时不存在。IR 复制自 `sail-revert-recheck-20261119/reverted/rv64d.ir`，内容 SHA-256 与 SMT 首轮一致。该 IR 由 Sail 0.20.1 和还原模型 `2edce019` 生成。主线 Sail 源码有偏差时，以冻结 IR 为准。无 SMT 基线沿用 `isla-nosmt-long3-20261119` 的原始配置与进度。 [IR 来源](ir-sha256.txt) · [冻结版本](isla-version.txt) · [生成记录](../../isla-sail-revert-recheck-20261119/experiments/sail-revert-recheck-20261119/verification.md) · [无 SMT 参考配置](scenario-nosmt-long3.toml)

本机 LOAD、STORE 同批启动，各 T32，PMP 64／可写 32，全符号前态，开启 SMT、路径合并、延后出口检查、延后 Z3 作用域、见证求值及缺省有限域枚举，沿用两类模型异常和 match failure 过滤。JoinPlan、内存写汇合、循环及调用汇合随当前路径合并启用。按简报第二轮要求启用新能力，本轮同时显式开启缺省关闭的独立错误叶 `arm_error_leaf`。诊断启用逐 check 计时。逐路径 1,200 秒，程序／外限 7,200／7,800 秒，单次 `--smt-timeout` 沿缺省。求解 Unknown／Timeout 的默认处置为 dead，若有路径因此丢弃且程序走到汇总出口，退出码为 66。 [实际配置](scenario.toml)

```sh
z3_prefix="$HOME/.local/opt/z3-official-d6c9b4fbb"
env ISLA_Z3_PREFIX="$z3_prefix" CARGO_BUILD_JOBS=16 CARGO_TARGET_DIR="$PWD/target" \
  timeout --kill-after=5s 1800s cargo build --locked --release --bin isarch --features smt-thread-interrupt
env -u LD_LIBRARY_PATH ldd target/release/isarch
python3 artifacts/build-observer.py target/release/isarch "$z3_prefix"
python3 -u artifacts/run-long.py
python3 artifacts/audit.py
python3 artifacts/compare.py > artifacts/comparison.md
```

## 统计口径

沿用上一轮的内置逐 check 事件和外部只读采集器。后者经 `LD_PRELOAD` 转发相同的官方 Z3 5.4.0 动态库，观测存活 context、整个进程的 Z3 分配估计、在途 check，以及已返回 check 的调用位置。Z3 分配估计含共享对象，Rust 求解器容器内存单独观测。枚举使用 `fork_symbolic_value`，候选重试使用 `retry_partition` 或 `concrete_consumer` 的调用栈归属。两者有重叠时只计一次总开销。原生计时记录 Z3 check 本身的墙钟，各执行线程累计。短栈或到达 80 帧上限时另报告次数，栈归属依赖编译产物保留的函数范围。 [采集器](observe-z3.c) · [监控器](run-long.py)

进度每 900 秒写一行每项数据，另保存启动和退出行。区域内退回标签、逐路径到限、原生 Z3 check／模型求值超时、实际丢路径分开统计。监控器仅收尾本轮进程。连续 30 分钟无进展且 RSS 无增长时停止该项。主机 `MemAvailable` 低于 16 GiB 时先收尾本轮 RSS 较高的一项。完整缓存触发既有口径的 `--check-samples`／judge。 [进度](progress.tsv) · [judge 脚本](run-judge.py)
