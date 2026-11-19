# SMT 等价改写缺省开启

基线为 Isla `c652949e`，交付分支为 `perf/bv-rewrite-default-20261119`。

## 实现

`BvRewrite::default()` 开启三条已有规则。TOML 缺省、CLI 无改写参数和直接构造的求解配置使用同一个缺省值。有 SMT 和无 SMT 的表达式仍在共用翻译入口改写。TOML 的 `false` 和空列表显式关闭，CLI 的 `--bv-rewrite=false` 覆盖 TOML。保留裸 `--bv-rewrite` 和命名规则列表。CLI 帮助、README 和规格已同步。

## 验证环境

Rust 1.93.1，官方 Z3 5.4.0（`d6c9b4fbb`），Sail 0.20.1（`446fb477`）。Cargo 命令在候选树内执行，使用 `--offline --locked -j 8`，以 `build.rustflags` 指定上述 Z3 的本机库目录及 RPATH。Rust 测试栈为 64 MiB。配置红测的第一版夹具省略了整个 `execution_limits` 表，触发测试辅助函数解包空值。改为传入空表后，旧实现按预期以实际值 `BvRewrite(0)`、期望值 `BvRewrite(7)` 失败。

| 验证命令 | 结果 |
| --- | --- |
| `cargo test -p isla-lib --lib smt::rewrite_tests -- --test-threads=1` | 6 项通过，覆盖规则等价性及有无 SMT 的共用翻译入口。 |
| `cargo test -p isla-lib --lib config -- --test-threads=1` | 81 项通过，覆盖默认、显式关闭、空列表、规则选择及 TOML 位置。 |
| `cargo test -p isla --lib region_options -- --test-threads=1` | 9 项通过，覆盖 CLI 缺省、保留 TOML 显式值及覆盖顺序。 |
| `RUST_MIN_STACK=67108864 cargo test -p isla-lib --features smt-thread-interrupt region -- --test-threads=1` | 257 项库测试、1 项集成测试通过，库测试 7 项标记为忽略。 |
| `RUST_MIN_STACK=67108864 ruby test/run_tests.rb --property-filter '^nested_merge_' --property-bin-dir target/release` | B64、B129 各 27 项通过。 |
| `cargo build --release --features smt-thread-interrupt --bin isarch --bin isla-property --bin isla-property129` | 通过。 |
| `cargo fmt --all --check`、`git diff --check` | 通过。 |

## PMP=2 judge

**有限语义签收通过。** 进程退出 0，探索状态为 `finished`。4,859 条保留路径分 152 批对两份输入完成 9,718 次绑定。输入 0 未接纳，输入 1 只接纳一次，后态和守卫赋值均唯一。

与原 SMT 等价改写签收和 `19955761` 常驻判定参照对比，输入 1 的 14 个顶层样本字段全部一致，包括 148 个前态寄存器、147 个后态寄存器、前后访存、ISA 状态、终态和返回值。路径签名、99 位守卫向量与按各自顺序对齐的赋值也一致。

本次运行 559.62 秒，其中探索 449.81 秒，常驻判定 96.64 秒。最大 RSS 为 8.52 GiB。执行超时、SMT 超时、终值查询超时、执行错误和未完成路径均为零，另有 3 条模型异常路径。累计诊断记录了 1,111,687 次数据 ITE 相等改写、160,082 次位掩码改写，符号扩展规则命中为零。三条规则的等价性由上面的 SMT 测试验证，真实签收覆盖本次 LOAD 配方和两份具体输入。

复用父仓 `agents/fuzz_strategy_20261112/exp/cache/inputs/rv64d.ir`。IR 原件的 SHA-256 为 `97199a835168371fec2e4d0cae4145e186c4b1f74232e3d5d3dc4017c4b41b91`。TOML 及两份前态取自父仓 `agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/raw/lazy-pmp2-judge-20261117/inputs/`。使用 `pmp2.toml`（包含 `base-frozen.toml`）和 `judge-input-complete-r4.jsonl`。前态、指令和路径合并参数沿用原签收。省略 CLI 和 TOML 改写值，以实际改写命中确认新缺省启用。

本机直接持有 `.worktree/local-heavy.lock` 运行，程序 `-T 32`。逐路径 120 秒，整次运行 1,800 秒，外层 1,815 秒，给更长逐路径限时留出探索和判定时间。开启区域进展及内存诊断以监控单次运行。测试产物在候选工作树 `output/bv-rewrite-default/`。

```sh
isarch -A rv64d.ir -C pmp2.toml -T 32 --tastic default \
  --instruction-bits 0x00008103 \
  --judge-resident judge-input-complete-r4.jsonl --judge-resident-out judged.jsonl \
  --timeout 120s --merge-diagnostics summary --memory-stats \
  --path-merging --region-defer-exit-check=true --region-lazy-z3-scope=true \
  --region-witness-eval=true --region-progress=true solve-state --clause=LOAD
```

证据位于 `output/bv-rewrite-default/judge/` 下的 `comparison.json`、`raw.log`、`output/rv64_zLOAD.json` 与 `time.txt`。进程已退出并释放本机共享锁。
