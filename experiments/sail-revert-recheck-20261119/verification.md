# 版本、生成与复验命令

| 组件 | 版本 |
| --- | --- |
| Isla | `dc9e539626c3fa2e073d9961da102d21839282fc`，启动时本地 `isarch` |
| 原模型 | Sail-RISC-V `d877550e7d39f2beb2fda06f6815b1a05127ad33` |
| 还原模型 | Sail-RISC-V `2edce019b471854b118ea68c5a62202fa1ff6a61` |
| Sail | 0.20.1，`446fb477c508853595ccc937ed60765aa685ae31` |
| Z3 | 官方 5.4.0，`d6c9b4fbb31cb76e35cc325dd7e64b7c26c7d70f` |
| Rust / Dune | 1.93.1 / 3.20.2 |

RV64D、VLEN=128、ELEN=64，`model.json` 来自上次还原实验。插件直接在当前 Isla 工作树构建。原模型与还原模型各从空的 Sail 求解缓存开始生成，两份 IR 的内容分别与上次还原实验的对应 IR 一致。Sail 求解与 isarch 动态链接均使用同一个官方 Z3。首次插件命令重复指定 Dune 的 `--root`，纠正后构建通过，两份完整生成分别约 24 分钟。

| 文件 | SHA-256（来源记录） |
| --- | --- |
| `original/rv64d.ir` | `3bfbb612663318f7f1b4bb385ca6e945be82e64419e9b660bd0891a80ea74210` |
| `reverted/rv64d.ir` | `94c807fab1ef35b2e1e5c2a87009c821e8a99123f49ff1a607831c8cb646922f` |
| `sail_plugin_isla.cmxs` | `3a2376867a1e67b8de22bfdc4a251294543e5dbaaff537bc54d074b6732cb13d` |
| `model.json` | `a9d750021e225c710d35a3a7d20e3316c3f84348a9dcbbe6a4ff3ac86534c469` |

从本工作树执行。环境变量 `runner_root` 指向 isla-runner 根目录，`run_data` 指向新建的数据盘目录，`z3_root` 指向官方 5.4 安装目录。

```bash
experiment=experiments/sail-revert-recheck-20261119
CARGO_TARGET_DIR="$run_data/target" RUSTFLAGS="-L native=$z3_root/lib" \
  cargo build --locked --release --features smt-thread-interrupt --bin isarch -j 12
timeout -k 10s 1800s bash "$experiment/generate.sh" "$runner_root" "$run_data" "$z3_root" \
  d877550e7d39f2beb2fda06f6815b1a05127ad33 original
timeout -k 10s 1800s bash "$experiment/generate.sh" "$runner_root" "$run_data" "$z3_root" \
  2edce019b471854b118ea68c5a62202fa1ff6a61 reverted
cp "$experiment/probe.toml" "$run_data/probe.toml"
bash "$experiment/run-checks.sh" "$runner_root" "$run_data" "$z3_root"
bash "$experiment/run-matrix.sh" "$runner_root" "$run_data" "$z3_root"
bash "$experiment/run.sh" "$runner_root" "$run_data" "$z3_root" judge reverted 1500 ''
```

生成脚本会在各 IR 旁写下完整 Sail 参数和版本。各运行的 `argv.txt`、`budgets.txt`、`linked.txt`、`measure.txt` 和 `raw.log` 位于数据盘 `runs/<运行名>/`。

## PMP 配置诊断

历史配置用 `sys_pmp_count=2`，但新生成的两个 IR 均在 `pmpCheck` 入口保留 `sys_pmp_count ∈ {0,16,64}` 的 Sail 类型约束。IR 映射到 `assume(false)` 后会丢弃到达 PMP 的路径。以相同配方运行原模型，确认这处限制两侧共有。试图同一次开启缓存写出和常驻 judge 被 CLI 拒绝，退出 1。额外做了抛出处过滤和无路径合并诊断，两个历史输入仍都未接纳。

补跑使用 [合法配置](pmp16-usable2.toml) 覆盖总数 16、可用数 2，保留历史两份输入和其余配置。路径合并保持开启，逐路径 600 秒，程序／外限 1500／1510 秒。通过脚本的 `SAIL_RECHECK_JUDGE_CONFIG` 选择本轮数据盘配置副本。配置旁的 `base-frozen.toml` 取自历史签收输入目录。

合法配置全符号补跑 1502.68 秒退出 124，最后快照已保存 1056 条路径，仍有 27 项排队，未进入常驻判定。定向补跑只收窄两份输入共同的前态，令 SATP 为 Bare、特权级为 User、`x1=0x80000040`，PMP 配置和其余输入字段继续由历史样本逐字段绑定。逐路径 600 秒、程序／外限 900／910 秒。两侧结果分别保存在 `reverted-judge-legal-directed`、`original-judge-legal-directed`。

```bash
judge_input_dir="$runner_root/agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/raw/lazy-pmp2-judge-20261117/inputs"
mkdir -p "$run_data/legal-pmp2"
cp "$judge_input_dir/base-frozen.toml" "$run_data/legal-pmp2/"
cp "$experiment"/pmp16-usable2*.toml "$run_data/legal-pmp2/"
SAIL_RECHECK_JUDGE_CONFIG="$run_data/legal-pmp2/pmp16-usable2.toml" \
  bash "$experiment/run.sh" "$runner_root" "$run_data" "$z3_root" judge reverted 1500 -legal-pmp2
for variant in reverted original; do
  SAIL_RECHECK_JUDGE_CONFIG="$run_data/legal-pmp2/pmp16-usable2-bare-user.toml" \
    bash "$experiment/run.sh" "$runner_root" "$run_data" "$z3_root" judge "$variant" 900 -legal-directed \
    --prestate x1=0x0000000080000040
done
```

所有本轮模型进程、Sail 与包装器已退出。8 次性能探针以 124 收尾，10 次定向样本检查以 0 收尾。9 次 judge 或诊断调用中，历史配置的缓存写出诊断以 1 退出，合法配置的全符号补跑以 124 退出，其余 7 次以 0 收尾。退出码 0 的原历史配方仍未接纳样本 1，签收依据为报告内容。
