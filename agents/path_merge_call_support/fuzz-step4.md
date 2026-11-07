# fuzz 第 4 步：并行生成与 DiffTest 闭环（2026-11-08）

生成提速与三方闭环均已实现。Sv39 STORE 的 2000 例验收中，每千个 mutant 的生成耗时由第 3 步的 981.225 秒降至 37.507 秒，约 **26.16 倍**；LOAD 为 43.944 秒，约 **22.05 倍**。同一初值的 300 个输入跨两个批次，在 `-T 1/32` 下的 `mutants.jsonl`、`judged.jsonl` 逐字节相同。

300 个 STORE mutant 已真实运行：**251 agree、49 原始不一致、49 被原有窄规则归类、0 新分歧、0 基础设施失败**。没有把这些结果认定为新缺陷。历史 14 个分歧的三方 cause 全部符合预期，窄规则命中 **14/14**；四场景各随机抽取 50 个正常 corpus entry，**200/200 agree**。最终 Rust 测试 **1138 通过、0 失败、6 项既有忽略**，原 1134 项没有退化。

只修改当前独立工作树；未做 Git 写操作，外部模型、重放代码和平台文件均只读。构建、临时文件、日志和 ELF 全部位于当前工作树。采用现有官方 Z3、ecfg4b 的 IR、配置、固定 S 态与指令；没有引入 U 态或反馈驱动接纳。

## A：先测量，再优化

96 个请求的基线测量：生成服务时间合计 58.882 秒，其中父输入绑定 0.906 秒、查询 55.985 秒、具体化 0.126 秒，其余约 1.864 秒。查询占 **95.1%**。独立动态库计时覆盖其中连续完整的 95 个请求：Z3 实际查询为 49.311 秒，对应 Rust 查询计时 51.486 秒，占 **95.8%**。不能把全部查询时间归给 Rust 约束构造。

基线共 6442 次查询，653 个随机 8 位偏好被拒绝，随后进入逐位极性选择。每次拒绝最多触发八次额外查询，说明主要浪费来自这些重试。阻断历史、约束构造及 JSON 等没有占据主要的独立墙钟时间；阻断式对 Z3 本身求解难度的影响未单独消融，不宣称它为零。

测量证据为 `output/fuzz-step4/profile-before-summary.json`、`native-solver-profile.json` 与对应原始 `stderr.log`。动态库只用于诊断，不用于正式性能结论。

| 候选，96 个请求 | 查询数 | 生成墙钟秒，单线程 | 结论 |
| --- | ---: | ---: | --- |
| 原实现，仅加计时 | 6442 | 58.916 | 查询为主要成本 |
| 使用现有 `define_const` 复用累计表达式 | 6442 | 56.551 | 单独收益约 4%，保留为复用手段 |
| 保持随机打散位，再探测固定桶 | 增加 | 未改善 | `fixed-*` 为诊断候选，不作为最终性能结论 |
| 相邻位组成桶，随机排列桶，证明固定桶后整组选择 | 3100 | 26.373 | 减少无效逐位查询，单次成本下降约 2.23 倍 |

固定桶并不直接采用任意求解模型的值：先查询当前条件下是否存在另一组取值，只有 UNSAT 才固定整组。部分可变的桶继续使用既有逐位极性选择。规范守卫、字段掩码、整解阻断、形态 A 的字段排重和完整具体化均保留。

`generation.rs` 把目标类固定分配到一个队列。主线程先按 mutant 编号预约批内目标和额度；相同目标类按编号处理其独立排重历史，不同目标可并行。线程内恢复并复用已有 `SolverMutator`；随机流仍由随机数初值、场景和编号派生。批次收齐后按编号写出，再更新调度。预约类空间耗尽会明确终止，不能悄悄换输入；本次正式批次没有发生耗尽。

| 场景与预算，初值 42，含 5% 对照 | 生成总秒 | 秒／千个 mutant | 相对第 3 步生成提速 | A/B 认证命中 | 同目标类字段／前态唯一 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Sv39 STORE，1000 | 33.432 | 33.432 | 29.35 倍 | 950/950 | 100% / 100% |
| Sv39 STORE，2000 | 75.014 | 37.507 | 26.16 倍 | 1900/1900 | 100% / 100% |
| Sv39 LOAD，2000 | 87.887 | 43.944 | 22.05 倍 | 1900/1900 | 100% / 100% |

STORE 的 1000 例 A/B 为 482/468，2000 例为 970/930；LOAD 为 953/947；所有对照也接纳。LOAD 的 2000 个输入共命中 721/728 类；本次只测初值 42，不将单次值冒充三个初值的平均。STORE 的 1000 个输入命中 372/380 类，2000 个输入命中 380/380 类。完整目录见 `coverage.json`。这些是单次共享主机测量，批量 isarch 均为 `-T 32`、最多四个同时运行；`-T 1` 仅用于用户要求的确定性对照。

性能表的生成不包含 corpus 认证、额外逐 mutant 认证或硬件执行。STORE 1000/2000 例的全量认证审计另花 62.745/123.595 秒；LOAD 为 157.646 秒，不能把认证审计计为普通生成成本。第 3 步参考值为 STORE 981.225、LOAD 969.049 秒／千个。

确定性证据有两组：96 个纯引导输入的三个 JSONL 逐字节相同；300 个含 5% 对照的输入跨两个批次，`mutants.jsonl`（10,089,055 字节）与 `judged.jsonl`（19,374,657 字节）逐字节相同。300 个输入的一侧还实际连接了 DiffTest，认证与硬件执行不改变生成输入或判断结果。仅计时文件不参与比较，没有删除数据字段或计算文件哈希。

## B：模块与 worker 接口

| 文件 | 职责 |
| --- | --- |
| `src/isarch/fuzz/generation.rs` | 按目标类分配的有界生成队列、结果排序 |
| `isla-lib/src/executor/sample_mutation.rs` | 累计表达式复用、取值桶、固定桶证明与计时 |
| `tools/fuzz/paging_worker.py` | 认证样本到现有 Python 重放 API 的薄入口、清理独立进程组 |
| `src/isarch/fuzz/difftest.rs` | `Executor`、有界队列、8 路 worker、超时、取消与子进程回收 |
| `src/isarch/fuzz/oracle.rs` | 三方比较、规则编号、保留原始差异 |
| `campaign.rs`、`options.rs`、`isarch_main.rs` | CLI、先认证后提交、批次汇总和 findings |
| `tools/fuzz/run_campaign.py`、`step4_validate.py` | 单场景复现与独立验收驱动 |

worker 每次处理一个输入，接受以下参数：

```text
--input <samples v1 JSONL>
--sample-id <可选编号；不指定时文件必须只有一条>
--profile <平台描述 JSON>
--lock <平台锁 JSON>
--files <emu/NEMU 等既有工具路径 JSON>
--observer <独立 NEMU 观察器 SO>
--output <本工作树内的目录>
--timeout <emu 秒数，默认 120，上限 600>
--compiler <可选编译器>
```

通过 `sys.path` 导入 `DIFFTEST_XIANGSHAN_DIR` 指向的既有 `paging_replay.py` 与 `paging_fuzz.py`。直接调用 `platform_case`、`load_decoder`、`build_case`、`run_probe`、`observe_run` 与 `MismatchTable`，没有复制分页或过滤规则逻辑。解码器由 `PT_DECODE_DIR` 指定。默认来源与本轮指定的 replay-p0、isla-enumerate 工作树一致；它们保持只读。

输出 `result.json` 保留原 `run_probe` 字段，并增加顶层 `isla_cause`、`xs_cause`、`nemu_cause`、`isla_consistent_side`、`observation`、`phase`、`mismatch{filtered,known_rule,group_key}`。原有 `bucket`、`reason`、`elf_sha256` 等字段继续保留。基础设施失败保留为空 cause，不编造三方观察；入口发生异常时先写错误记录，再继续抛错并非零退出。

实际指定的 ecfg4b `profile.lock.json` 仍是 **schema_version=1**，与任务背景所述的版本 2 不同。现有库支持两版；本轮使用原文件，记录实际版本，未修改它或另造替代锁。只核对平台描述与锁的关联，isarch 哈希仅作来源记录，样本有效性依靠当前模型语义认证。没有批量重算工具文件身份。

Rust 每个 worker 线程调用一个 Python 进程；同时在途默认 8 个，上限 12，任务队列容量为两倍 worker 数。单例 emu 超时默认 120 秒，Python 外限另加 30 秒用于构建和清理。结果按输入编号收齐，汇总只在批次边界更新。

Rust 处理 SIGINT/SIGTERM 后停止排队执行，结束 Python、emu 独立会话及其后代，回收已收养的子进程。Python 使用子进程收养机制，在 `finally` 中终止 emu 会话并等待 native NEMU。Rust 还给 Python 设置父进程退出信号，避免执行线程或主进程意外消失后 Python 长期残留。超时不重试、不换输入，不把基础设施失败记成模型分歧。

`Oracle` 保留 Isla/NEMU/XiangShan 三方结果。现有 Python 窄规则 `xs_leaf_ppn_af_over_permission_pf` 对应编号 **R-XS-001**，统计每次命中；不修改、放宽规则，也不按整类过滤。findings 按目标类、不同字段与阶段分组，输入和原始结果都保留。

## 验收与 findings

| 项目 | 结果 | 证据 |
| --- | --- | --- |
| 1/32 线程确定性 | 96 例和跨批次 300 例通过 | `buckets-determinism.json`、`determinism-300.json` |
| 引导命中与排重 | STORE 1900/1900、LOAD 1900/1900，唯一比例均 100% | `generation-acceptance.json` |
| 已知 14 例经 worker 重放 | 14/14 cause 符合预期，14/14 窄规则命中 | `worker-validation-final/` |
| 四场景各 50 个正常 corpus entry | 200/200 agree | `worker-validation-final/` |
| 真实 STORE 闭环，300 例 | 251 一致，49 原始分歧，49 规则命中，0 新分歧 | `real-campaign-300/fuzz/findings-summary.json` |
| Rust 全工作区 | 1138 通过、0 失败、6 项既有忽略 | `test-workspace-final.log` |
| 原有 Python 测试 | 127/127 | `python-existing-tests-final.log` |
| 新 Python 测试 | 6/6 | `python-new-tests-final.log` |
| 取消与超时后的进程 | 独立会话及 fork 后代均无残留 | `process-timeout-tests-final.log`、`real-cleanup-verification-final.json` |
| Make MRET 冒烟 | 退出 0，4 条用例，保留既有 Poison 提示 | `mret-final/` |

已知分歧的 cause 顺序为 **Isla / XiangShan / NEMU**：

| 场景 | 数量 | cause 三元组 | R-XS-001 |
| --- | ---: | --- | ---: |
| sv39-load | 6 | 13 / 5 / 13 | 6 |
| sv39-store | 4 | 15 / 7 / 15 | 4 |
| sv48-load | 3 | 13 / 5 / 13 | 3 |
| sv48-store | 1 | 15 / 7 / 15 | 1 |

独立重放结束后扫描了本次输出目录对应的 Python、emu 与 native NEMU 进程，`worker-validation-final/remaining-processes.json` 为 `[]`。Rust 单元测试还用真实超时与 SIGTERM 取消分别验证独立会话清理；Python 测试验证 emu 会话和 fork 后代均被回收。另以真实 emu 做 1 毫秒超时与执行中取消，两次检查均无遗留进程；创建子进程到登记之间的取消竞态已用失败测试复现并修复。最后重跑全部 214 例，仍为 14/14 窄规则命中与 200/200 agree。最终二进制另跑 8 例硬件冒烟，收尾进程检查也为空。

上述证据均位于当前工作树的 `output/fuzz-step4/`，总验收记录为 `acceptance.json`（`complete=true`）。原始首次 Python 测试有 6 个错误，原因是测试默认向只读 replay-p0 写临时文件；使用既有 `PAGING_TEST_OUTPUT_DIR` 后 127 项全部通过，没有改测试或跳过条目。首次独立目录 Make 冒烟漏建 `scripts` 链接，启动失败；补齐目录布局后另建 `mret-final/` 重跑，原失败日志保留。

真实 campaign 使用初值 42，285 个 A/B 加 15 个记录池对照，所有 300 个输入都先通过认证档，再送到 emu。总进程约 372.7 秒，生成 11.552 秒、快档 1.378 秒、认证 17.646 秒、硬件阶段 284.398 秒。49 条原始分歧全部由 R-XS-001 命中，新分歧为零，因此没有需要追加的未知三方 cause 列表。完整输入在 `mutants.jsonl`，认证样本在 `certified.jsonl`，每例 ELF 与三方日志在 `difftest/input-编号/`。

## 复现

从当前工作树根目录运行，输出目录使用新名字。构建与临时文件均留在当前工作树。

```sh
mkdir -p output/fuzz-step4/tmp
export TMPDIR="$PWD/output/fuzz-step4/tmp"
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
export PT_DECODE_DIR="$(realpath ../isla-enumerate/agents/path_merge_call_support/pt_decode)"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
python3 -m unittest discover -s tools/fuzz/tests
```

并行生成及跨批次确定性：两个命令顺序执行，比较两个完整文件，不计算哈希。

```sh
python3 tools/fuzz/run_campaign.py --scenario sv39-store --budget 300 \
  --random-seed 42 --threads 1 --output output/fuzz-step4/repro-t1
python3 tools/fuzz/run_campaign.py --scenario sv39-store --budget 300 \
  --random-seed 42 --threads 32 --output output/fuzz-step4/repro-t32
cmp output/fuzz-step4/repro-t1/fuzz/mutants.jsonl output/fuzz-step4/repro-t32/fuzz/mutants.jsonl
cmp output/fuzz-step4/repro-t1/fuzz/judged.jsonl output/fuzz-step4/repro-t32/fuzz/judged.jsonl
```

真实闭环：

```sh
python3 tools/fuzz/run_campaign.py --scenario sv39-store --budget 300 \
  --random-seed 42 --threads 32 --executor difftest \
  --output output/fuzz-step4/repro-difftest
```

独立 worker 验收复用第 2 步已有的回放样本，先在当前模型做完整认证，再重放；不要与另一个 8 路真实 campaign 同时运行。

```sh
python3 tools/fuzz/step4_validate.py prepare --output output/fuzz-step4/repro-worker
python3 tools/fuzz/step4_validate.py certify --output output/fuzz-step4/repro-worker --isarch-processes 4
python3 tools/fuzz/step4_validate.py replay --output output/fuzz-step4/repro-worker
PAGING_TEST_OUTPUT_DIR="$PWD/output/fuzz-step4/python-test-output" \
  python3 -m unittest discover -s ../replay-p0/difftest-xiangshan/tests
```

每个 campaign 的 `done.json` 保存完整 argv、退出码和时间；`timing.json` 分开列生成、快档、认证和硬件阶段。输入语义及结果按 JSON 字段比较，不以二进制哈希变化拒绝已有输入。

## 未做与遗留

- 形态 B 仍只在同一完成路径内选邻类，没有跨 DAG 守卫对齐。
- 没有符号前态 U 态、反馈驱动接纳、动态扩充类目录或 DAG 纯求值器。
- 类内取值变化不自动加入 corpus；本批没有新增 corpus entry。
- 原探索的 `partial/errors=5/7` 和退出 1 继续保留；没有重新证明旧排除域，也没有把退出 1 改写成整体探索完成。
- 生成表达式共享使用原 `define_const` 接口；长时间超大预算的符号表增长尚未单独测量。本轮预算上限为 2000 个 mutant。
- 目前只登记了 R-XS-001；将来增加现有 Python 规则时必须明确登记编号，未知规则直接报错。
