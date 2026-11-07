# fuzz M0 常驻 judge 原型（2026-11-07–08）

## 目标、范围和步骤

基于 `78b04e3`，只在本独立工作树实现隐藏参数。每个场景探索一次，保存每条完成路径的检查点、SamplePath、合并记录和路径号。工作线程各建 Z3 Context，从检查点恢复负责的路径；对全部输入复用现有 judge。保持 J1 和 `--check-samples-judge` 行为。

热点文件：`src/isarch/exec.rs`、`src/isarch/samples.rs`、`src/isarch_main.rs`、`src/opts.rs`、新增 `src/isarch/resident.rs` 和 `isla-lib/src/executor/samples.rs`。

先为只判定入口写失败测试，再实现，运行格式化、release 构建和全工作区测试。实测 Sv39 STORE 的 380 个 corpus entry、1000 个变异体及三个负对照。对照只读既有 JSON，不额外计算哈希。

首要未决问题：恢复后求解器是否保持原路径语义；发现差异须定位。另测探索耗时、保存后 RSS、各路径恢复耗时、逐输入墙钟与 CPU 时间（32/1 线程）。实现与验证结果分开登记。

## 当前状态

实现完成。红测因缺少 `judge_only` 编译失败；实现后新增测试通过。`cargo fmt --check`、`cargo build --release --offline -j 8`、`cargo test --workspace --offline -j 8` 通过：1109 通过、0 失败、6 项既有忽略；原 1108 项无退化。`make solve-MRET` 退出 0，产出 4 条用例，保留既有 partial／1 条未完成路径。32/1 线程的完整场景对照均已通过。最终 release 构建、全工作区 1109 项测试和隐藏参数帮助检查也已通过；帮助修正后另跑 64 线程冒烟：一个正例完整字段一致，三个负对照均零接纳，耗时 13.649 秒。

## 修改文件

- 核心：`isla-lib/src/executor/samples.rs` 新增只判定入口与原型输入加载；`src/isarch/exec.rs` 保存路径并调用常驻流程；新增 `src/isarch/resident.rs` 实现线程内恢复、逐输入判定和计时。
- 参数与接线：`src/isarch/samples.rs`、`src/isarch/mod.rs`、`src/isarch_main.rs`、`src/opts.rs`。
- 依赖：`Cargo.toml`、`Cargo.lock` 显式加入已在工作区使用的 libc，用于线程 CPU 时钟。
- 复现：新增 `agents/path_merge_call_support/fuzz_m0_validate.py`。
- 文档与状态：本文、`agents/findings.md`、`agents/overview.md`、`agents/path_merge_call_support/status.md`、`specs/TODOs.md`、`docs/RESULTS.md`。

## 实现与用法

在 `solve-state` 之前添加两个隐藏参数：

```sh
--judge-resident mutants.jsonl --judge-resident-out judged.jsonl
```

两项必须同时指定，输入输出不得相同，也不得与 J1 选项一起启用。输入沿用 samples v1，可省略 `post_registers`、`post_memory`、`result`、`ret_val`；即使提供这些期望字段，常驻入口也忽略它们。前态字段仍必须完整。

完成路径的收集发生在有限域代表值钉选、编码筛选和输出过滤之前。保存检查点、SamplePath、合并记录和路径号，随后继续原 J1 的正常探索和收尾。探索结束后按路径号排序并分派；每个工作线程建立自己的 Context，每条负责的路径只从检查点恢复一次。以后逐个输入尝试全部路径，复用 `SamplePath::judge()`，包括回滚后的后态唯一性检查。

输出保持 `JudgedSample` schema_version=1，内嵌完整 samples v1。零条路径接纳时没有输出行；多于一条路径接纳时报错并终止，没有 fallback。原 J1 加载和 `check_path_with_judge()` 逻辑保持不变。

两个帮助入口均隐藏原型参数；`src/opts.rs` 仅为共享解析器的帮助显示补齐过滤，不改参数解析或求解。

stderr 记录四组 JSON：`JUDGE_RESIDENT_SAVED`（探索、保存后 RSS 与此前峰值）、`JUDGE_RESIDENT_RESTORED`（每路径恢复）、`JUDGE_RESIDENT_MEASUREMENTS`（逐输入墙钟／CPU）、`JUDGE_RESIDENT_REPORT`（接纳计数）。最后一项只使用 `accepted_paths`，不表示核对了输入期望；原报告的 consistent/inconsistent 计数均为 0。

逐输入墙钟从派发到全部线程返回，包含线程通信、判定与输出；CPU 为各工作线程的 `CLOCK_THREAD_CPUTIME_ID` 增量之和，不包含等待派发的时间。恢复计时只包围 `Solver::from_checkpoint()`；恢复阶段总墙钟另包含 Context 创建和线程启动。探索计时覆盖 `start_multi` 及 ExecuteAs 续执行，不含 IR 加载和初始前态准备；进程总墙钟单独记录。

## 复现

从本工作树根目录执行。已有 `t32`、`t1` 目录拒绝覆盖，复跑应更换脚本中的 OUT。来源数据和二进制安装只读使用。

```sh
mkdir -p output/fuzz-m0/tmp
export TMPDIR="$PWD/output/fuzz-m0/tmp"
export RUSTFLAGS="-L native=$HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
cargo fmt --check
cargo build --release --offline -j 8
cargo test --workspace --offline -j 8
python3 agents/path_merge_call_support/fuzz_m0_validate.py prepare
python3 agents/path_merge_call_support/fuzz_m0_validate.py run --threads 32
python3 agents/path_merge_call_support/fuzz_m0_validate.py verify --threads 32
python3 agents/path_merge_call_support/fuzz_m0_validate.py run --threads 1
python3 agents/path_merge_call_support/fuzz_m0_validate.py verify --threads 1
make -f scripts/run.mk -o build-isarch solve-MRET THREADS=64 \
  IR_FILE=../replay-p0/output/ecfg4b/rv64d.ir \
  SOLVE_CONFIG=../replay-p0/output/ecfg4b/config-xs.toml TASTIC=default
```

验证脚本读取 `../replay-p0/output/ecfg4b/sv39-store-j1/done.json` 的 argv，仅替换程序、线程数、输出和检查入口。IR、config-xs.toml、指令、前态、`--path-merging`、`--smt-timeout 5 --timeout 890` 保持不变。没有加载历史观察器；外限 1200 秒涵盖探索与逐输入判定，不延长原探索预算。

## 已知限制

- 这是一次装入 JSONL 的原型，没有变异器、corpus 调度、覆盖增长或正式 fuzz 子命令；只验证路径常驻判定。
- 每个输入串行派发给全部工作线程，等待全部路径判定后才派发下一个；未做流水线或吞吐优化。工作线程最多为路径数，32 线程配置下实际判定线程为 26。
- 输入和路径全部驻留内存；没有持久化检查点或跨进程复用。计时、RSS 依赖 Linux。
- 保留 samples v1 的初始内存语义与写后读限制；不恢复合并主迹的精确访存顺序。守卫记录编号不跨进程稳定，只比较规范向量。
- 每次启动仍需探索一次；原型按单场景运行，不保证多个 clause／分片组成的会话有全局唯一路径。
- 现有 partial／排除域终止单列保留；本轮不重做旧观察器的逐查询排除证明。


## 完整场景验证与测量

**限定结论：M0 核心流程可行。本批 32/1 线程均保存并恢复 26 条完成路径，380 个 corpus entry 与 1000 个变异体各恰好被一条路径接纳，完整输出差异均为 0。未发现检查点恢复后的求解器语义变化或 bind 错误；这是这批输入的证据，不是对全部可能输入的等价证明。**

输入副本删除全部四个期望字段，见 [inputs.jsonl](../../output/fuzz-m0/inputs.jsonl)。corpus 来自 ecfg4b 原始 samples v1，变异体来自指定已补 fcsr 的 classified 文件；来源只读。为避免两组 sample_id 冲突，将输入顺次编号，并保存 [input-map.json](../../output/fuzz-m0/input-map.json)。比较时恢复原 sample_id，只去掉进程内编号相关的 guard_order、guard_assignment；其余顶层字段和 sample 全部字段直接比较 JSON 对象，包括规范向量、唯一性标记、result、前后寄存器、前后内存、isa_state 和 ret_val。

corpus 真值为 `../isla-judge/output/judge/judge/sv39-store/judged.jsonl`；变异体真值为该树 `output/fuzz-p1b-classes/mutants/judge/sv39-store/judged.jsonl`，路径号与规范向量另与 ledger.json 核对。两批均输出 1380 行；[32 线程差异清单](../../output/fuzz-m0/t32/differences.json)和[单线程差异清单](../../output/fuzz-m0/t1/differences.json)均为空。

三个负对照均从成功 corpus entry 62 构造，两种线程配置下接纳路径数都为 0：

| 输入编号 | 修改 | 32 线程 | 1 线程 |
| --- | --- | ---: | ---: |
| 1380 | 仅翻转 pre_registers.x1 最低位 | 0 | 0 |
| 1381 | 删除实际读取地址 0x80100800 的一个字节 | 0 | 0 |
| 1382 | 根 PTE 设为 0x08000001，指向排除区 0x20000000；补齐新读取地址 0x20000800 的下级 PTE 字节 | 0 | 0 |

原始退出码两批均为 1，执行摘要都是 partial／errors=5；执行超时、SMT 超时、终值查询超时、未完成路径、待处理批次均为 0。保留原排除域执行终止，没有重做历史逐查询排除证明，也没有把原始状态改成 finished。

下表为单次实测。RSS 包含 IR、输入、执行器及求解器，不是路径缓存的独立大小。32 线程批次的前段与第一次 cargo test 编译／测试有重叠；单线程批次与其顺序运行，两次性能批次没有互相重叠。因此不把此表当成隔离环境中的稳定加速比。

| 指标 | -T 32（判定线程 26） | -T 1 |
| --- | ---: | ---: |
| 首次探索（秒） | 13.156 | 19.808 |
| 保存后 RSS（MiB） | 883.363 | 767.180 |
| 保存时累计 RSS 峰值（MiB） | 934.859 | 800.344 |
| 全过程 RSS 峰值（MiB） | 1358.547 | 859.098 |
| 全部路径恢复墙钟（秒） | 0.081 | 0.117 |
| 每路径恢复平均墙钟（毫秒） | 11.864 | 4.347 |
| 每变异体平均墙钟（毫秒） | 234.141 | 322.059 |
| 每变异体墙钟中位数（毫秒） | 159.041 | 233.298 |
| 每变异体墙钟 P95（毫秒） | 378.532 | 483.756 |
| 每变异体平均 CPU（毫秒） | 677.447 | 310.402 |
| 1000 变异体墙钟合计（秒） | 234.141 | 322.059 |
| 1000 变异体 CPU 合计（秒） | 677.447 | 310.402 |
| 全部 1383 输入判定墙钟（秒） | 345.088 | 456.943 |
| 全部 1383 输入判定 CPU（秒） | 988.230 | 443.929 |
| 进程总墙钟（秒） | 362.100 | 480.488 |

既有“每批重新探索”的 judge：380 个 corpus entry 一批 89.301 秒，1000 个变异体一批 266.366 秒，两批相加 355.667 秒。常驻的 32 线程变异体纯判定为 234.141 秒，另需探索 13.156 秒与恢复 0.081 秒，并且这组变异体在同进程 380 个 corpus entry 之后判定，已有求解器使用历史。纯判定比历史单批少约 12.1%，但不能把它解释为同负载的纯缓存加速。

把 corpus、变异体和负对照一起计入，本轮 32 线程进程总墙钟 362.100 秒，未比历史两个批次之和明显缩短。单线程变异体纯判定 322.059 秒，CPU 310.402 秒；32 线程为 234.141 秒、CPU 677.447 秒。此原型证明了路径可以复用，没有证明显著吞吐收益。

每路径恢复的完整墙钟／CPU 数字在 [32 线程 metrics.json](../../output/fuzz-m0/t32/metrics.json)和[单线程 metrics.json](../../output/fuzz-m0/t1/metrics.json)；两份文件也保存每个输入的墙钟／CPU。汇总见 [32 线程 summary.json](../../output/fuzz-m0/t32/summary.json)和[单线程 summary.json](../../output/fuzz-m0/t1/summary.json)。各自 done.json 保存实际 argv、cwd、总耗时和退出码，time.txt 保存进程级 CPU 与 RSS 峰值。

| path_signature | -T 32 恢复墙钟（毫秒） | -T 1 恢复墙钟（毫秒） |
| --- | ---: | ---: |
| 1515758119081714249 | 12.298 | 8.130 |
| 2752876776965356570 | 10.274 | 1.221 |
| 5388342026326964849 | 2.305 | 0.808 |
| 5861799980873429453 | 4.335 | 1.141 |
| 6417597896559680344 | 14.361 | 7.034 |
| 6672117053918287038 | 6.645 | 2.764 |
| 7045064852189834985 | 21.307 | 6.391 |
| 7143617572799853392 | 15.560 | 3.864 |
| 7359989186059684407 | 15.695 | 6.572 |
| 7683191734168398840 | 18.702 | 6.322 |
| 7806394602894184644 | 7.795 | 2.668 |
| 9549010931531468040 | 19.647 | 5.598 |
| 9781422093275644871 | 5.940 | 2.142 |
| 9872932927871959034 | 8.711 | 3.424 |
| 9915689945045587861 | 4.744 | 1.377 |
| 10425144959524720486 | 7.037 | 1.195 |
| 10451216379200822465 | 3.318 | 0.638 |
| 12587046013427828726 | 20.424 | 9.616 |
| 13200188859556902643 | 10.954 | 2.999 |
| 13437207682752757463 | 16.695 | 10.140 |
| 13737262353197203368 | 15.312 | 5.686 |
| 14131905759038089610 | 17.646 | 6.551 |
| 14651400866703406955 | 10.620 | 3.581 |
| 14946538549964930339 | 15.155 | 6.905 |
| 16077645086038119269 | 9.271 | 3.003 |
| 16268951735401421547 | 13.715 | 3.246 |

完整场景使用初次 release 构建（build.log）；之后仅修改共享 `--help` 的文字过滤（src/opts.rs），未改参数解析、路径保存、恢复或 judge。最终构建与帮助检查另留 build-final.log、test-final.log、help-check.json，不能将帮助修正说成新的求解器实验。

最终二进制的 [64 线程冒烟](../../output/fuzz-m0/final-smoke/verification.json)复用输入 0、1380、1381、1382；一条正例与完整批次的输出逐字段一致，三个负对照仍零接纳。原始退出 1、partial／errors=5 保留。最终构建通过、全工作区测试 1109 通过／0 失败／6 项既有忽略，格式检查与帮助隐藏检查通过。所有产物在本工作树；没有 git 写操作、其他工作树修改或额外哈希核对。


## 后续：第 1 步快档（2026-11-08）

M0 的上述性能结果保留为原型历史。[fuzz-step1.md](fuzz-step1.md) 记录随后增加的分阶段计时、静态证明与独立快档：同一 380 个 corpus entry＋1000 个 mutant 在 1／32 线程下与认证档逐字段零差异，三个负对照零接纳，整批纯判定墙钟提速 8.30／65.75 倍；完整认证流程仍可用。
