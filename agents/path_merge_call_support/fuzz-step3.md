# fuzz 第 3 步：路径引导变异与 DAG 导出（2026-11-08）

**第 3 步限定验收完成。** 六组各 2000 个 mutant 中，5791 个 A、5609 个 B 经认证后全部命中目标类；同目标类的改动字段取值组合和完整前态唯一比例均为 100%。两场景各重跑初值 1，`mutants.jsonl`、`judged.jsonl` 等六个文件逐字节相同。工作区测试 1134 通过、0 失败、6 项既有忽略。普通 campaign 完整循环为 STORE **993.1 秒/千个**、LOAD **982.0 秒/千个**，当前瓶颈是串行求解器生成。

基线为 `4828d8c` 加本轮未提交改动，沿用 ecfg4b 的 IR、配置、指令及前态，链接既有官方 Z3。完整机器结果为 `output/fuzz-step3/final/acceptance.json`（`complete=true`）。没有 Git 写操作，没有修改其他工作树或 Python 文件，没有连接 emu。形态 B 当前限定同一完成路径，编码空间对照复用记录池，范围见文末。

## 模块与设计

| 文件 | 职责 |
| --- | --- |
| `isla-lib/src/executor/sample_mutation.rs` | 规范守卫约束、按位依赖、父输入绑定、字段取值偏好、排重和具体化 |
| `isla-lib/src/executor/sample_mutation_tests.rs` | 类内多样性、未使用寄存器固定、邻类无关位固定、有限空间耗尽及 DAG 顺序测试 |
| `isla-lib/src/executor/sample_dag.rs` | 原始 `Def` 序列、类型、守卫与状态引用的 JSON 导出 |
| `merge_components.rs`、`merge_enumeration.rs`、`merge_record.rs` | 只调整已有按位依赖分析的可见性，供变异器复用 |
| `src/isarch/fuzz/mutator.rs` | 实现 `Mutator`，持有一次恢复的求解器，生成完整前态并清空期望后态 |
| `src/isarch/fuzz/campaign.rs` | 类轮转、邻类排序、批次、快档、认证档、新类候选及计时 |
| `src/isarch/fuzz/dag.rs` | 每路径落盘、重读与 manifest 汇总 |
| `classifier.rs`、`traits.rs`、`options.rs`、`corpus.rs`、`mod.rs` | 复用第 2 步的执行队列、类身份及会话，新增 campaign 参数 |
| `src/isarch_main.rs`、`README.md`、`specs/isarch-cli.md` | 中文帮助和用法 |
| `tools/fuzz/step3-experiments.sh`、`step3-report.sh`、`step3-runner-test.sh` | 调用既有 Python 算子、批量验收、逐字段统计及驱动取消测试；没有新增或修改 Python 文件 |

形态 A 固定父 corpus entry 的规范守卫向量，随机排列字段及其 8 位切片，选出可换取值的切片。其他活动输入字段、选中字段的其他位均固定为父值。只从访存输入及影响守卫、地址、结果、被修改后态的前态字段中选择；不靠改写未使用的浮点、向量或通用寄存器制造多样性。约束同时要求选中字段不同于父值和该目标类先前所有 mutant 的对应字段。若某个切片没有其他取值，就检查排列中的下一个切片；所有字段空间用尽会显式报告耗尽，不给默认输入。

形态 B 只比较同一条完成路径上的规范向量，按汉明距离、目标命中次数、稳定目录顺序排序。批次内部用预约计数避免集中选一个目标，实际命中计数在批次结束后提交。达到本轮每类额度的目标不再选取。优先只开放差异守卫与路径断言关联的位，尽量保住父值；若不可满足，再加入其他守卫的关联闭包。例如只改变 x 的分支、同时保持 `x == y`，也必须允许 y 改变。闭包以外的输入位始终固定。父类未活动的读取没有父输入值，目标类需要它时由求解器生成。新地址和新读取内容由同一个求解模型经原 `SamplePath::materialize` 生成，不搬用父样本的旧地址或后态。

两种形态都用既有 `guard_order` 和父链 `context`，固定的是 `active && condition`，不是未经规范化的原始守卫。随机性继续使用第 2 步由随机数初值、场景、mutant 编号派生的独立 ChaCha8 随机流。位顺序与取值偏好显式随机化；先尝试整组 8 位偏好，不可满足时逐位选择可满足的极性。最终固定所有活动输入的自由位，避免依赖 Z3 的模型偏好。每类保留已生成的有关输入解，构造整解阻断式；形态 A 另有更严格的字段排重。

普通 campaign 在 corpus 认证后逐批执行生成、快档、候选认证、提交调度。只有出现初始目录以外的新类，才作为新增覆盖候选进行认证并写入 `corpus-added.jsonl`；反馈接口只观察，不调用分数或新颖性来做决策。验收开关 `--fuzz-certify-all` 对所有接纳的 mutant 再跑认证档，要求完整 judged JSON 与快档逐字段相同。A/B 的实际类必须等于目标类，否则直接 panic。

默认 5% 对照从 replay-log 的 M1/M2/M5 记录池独立随机抽样，统一在 A/B 阶段结束后生成，因此 A 的排重历史覆盖此前全部 mutant。2000 个输入时是先 1900 个 A/B，再 100 个对照。字节改动、页面复制、新读取范围和 STORE 初值规则全部复用第 2 步，不重新实现 Python 页表预测。记录保留原算子、`control_source_sample_id` 和当前 mutant 编号。对照池抽样允许重复；A/B 保持显式排重。完全不使用对照池时设 `--fuzz-control-percent 0`。

## 产物与元数据

继续输出 samples v1 的 `mutants.jsonl`、judged v1 的 `judged.jsonl`、完整 samples v1 的 `classified.jsonl`，以及第 2 步同格式的 coverage、transitions、statistics、ledger 和 observations。框架元数据放在 `mutations.jsonl`，不修改样本结构。

每条 A/B 记录有 `operator`、`form`、父 corpus entry、`target_identity`、`actual_identity`、`actual_certified` 与 `changes`。类身份仍是场景配置 id、路径签名、规范守卫向量。`changes` 记录逻辑字段名、前后具体值和开放位，`read.N` 对应 DAG 的访存序号。它记录求解器输入字段的差异；地址随字段改变时，具体地址见 mutant 的内存和 DAG 地址表达式。对照保留既有 `address`、`old_value`、`new_value`、位号或 PPN 等记录；对照没有事先指定的目标类。

新增 `certified.jsonl`、`corpus-added.jsonl`、`control-input-audit.json`、`dag/` 和 `dag-manifest.json`。计时除原字段外，包含生成、快档、额外认证、campaign 主体和含正式报表落盘的完整循环。DAG 格式与自由符号限制见 [导出说明](fuzz-dag-export.md)。

## 验证方法与实施记录

最终代码 `cargo test --workspace --offline -j 8` 为 **1134 通过、0 失败、6 项既有忽略**，保留原 1128 项，新增 6 项。`make solve-MRET THREADS=32` 退出 0、4 条用例，保留原 `partial/unfinished-paths=1`。DAG 当前路径索引与落盘重读一致：STORE 为 26 路径、1373 守卫、12095 个定义；LOAD 为 26 路径、1355 守卫、12033 个定义。12 个正式批次的独立重读、定义引用拓扑检查全部通过，共 312 条路径、16368 个守卫。

已完成的六组正式批次共 12000 个输入，其中 A 为 **5791** 个、B 为 **5609** 个，均经认证命中目标类；600 个对照也全部接纳。A、B 各自及合计的同目标类改动字段取值组合唯一比例、完整前态唯一比例均为 **100%**，六次的平均与范围均为 100%。含允许重复的对照后，每组规范化前态有 1998–1999 个不同输入。六组引导及六组 Python 对照的 24000 个分类样本均通过现有 Python samples v1 与标准分页解码。功能证据为 `final/functional-acceptance.json`；它的 `complete=false` 仅表示该记录不包含独立的确定性、速度阶段，最终 `acceptance.json` 已全部完成。

| 场景 | 引导实际类数，三次 | 引导平均／范围 | Python 实际类数，三次 | Python 平均／范围 | 每千个 mutant：引导／Python |
| --- | --- | --- | --- | --- | --- |
| sv39-store | 380、380、380 | 380／380–380 | 377、380、377 | 378／377–380 | 190／189 |
| sv39-load | 723、722、723 | 722.667／722–723 | 665、676、673 | 671.333／665–676 | 361.333／335.667 |

每千个 mutant 的范围分别为：STORE 引导 190–190、Python 188.5–190；LOAD 引导 361–361.5、Python 332.5–338。初始 corpus 覆盖不计入这些数字。两场景当前模型均保留原探索退出 1、`partial/errors=5`，未重做既有排除域的逐查询证明。

| 场景 | 初值 | A 命中／总数 | B 命中／总数 | 对照数 | A/B 字段取值与前态唯一比例 |
| --- | ---: | ---: | ---: | ---: | ---: |
| sv39-store | 1 | 958/958 | 942/942 | 100 | 100% |
| sv39-store | 42 | 970/970 | 930/930 | 100 | 100% |
| sv39-store | 2026 | 962/962 | 938/938 | 100 | 100% |
| sv39-load | 1 | 976/976 | 924/924 | 100 | 100% |
| sv39-load | 42 | 953/953 | 947/947 | 100 | 100% |
| sv39-load | 2026 | 972/972 | 928/928 | 100 | 100% |

**确定性通过。** STORE、LOAD 各以初值 1 独立重跑 2000 个输入，`mutants.jsonl`、`judged.jsonl`、`mutations.jsonl`、`statistics.json`、`coverage.json`、`transitions.json` 共 12 个文件逐字节相同。只比较这些不含耗时的接口文件，没有删除其中字段，没有计算哈希。普通速度批次不做额外逐例认证，其 `mutants.jsonl`、`judged.jsonl` 也与认证批次逐字节一致。

| 普通模式，秒/千个 mutant | STORE | LOAD |
| --- | ---: | ---: |
| 完整循环，含正式产物落盘 | 993.134 | 982.049 |
| 生成 | 981.225 | 969.049 |
| 快档判定 | 4.973 | 4.906 |
| 整个进程，含探索、DAG、恢复及 corpus 认证 | 1021.774 | 1026.310 |

表为各场景单次 2000 个输入实测，`-T 32`，与其他验收／复验批次共享最多 4 个锁位；不是隔离主机的性能上限。完整循环从 corpus 初始认证结束后计时，包含生成、判定、反馈报表与输入／输出落盘，不含一次性启动阶段。普通模式新增 corpus 条目和额外认证次数均为 0，符合本轮类目录完整、反馈不接决策的范围。生成目前串行，`-T` 用于探索和两档判定；没有宣称整体吞吐较随机翻转更快，也未将快档耗时当作整个 campaign 耗时。

**最终源码验证通过。** 新增关联守卫失败测试复现 `x` 分支改变、`x == y` 保持时只固定 y 会错误报告耗尽；修复后及原变异测试全部通过。六个正式批次的第一次关联投影均能求解，`solver_attempts=1900`、`exhausted_requests=0`；新增放宽候选不改变这些已生成输入。最终二进制另以 `-T 32` 完成 32 个输入全量认证冒烟，全部命中目标，见 `output/fuzz-step3/final-smoke/`。最终全工作区测试、格式检查及差异空白检查通过。

先增加缺失接口的失败测试，再实现变异与导出；先增加 Scheduler 和邻类距离的失败测试，再接 campaign。首轮批量观察发现形态 A 会选中未使用寄存器，主动停止，先加固定未使用寄存器的失败测试，再收紧可变字段。诊断日志保留于 `output/fuzz-step3/initial/` 和 `uncached/`，不用于最终指标。另用相同 32 例测试过查询共享，三个 JSONL 逐字节相同，但生成耗时 13.4／13.8 秒，没有观察到提速，因此撤回该候选。父守卫取值复用既有 `model_guards` 的打包读取与规范化接口。

Python 基线直接调用既有 `paging_fuzz.mutate` 和标准分页适配，以随机数初值 1、42、2026，每场景产生 2000 个不同输入。沿用原有父条目打乱轮转、M1/M2/M5 轮转、平台拒绝及输入排重；排重用 JSON 字段，不计算哈希。不调用原 campaign 的平台锁、硬件或来源快照。生成结果由当前 Rust replay-log 重新判定。

正式引导实验每场景、每个随机数初值也为 2000 个 mutant，含 5% 记录池对照，且开启全量认证。覆盖指标是本轮实际命中的不同类数除以 2，表示每千个 mutant；不把初始 corpus 的覆盖算入。多样性同时报告同目标类的改动字段最终取值组合唯一比例，以及完整前态输入唯一比例。另重跑初值 1 的两场景做逐字节确定性核对，并关闭额外认证单独测循环速度。

所有批量进程各 `-T 32`、最多同时 4 个；每 30 秒检查日志进展，连续 2400 秒没有进展即停止。保留原探索 partial 和错误，不把判定成功等同于全域探索完成。

诊断期间停止 shell 驱动时，Python 的线程池仍等待并继续排队任务，子进程没有一并退出，曾超过 4 个进程，并造成旧结束记录混入原目录。该轮日志与耗时不计入最终验收。驱动已改为 `exec python3`，捕获取消信号并结束本驱动登记的进程组，取消后不再启动队列任务；父子共同持有跨驱动的 4 个 `flock` 锁位，即使父进程被强制结束也不提前释放。假程序集成测试覆盖并发上限、取消清理和意外退出锁位，已通过。最终验收使用独立的 `final/`，旧进程退出前先占住对应数量的锁位，将新旧合计也限制在 4 个。实验脚本现在必须显式指定 `FUZZ_STEP3_OUTPUT`，旧监控器不能使用默认目录继续启动批次。

## 复现

从本工作树根运行；来源保持只读，输出目录必须不存在。工具链使用已有官方 Z3，构建、临时文件和实验输出均在本工作树。

```sh
mkdir -p output/fuzz-step3/tmp output/fuzz-step3/cache
export TMPDIR="$PWD/output/fuzz-step3/tmp"
export XDG_CACHE_HOME="$PWD/output/fuzz-step3/cache"
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_STEP3_OUTPUT="$PWD/output/fuzz-step3/final"
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
bash agents/path_merge_call_support/tools/fuzz/step3-experiments.sh all
bash agents/path_merge_call_support/tools/fuzz/step3-report.sh functional
bash agents/path_merge_call_support/tools/fuzz/step3-report.sh
```

脚本沿用第 2 步保存的 argv，只替换 fuzz 模式、输入、预算和输出，保留 IR、配置、指令及前态。每次实际 argv、cwd、退出码与进程墙钟见各批次 `done.json`，运行中另记录 `running.json` 的锁位。`all` 统一排队正式对照、确定性复验和普通模式速度测量，最多 4 个同时运行；也可依次用 `run`、`repeat`、`performance` 分别执行。重新运行应设置另一个尚未使用的绝对输出目录，避免覆盖已完成产物。

统计分两阶段：`functional` 完成六组引导和六组基线的逐字段统计、DAG 重读与 Python 兼容检查；默认阶段复用同目录已完成的功能验证记录，只补确定性与速度检查，避免重复执行已通过的 24000 例解码。

## 范围限制

- 形态 B 尚不跨完成路径；不同 DAG 的守卫坐标尚未对齐。类只有自身时使用形态 A；邻类额度或可变空间用完时另发形态 A 请求，并记录原因。
- 当前字段变异支持位向量与布尔自由字段；类内切片选择针对位向量。未接入符号构造子的变异策略；遇到不支持的内部值直接报错。
- 对照是既有编码空间算子的记录池抽样，没有在 Rust 中另写全新的 M1/M2/M5 随机记录生成器。验收的 Python 基线为每个初值重新调用原算子产生的 2000 个输入。
- 初始 corpus 已覆盖类目录时，普通 campaign 不会仅因类内取值不同就增加 corpus。本轮不实现桶反馈驱动的接纳、动态扩充调度类目录或硬件反馈。
- DAG 没有解析器、求值器或跨进程恢复能力；具体输入仍由当前模型重新认证。
- 不接 emu，不宣称硬件覆盖或检错收益。不改 IR、Sail、配置或 Python 文件，不重做既有排除域错误的逐查询证明。
