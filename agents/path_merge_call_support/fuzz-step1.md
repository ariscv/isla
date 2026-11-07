# fuzz 第 1 步：判定耗时与快档（2026-11-08）

**限定验收通过。** Sv39 STORE 的 380 个 corpus entry、1000 个 mutant，快档与认证档在 `-T 1/32` 下均逐字段零差异，三个负对照均零接纳。整批纯判定墙钟分别提速 **8.30／65.75 倍**，CPU 分别减少到原来的 **1/8.35／1/5.95**。工作区测试 **1115 通过、0 失败、6 项既有忽略**，原 1109 项无退化。

原型的线程扩展问题有两部分：逐输入屏障使唯一接纳路径上的证明与 JSON 写出无法并行；并发绑定又触发 Z3 全局锁竞争。Context 只在启动时创建，不是逐例成本。快档保留全部路径扫描，不依赖未经证明的跨路径互斥。

## 范围与实施

基线 `996048d`，仅修改本独立工作树，不做 Git 写操作。总体设计遵循 [架构](fuzz-architecture.md)，数据沿用 [M0](fuzz-m0.md)。未修改 IR、Sail、场景配置、原探索预算或其他工作树。编译器与 Cargo 均为 1.93.1，链接既有官方 Z3 `1fd1d3613`；128 个可用 CPU，无绑核。

实施顺序：先写失败测试及计时，再顺序测认证档的 1／32 线程批次，补锁与分配取样；随后实现快档，先冒烟，再顺序跑完整快档 1／32 线程与对拍，最后跑工作区测试。正式四个性能批次之间没有重叠，也未与本轮构建／测试重叠；诊断批次单列，不用于提速倍数。

## A：认证档分阶段耗时

下表只计 **1380 个正例**，不含三个负对照、首次探索、输入读取和启动恢复。CPU 是判定线程 CPU 之和。墙钟按每个输入最慢的工作线程归属阶段，剩余时间归入“其他”；并行线程的阶段墙钟不能直接相加当作整批时间。

| 阶段 | -T 1 CPU 秒／占比 | -T 1 墙钟秒／占比 | -T 32 CPU 秒／占比 | -T 32 墙钟秒／占比 |
| --- | ---: | ---: | ---: | ---: |
| 选路径／前态绑定 | 152.761／31.63% | 153.122／31.63% | 623.452／64.50% | 36.728／10.21% |
| 具体化、规范守卫与 ISA 展示 | 2.114／0.44% | 2.120／0.44% | 2.601／0.27% | 2.620／0.73% |
| 守卫唯一性证明 | 9.726／2.01% | 9.747／2.01% | 11.317／1.17% | 11.350／3.16% |
| 回滚后 check：重新绑定 | 11.791／2.44% | 11.817／2.44% | 12.514／1.29% | 12.546／3.49% |
| check：构造后态比较式 | 0.700／0.14% | 0.703／0.15% | 0.644／0.07% | 0.648／0.18% |
| check：后态唯一性证明 | 180.540／37.38% | 180.955／37.38% | 175.737／18.18% | 176.183／49.00% |
| 事务回滚 | 7.985／1.65% | 8.053／1.66% | 12.357／1.28% | 0.675／0.19% |
| JSON 写出 | 114.046／23.61% | 114.322／23.61% | 115.914／11.99% | 117.036／32.55% |
| 其他：保存事务、线程通信等 | 3.354／0.69% | 3.273／0.68% | 12.112／1.25% | 1.783／0.50% |
| 合计 | **483.016** | **484.112** | **966.647** | **359.567** |

`check` 本身包含后态唯一性证明，因此把重新绑定、比较式构造和取反查询拆开，避免重复计数。1380 个输入共有 **53212 次**后态取反查询，每例约 38.6 次。1000 个 mutant 的独立阶段表在 [单线程汇总](../../output/fuzz-step1/cert-t1/timing-summary.json)和 [32 线程汇总](../../output/fuzz-step1/cert-t32/timing-summary.json)的 `groups.mutant`；其 CPU／墙钟合计分别为 337.462／338.258 秒、680.136／250.726 秒。

启动与输入读取另列，以下墙钟明确区分累计线程时间和整个阶段经过时间：

| 项目 | -T 1 | -T 32 |
| --- | ---: | ---: |
| JSON 输入读取：CPU／墙钟秒 | 0.856／0.907 | 0.747／0.748 |
| Context 创建次数 | 1 | 26 |
| Context 创建：CPU／累计线程墙钟秒 | 0.002／0.002 | 1.022／1.032 |
| 检查点恢复：CPU／累计线程墙钟秒 | 0.109／0.110 | 0.380／0.392 |
| 线程启动至全部恢复完成：整段墙钟秒 | 0.112 | 0.078 |
| 首次探索墙钟秒 | 17.341 | 11.528 |

Context 和恢复并行执行，累计线程墙钟不能与整段墙钟相加。逐例没有创建 Context。主线程在整个判定批次的 CPU 为 0.068／0.654 秒，未混入工作线程 CPU。

### 为什么只快约 1.4 倍，CPU 却翻倍

含三个负对照时，认证档批次墙钟 **484.354→359.669 秒，1.347 倍**；CPU **483.221→967.595 秒，2.002 倍**。

- **墙钟受逐输入屏障限制。** 一个输入只有一条路径接纳，全部线程仍须返回后才发下一个输入。32 线程关键线程上的后态证明加 JSON 写出占 **81.55%** 墙钟；增加处理拒绝路径的线程无法缩短这部分。绑定的关键线程墙钟从 153.315 降到 36.784 秒，解释了整批大部分墙钟收益。
- **额外 CPU 几乎都在绑定。** 绑定 CPU 从 152.953 增到 624.360 秒，增加 471.407 秒，占总 CPU 增量 **97.32%**。Context 总 CPU 只有 1.022 秒，不能解释这个增量。
- **实测发现 Z3 全局锁竞争。** 同一批前 100 个 mutant，1／32 线程诊断中，`symbol::symbol(char const*)` 的锁调用分别为 **18476850／18496795 次**。26 个常驻线程记录的是同一锁地址；`addr2line` 将调用点定位为该函数。低层锁等待／唤醒处的 CPU 位置取样由 **0 增到 2411**，对应常驻线程总取样 33140／33882。取样数说明竞争实际发生，不作为精确 CPU 秒数。
- **分配工作量没有翻倍。** malloc 次数约 7922／7929 万，free 约 7949／7955 万；取样调用成本有上升。没有把全局锁、分配器内部和缓存开销进一步分成可相加的 CPU 秒数，也不把全部 471 秒都归给一把锁。
- **JSON 写出自身也很贵。** 100 例有 **1648226 次 write**，因为认证档直接把 serde JSON 小片段写入 File。完整单线程进程的 system CPU 为 111.56 秒，与 JSON 写出 114.05 秒 CPU 相符；快档整行写出后，该阶段降至 0.43 秒 CPU。

证据：[1 线程诊断](../../output/fuzz-step1/locks2-t1/locks-summary.json)、[32 线程诊断](../../output/fuzz-step1/locks2-t32/locks-summary.json)，原始锁地址、调用次数和 CPU 位置在各自 `locks.jsonl`。perf 和 ptrace 在本环境不可用，因此使用独立 `LD_PRELOAD` 取样工具；它只用于诊断，不用于提速表。首轮 `locks-t1/locks-t32` 日志被 time 父进程覆盖，不能用于结论；改为追加后重跑，采用 `locks2-*` 证据。

## B：快档做了什么

增加隐藏参数 `--judge-resident-fast`，必须与原有输入／输出参数一起使用。不加该参数继续调用完整认证档，保留逐例守卫证明、回滚及原 check。两档复用同一具体化、规范守卫和输出结构。

1. **每条路径只算一次静态事实。** 直接分析本次恢复后的 Isla `DefineConst`、前态、读取条件和输出，不加载旧证明、不按哈希或路径号认证。完整前态确定输入符号；活动读取只有在其地址和活动条件也由输入确定时才视为确定。对 ITE、短路布尔式保留条件，非活动自由读值不能污染结果。再用当前路径约束证明这些充分条件恒成立；守卫按既有父链语义归一化。后态证明还覆盖 result、后置寄存器、每次访存的活动条件、地址和数据，从而覆盖最终内存值与完整触碰范围。
2. **证明完整才省略逐例证明。** 本场景 26/26 路径的守卫、后态与前态形状条件均通过，索引建立约 0.16 秒。自由符号、未解释函数、浮点欠规定操作、不支持的前态形状、证明 Unknown、前态同地址含冲突字节等情况均走完整 judge；不把内部错误当成普通拒绝或给默认值。
3. **按整次读取绑定，复用已有假设查询。** 枚举能覆盖该次全部字节的具体基址，整段数据按小端打包，一次等式替代逐字节反复析取；支持地址回绕和缺字节拒绝。使用 `check_sat_with`，不新增定义或永久断言，也不为只读查询复制完整事务符号表。具体值等式仍复用原 `equal()`，避免改变数值文本等价语义。
4. **按输入并行。** 每个工作线程建立一个 Context，恢复全部路径，队列连续分派输入；一个线程完整检查一个输入的全部路径，删除逐输入的全线程屏障。32 线程快档实际用 32 个判定线程，认证档原型实际为 26。32 线程需恢复 832 份路径求解器；恢复墙钟 1.098 秒，峰值 RSS 1755.87 MiB，认证档为 1370.63 MiB。
5. **JSON 整行写出。** 各线程先在内存序列化，再短暂持锁写整行；计数仍拒绝重复接纳。认证档保留原来的写出方式。

旧 [ecfg4b 精确计数](exact-count-ecfg4b.md)证明的是冻结场景中“规范守卫只依赖投影位”，没有证明全部后态，也不是当前输入绑定协议的运行时证书，因此**没有直接复用其 PASS**。新分析复用了 Isla 的表达式、访存拆字节、父链上下文和具体化接口；旧 `EventReferences` 的无条件依赖集合不足以表达“未活动的读值不必确定”，所以条件分析单独放在 `sample_fast.rs`。

**未启用父路径优先和接纳即停。** 一条合并路径内的确定性不推出不同完成路径互斥；普通接口也允许重复路径被收集。现有样本每例恰好一条路径接纳，只是本批证据。未做全输入的跨路径互斥证明，因此仍扫描全部路径，并保持多接纳报错；在此条件下，单纯改变尝试顺序不减少工作量。未写 DAG 纯求值器、未改 Z3 内部锁或全局分配器。

快档 1→32 线程的批次墙钟提速 **10.66 倍**，CPU 仍增加 **2.81 倍**，不是线性扩展；并发绑定成本仍是后续可测瓶颈。

## C：对拍、提速与验证

下表为两种线程配置各一轮、相同 **1383 个输入**的整批判定。CPU 是工作线程服务 CPU 之和；快档允许多个输入同时处理，不能把逐输入服务墙钟相加冒充整批墙钟。

| 线程 | 认证档墙钟秒 | 快档墙钟秒 | 墙钟提速 | 认证档 CPU 秒 | 快档 CPU 秒 | CPU 成本缩减倍数 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| -T 1 | 484.354 | 58.325 | **8.30** | 483.221 | 57.873 | **8.35** |
| -T 32 | 359.669 | 5.470 | **65.75** | 967.595 | 162.755 | **5.95** |

含 IR 加载、探索、索引、恢复及收尾的进程总墙钟为 **507.887→81.108 秒（6.26 倍）**、**376.640→21.469 秒（17.54 倍）**。1000 个 mutant 的平均 CPU 为 **337.462→41.889 毫秒**、**680.136→114.769 毫秒**。进程完整 CPU（含探索、恢复及主线程）另为 **506.78→80.73 秒、993.85→215.93 秒**，缩减 **6.28／4.60 倍**。机器汇总：[speedup.json](../../output/fuzz-step1/speedup.json)。

- **逐字段对拍：PASS。** 两档两种线程配置均输出 1380 行；还分别与 M0 指定的独立 judge 真值、P1b 账本比较。路径号、规范守卫向量、result、完整前后寄存器、前后内存、isa_state、ret_val、唯一性标记等全部相同。只去掉进程内不稳定的 guard_order／guard_assignment，并按原 sample_id 对齐；不删其他字段，不算哈希。[1 线程对拍](../../output/fuzz-step1/compare-cert-t1-fast-t1.json)、[32 线程对拍](../../output/fuzz-step1/compare-cert-t32-fast-t32.json)；四个批次的 `differences.json` 也均为空。
- **三个负对照：PASS。** x1 翻转最低位、删除实际读取字节、根 PTE 指向排除区且补齐下级读取字节，两档两种线程配置均接纳 0 条路径。
- **最终二进制冒烟：PASS。** `-T 64`，输入 0、62、380 和三个负对照；认证档、快档正例字段均与完整基线相同，负对照零接纳。见 [smoke-verification.json](../../output/fuzz-step1/smoke-verification.json)。
- **测试与构建：PASS。** profile 红测缺少计时模块，fast 红测缺少分析／分类接口；分别实现后通过。最终 `cargo test --workspace --offline -j 8` 为 **1115 通过、0 失败、6 项既有忽略**，见 [汇总](../../output/fuzz-step1/test-summary.json)及 `test-workspace-final.log`。新增六项含计时一项、静态／分类边界四项、选项约束一项。首次全量有五个新增测试因与既有进程级 Qfaufbv 策略冲突失败；只修测试初始化后重跑通过，没有改变判定实现。最初的 bin 选项测试过滤为 0 项，正式改用 lib 入口后实际执行通过，不把空测试算成验证。
- **Make 冒烟：PASS。** 独立输出目录中 `make solve-MRET THREADS=64` 退出 0、4 条用例，保留既有 partial／unfinished=1；见 `output/fuzz-step1/mret/`。
- `cargo fmt --all -- --check`、`git diff --check`、新增 Python 的 ruff 检查和诊断 C 的 `-Wall -Wextra` 编译通过。

四个完整 Sv39 STORE 批次仍为原始退出 **1**、`partial / errors=5`；执行／SMT／终值查询超时、未完成路径与待处理批次均为 0。没有重新证明排除域错误，也没有改写成 finished。所有单步均低于 40 分钟，无超时或无进展停止事件。

## 修改文件

- `isla-lib/src/executor/sample_profile.rs`：可选线程局部阶段计时。
- `isla-lib/src/executor/sample_fast.rs`：当前路径的条件依赖分析、静态充分证明与快档绑定／分类。
- `isla-lib/src/executor/sample_fast_tests.rs`：自由符号、非活动读取／守卫、回绕、缺字节、只读查询边界。
- `isla-lib/src/executor/samples.rs`：计时接线、共用具体化、分类写出与计数；认证流程保留全部证明。
- `isla-lib/src/executor/merge_record.rs`：重导出现有父链上下文辅助函数。
- `src/isarch/resident.rs`、`resident_fast.rs`：认证档计时、快档队列与每线程求解器。
- `src/isarch/samples.rs`、`src/isarch/exec.rs`、`src/isarch_main.rs`：隐藏开关、约束与调用接线。
- `agents/path_merge_call_support/fuzz_step1_validate.py`：复用 M0 数据与验证，添加批次命名和两档直接比较；`fuzz_m0_validate.py` 仅允许新增计时标签。
- `agents/path_merge_call_support/tools/fuzz/lock_profile.c`、`summarize.py`：诊断、阶段汇总。
- 本文及 `fuzz-m0.md`、`status.md`、`agents/overview.md`、`agents/findings.md`、`specs/TODOs.md`、`docs/RESULTS.md`：结果入口与摘要。

## 复现命令

从本工作树根执行。输出全部在本树；来源只读。已有批次拒绝覆盖，复跑更换下列 `repro` 名称。

```sh
mkdir -p output/fuzz-step1/tmp output/fuzz-step1/cache
export TMPDIR="$PWD/output/fuzz-step1/tmp"
export XDG_CACHE_HOME="$PWD/output/fuzz-step1/cache"
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
python3 agents/path_merge_call_support/fuzz_m0_validate.py prepare
for t in 1 32; do
  python3 agents/path_merge_call_support/fuzz_step1_validate.py run --name cert-repro-t$t --threads $t
  python3 agents/path_merge_call_support/fuzz_step1_validate.py verify --name cert-repro-t$t --threads $t
  python3 agents/path_merge_call_support/fuzz_step1_validate.py run --name fast-repro-t$t --threads $t --fast
  python3 agents/path_merge_call_support/fuzz_step1_validate.py verify --name fast-repro-t$t --threads $t
  python3 agents/path_merge_call_support/fuzz_step1_validate.py compare --name cert-repro-t$t --other fast-repro-t$t
  python3 agents/path_merge_call_support/tools/fuzz/summarize.py timing output/fuzz-step1/cert-repro-t$t
done
```

诊断可另跑；它会干扰性能，因此与正式性能批次顺序执行：

```sh
cc -shared -fPIC -O2 -Wall -Wextra agents/path_merge_call_support/tools/fuzz/lock_profile.c \
  -o output/fuzz-step1/lock-profile.so -ldl -pthread
sed -n '381,480p' output/fuzz-m0/inputs.jsonl > output/fuzz-step1/diagnostic-inputs.jsonl
for t in 1 32; do
  python3 agents/path_merge_call_support/fuzz_step1_validate.py run --name locks-repro-t$t --threads $t \
    --diagnostic "$PWD/output/fuzz-step1/lock-profile.so" --inputs "$PWD/output/fuzz-step1/diagnostic-inputs.jsonl"
done
python3 agents/path_merge_call_support/tools/fuzz/summarize.py locks output/fuzz-step1/locks-repro-t1 --workers 1
python3 agents/path_merge_call_support/tools/fuzz/summarize.py locks output/fuzz-step1/locks-repro-t32 --workers 26
```

每个批次的 `done.json` 保存完整 argv、cwd、退出码与总墙钟；`time.txt` 保存进程 CPU 和峰值 RSS，`metrics.json` 保存所有阶段及逐输入数字。单独正确性冒烟用 `-T 64`；本轮 1／32 线程是用户明确要求的性能对照。
