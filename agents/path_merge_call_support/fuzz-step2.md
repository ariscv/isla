# fuzz 第 2 步：正式子命令与 P1b 回放（2026-11-08）

**第 2 步限定验收通过。** 四场景共 2836 个 corpus entry 通过认证，5000 个 mutant 与 P1b 逐例零差异；两轮完整运行的 60 个正式产物逐字节相同（仅排除耗时文件）。工作区测试 1128 通过、0 失败、6 项既有忽略，原 1115 项无退化。只修改当前独立工作树，不做 Git 写操作，不接 emu，不改 Python 文件。

基线为 `cab2d4c` 加本轮未提交改动；使用现有官方 Z3 `1fd1d3613`、默认 direct 后端，Cargo/Rust 1.93.1，主机提供 128 个 CPU。

## 实现范围与文件

`fuzz` 与 `solve-state` 并列，直接进入同一套参数、断言分叉转换、初始内存、指令与前态解析、探索入口。完成路径复用 M0 的 `ResidentPath`，分类直接复用 `SamplePath::judge` / `classify` 和第 1 步的 `FastFacts`，没有复制求解算法或改 Sail 语义。每个场景仅探索一次，每个工作线程恢复全部路径一次；corpus 认证与 mutant 快档共用这些求解器。

| 文件 | 职责 |
| --- | --- |
| `src/isarch/fuzz/mod.rs` | 会话、已有来源记录、逐 mutant 随机流 |
| `src/isarch/fuzz/options.rs` | `judge-only`、`replay-log`、预留 `campaign` 及参数约束 |
| `src/isarch/fuzz/traits.rs` | 五个 trait、固定记录调度、仅观察的反馈实现 |
| `src/isarch/fuzz/classifier.rs` | 队列、常驻求解器、批次提交、输出接线 |
| `src/isarch/fuzz/corpus.rs` | corpus 认证、规范向量排序与类目录 |
| `src/isarch/fuzz/replay.rs` | P1b 原记录应用、读取范围核对、两处 `fcsr` 审计 |
| `src/isarch/fuzz/report.rs` | P1b 同口径账本、覆盖、转移、统计与候选特征 |
| `src/isarch/fuzz/io.rs` | 稳定 JSON / JSONL 与守卫坐标重编号 |
| `src/isarch/fuzz/tests.rs` | trait、确定性、回放、不变量与报表回归 |
| `src/isarch_main.rs` | `parse_subcommand` 分支、共用探索参数、中文帮助和用法 |
| `src/isarch/mod.rs`、`samples.rs`、`exec.rs` | 模块导出、会话持有、完成路径保存与执行接线 |
| `Cargo.toml`、`Cargo.lock` | `rand_chacha = 0.2.2` 直接依赖，离线使用已有锁定版本 |
| `README.md`、`specs/isarch-cli.md` | 使用入口与正式参数说明 |
| 本文、`status.md`、`agents/overview.md`、`agents/findings.md`、`specs/TODOs.md`、`docs/RESULTS.md` | 交付记录、状态摘要、已验证的代码事实与索引 |

架构文档在本轮开始时已有未提交修改，本轮原样保留。实施与测试证据均在 `output/fuzz-step2/`。

## 五个接口

| trait | 接口与当前行为 |
| --- | --- |
| `Scheduler` | `next_batch(&self, limit) -> Vec<usize>`；`on_batch_end(&mut self, completed)`。批次领取不改变位置，整批结果收齐后才提交位置 |
| `Mutator` | `mutate(&self, parent: &Sample, record: &Value, rng: &mut ChaCha8Rng) -> Sample`。当前只精确应用历史 M1/M2/M5 记录，不生成新改动 |
| `Executor` | 关联类型 `Input` / `Output`；`submit(&mut self, Vec<Input>)`；`drain(&mut self) -> Vec<Output>`。有界任务队列、常驻线程、批次结果按输入编号顺序返回 |
| `Oracle` | `compare(&self, expected: &Value, observed: &Value) -> Option<Value>`。当前 `NoHardwareOracle` 明确返回 `None`，没有硬件比较结论 |
| `Feedback` | 关联类型 `Feature`；`observe(&mut self, sample_id, &Feature)`；默认 `is_novel=false`、`score=1.0`，并预留 `on_corpus_add` / `on_mismatch` |

框架不解释特征。报表适配层将类身份、结果和输入字节高四位的取值桶交给 `LogFeedback`，只写观察日志，没有据此增加 corpus、改变分数或过滤差异。

## 第 0 步与类身份

每个 corpus entry 使用完整认证档扫描全部完成路径，要求恰好一条路径接纳，路径号不变，守卫与后态唯一。逐字段比较 `result`、前后寄存器、前后内存、`ret_val`、`isa_state`；随后每条路径内按规范守卫向量排序，要求从零开始的名次等于原 `class_id`。任何不变量违反直接报错终止。

类的内部身份为 `(scenario_config_id, path_signature, guard_vector)`；整数类号只用于兼容输出。`--fuzz-scenario` 是场景配置 id，本轮固定为已有四场景名；切换语义配置应使用另一个 id，并重新认证 corpus。没有用二进制或文件哈希控制有效性。`provenance.json` 原样记录 corpus 目录已有的 `done.json`、`samples.manifest.json` 与当前程序路径，没有重算文件哈希。

## 回放与输入审计

历史 `mutations.json` 没有包含 Python 补齐新读取字节和裁剪内存范围的过程。回放从同目录 `judge-batches.json` 定位原始 samples v1 输入，也可指定 `--fuzz-inputs`。Rust 按原记录的父路径与父类号找到当前 corpus entry，应用位翻转、PPN 改动、页面复制和 STORE 未知初值的既定具体化规则，再逐字节核对原始输入范围。新增读取只接受原流程明确约定的零值或固定数据标记。没有在 Rust 中重写分页语义；最终输入交给当前 Isla 判定。

旧 mutant 的两处 `fcsr` 分别取自父 corpus entry 的 `pre_registers.fcsr` 与 `isa_state.fcsr`。补入后删除这两处，要求整个 JSON 与原对象完全相等；`pre_memory` 另行比较。因此补齐没有改变页表字节、地址、SATP、指令和其他输入。

旧 `parent_sample_id` 只作历史来源保留；`parent_corpus_entry` 另存本次 ecfg4b 的实际条目编号与完整类身份，避免把旧文件编号误当当前 corpus entry 编号。

## 输出和 Python 兼容

每次 `--fuzz-output` 必须是绝对路径的新目录，拒绝覆盖已有批次。

| 产物 | 内容 |
| --- | --- |
| `reconfirm.json` | 每个 corpus entry 的认证检查结果 |
| `seed-map.json` | corpus 类目录，含完整类身份、兼容类号、条目编号 |
| `corpus-judged.jsonl` | corpus 认证输出，judged v1，填写反查类号 |
| `mutants.jsonl` | 实际送判定的前态输入，samples v1，期望字段清空 |
| `mutations.jsonl` | mutant 编号、算子、历史父编号、当前父 corpus entry 和逐字段改动；去掉历史预测耗时 |
| `judged.jsonl` | 接纳结果，judged v1，`sample.class_id` 为实际反查类号；未接纳者无行 |
| `classified.jsonl` | 从 judged 提取的完整 samples v1，供现有 Python 流程读取 |
| `coverage.json`、`transitions.json`、`statistics.json`、`ledger.json` | 类命中与未命中、跳类转移、P1b 同口径统计、逐例账本 |
| `observations.jsonl` | 候选特征，不触发 corpus 增长 |
| `path-index.json`、`provenance.json`、`input-audit.json`、`timing.json` | 当前路径静态事实、来源、输入审计、分阶段耗时 |

对外样本只用 samples v1 / judged v1，不向样本结构加入框架元数据。账本不伪造 `j2_cause` / `old_isla_cause`；这些历史列留在只读 P1b 账本里。新账本计算的 `judge_cause` 会与历史三方列核对。新类仍用完整身份记录，兼容 `class_id=null`；本批没有新类。

## 确定性

随机流使用 `ChaCha8Rng`。32 字节初值由 SHA-256 对域标记、随机数初值、场景字节长度与内容、mutant 编号派生，整数均为小端编码。这里计算的是随机流初值，不是文件身份检查。精确回放不消费随机数；后续算子继续接收同一接口。

每批完整返回后才更新调度。判定结果按输入顺序写出，路径按签名排序；将进程内 `guard_order` 重新编号为规范向量坐标 `0..n`，并同步构造 `guard_assignment`，保留原向量及其顺序。判定结构仍为 schema v1；不把进程内记录编号当跨进程身份。

**确定性复验通过。** 四场景各 15 个文件，共 60 个文件、1,007,461,037 字节，两次独立进程运行逐字节一致，见 [determinism.json](../../output/fuzz-step2/determinism.json)。比对范围是 `fuzz/` 的全部正式产物，单独排除耗时文件 `timing.json`；探索器原有诊断日志、外层命令记录和进程计时不作为确定性数据接口。

## 验收结果

**四场景全部通过。** 2836 个 corpus entry 全部完成认证，5000 个 mutant 各恰好一条路径接纳。与只读 P1b 的 `ledger.json` 逐例核对全部共有列，并核对 `judge_cause == j2_cause == old_isla_cause`；逐字段核对完整 judge JSON（只去掉进程内守卫编号，并填入反查类号）、类目录、`statistics.json` 和全部转移表，差异均为 0。完整结果见 [comparison.json](../../output/fuzz-step2/comparison.json)，[差异清单](../../output/fuzz-step2/differences.json)为空。

| 场景 | corpus entry | mutant | 留父类 / 跳类 | 命中类 / 总类 | 差异 | 纯判定秒 | corpus 认证秒 | 进程总秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sv39-store | 380 | 1000 | 548 / 452 | 354 / 380 | 0 | 5.381 | 26.241 | 61.818 |
| sv39-load | 728 | 2000 | 1095 / 905 | 672 / 728 | 0 | 7.640 | 48.940 | 89.262 |
| sv48-store | 606 | 1000 | 503 / 497 | 426 / 606 | 0 | 4.892 | 76.795 | 119.993 |
| sv48-load | 1122 | 1000 | 494 / 506 | 581 / 1122 | 0 | 4.117 | 143.182 | 178.786 |
| 合计 | 2836 | 5000 | 2640 / 2360 | 2033 / 2836 | 0 | — | — | — |

四场景各一个进程、各 `-T 32`、最多四个同时运行。纯判定包括批次派发、扫描全部路径和结果收集，不含探索、索引、恢复、corpus 认证、输入处理和文件落盘。表为最终完整回放一轮的单次墙钟实测，四场景并行，不能解释为隔离环境的跨场景性能排序。第二轮只用于确定性，其中一部分与全量测试重叠，不用其耗时作为性能结论。

两轮八个进程均保留原始退出 1、`partial/errors=5/5/7/7`；执行、SMT、终值查询超时、未完成路径与待处理批次均为 0。本轮未重做旧排除域的逐查询证明。全部运行持续有进展，未触发 40 分钟停止条件。

- **输入审计通过：** 5000/5000 只补两处 `fcsr`，删除后整个原始 JSON 不变，`pre_memory` 单独相同；所有回放字节匹配。各场景 `input-audit.json` 保存检查汇总。
- **只判定模式通过：** Sv39 STORE 1000 个 mutant，与 replay-log 的完整 judged 行完全相同；三种既有负对照均零接纳。使用批量大小 97，验证不同批次边界，见 [judge-only-verification.json](../../output/fuzz-step2/judge-only-verification.json)。
- **Python 兼容通过：** 完整 `classified.jsonl` 5000/5000 通过现有 samples v1 字段检查和 P1b 的 `paging_replay.classify_standard_pte` 标准分页适配解码，没有接 emu。直接调用未适配的基础解码器会误判 NAPOT；正式兼容验证使用原 P1b 适配流程。见 [python-compatibility.json](../../output/fuzz-step2/python-compatibility.json)。
- **TDD 与单元测试通过：** 初始红测缺少接口；另有执行器缺接口、路径别名 P00/P01、当前 corpus entry 引用和只判定模式误记跳类的失败测试，修复后通过。新增 12 项 fuzz 单元测试及 1 项子命令继承测试，共新增 13 项。覆盖五个 trait、独立随机流、批次提交、结果排序、守卫坐标、M1/M2/M5 回放、错误旧值、corpus 路径／后态／类名次不变量和报表兼容。
- **构建与工作区测试通过：** 离线 release 构建；`cargo test --workspace --offline -j 8` 为 1128 通过、0 失败、6 项既有忽略；`cargo fmt --all -- --check`、`git diff --check` 通过。最终清理仅将一次调用的加载包装内联并修正注释，另跑最终构建、全工作区测试和三正例／三负对照冒烟；冒烟完整 judge 与正式回放一致。测试日志见 `output/fuzz-step2/test-workspace-final.log`，最终冒烟见 `output/fuzz-step2/final-smoke/verification.json`。
- **Make 与帮助通过：** 独立目录 `make solve-MRET THREADS=32` 退出 0、4 条用例，保留既有 `partial/unfinished-paths=1`；`fuzz --help` 退出 0，明确两种模式、参数、v1 输出及 campaign 未实现；选择 campaign 明确退出 1。

## 未做与遗留

- `campaign` 仅留模式与接口，选择该模式会明确报尚未实现；没有生成新的变异算子。
- 不接 emu、NEMU、XiangShan worker，不宣称硬件一致性；没有 corpus 增长或 finding。
- 静态条件不足仍使用已有完整 judge；没有写新的替代判定逻辑。继续扫描全部路径检查重复接纳，没有启用未经证明的接纳即停。
- 历史回放需要原始输入作为读取范围记录；记录本身不足以重建 Python 的读取补齐过程。缺记录直接报错，不猜测输入。
- corpus 和输入驻留内存；每次进程启动重新探索，不跨进程保存检查点。一次会话针对一个固定场景与指令，没有多场景共用一个进程的全局唯一路径保证。
- 原有 `partial/errors=5/7` 与原始退出 1 保留。本轮不重新证明旧排除域终止，不将这些状态写成 finished。

## 复现命令

从本工作树根执行，先构建并测试。来源目录只读；下列 `repro` 目录应为尚不存在的新目录。Z3 使用已有安装，所有构建、缓存和测试产物都在本工作树。

```sh
mkdir -p output/fuzz-step2/tmp output/fuzz-step2/cache
export TMPDIR="$PWD/output/fuzz-step2/tmp"
export XDG_CACHE_HOME="$PWD/output/fuzz-step2/cache"
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
target/release/isarch fuzz --help
```

四场景回放直接复用 ecfg4b 的实际命令，只移除 J1 检查输入／报告，换成正式 fuzz 参数。脚本内没有重建模型或重算文件哈希，外限为 40 分钟。要做确定性复验，将 `repro` 改成另一个新名字，重复同一段。

```sh
python3 - <<'PY'
import concurrent.futures, json, os, subprocess, time
from pathlib import Path
root = Path.cwd()
base = root / 'output/fuzz-step2/repro'
source = root.parent / 'replay-p0/output'

def run(scene):
    directory = base / scene
    directory.mkdir(parents=True, exist_ok=False)
    argv = json.loads((source / 'ecfg4b' / (scene + '-j1') / 'done.json').read_text())['command']
    argv[0] = str(root / 'target/release/isarch')
    for flag in ['--check-samples', '--check-samples-report']:
        index = argv.index(flag)
        del argv[index:index + 2]
    argv[argv.index('solve-state')] = 'fuzz'
    argv += ['--fuzz-mode', 'replay-log', '--fuzz-scenario', scene,
             '--fuzz-corpus', str(source / 'ecfg4b' / scene / 'samples.jsonl'),
             '--fuzz-mutations', str(source / 'fuzz-p1b' / scene / 'mutations.json'),
             '--fuzz-output', str(directory / 'fuzz')]
    assert argv[argv.index('-T') + 1] == '32'
    environment = os.environ.copy()
    environment.pop('LD_PRELOAD', None)
    started = time.monotonic()
    with (directory / 'stdout.log').open('w') as stdout, (directory / 'stderr.log').open('w') as stderr:
        result = subprocess.run(argv, cwd=directory, env=environment,
                                stdout=stdout, stderr=stderr, timeout=2400)
    (directory / 'done.json').write_text(json.dumps(dict(command=argv, cwd=str(directory),
        returncode=result.returncode, seconds=time.monotonic() - started), indent=2) + '\n')
    assert result.returncode in (0, 1)
    assert (directory / 'fuzz/timing.json').exists()
    print(scene, result.returncode, flush=True)

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    list(pool.map(run, ['sv39-store', 'sv39-load', 'sv48-store', 'sv48-load']))
PY
```

`judge-only` 沿用相同探索参数，改用 `--fuzz-mode judge-only --fuzz-inputs <samples v1 路径>`，删除 `--fuzz-mutations`，并使用新的输出目录。旧缺 `fcsr` 的原始文件应通过 `replay-log` 补齐；`judge-only` 要求完整前态。最终正式回放的实际 argv、cwd、原始退出码保存在 `output/fuzz-step2/replay/<场景>/done.json`。

核对正式产物可直接逐字段比较，不计算哈希：

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path.cwd()
reference = root.parent / 'isla-judge/output/fuzz-p1b-classes'
expected_ledger = json.loads((reference / 'ledger.json').read_text())
expected_statistics = json.loads((reference / 'statistics.json').read_text())
for scene in ['sv39-store', 'sv39-load', 'sv48-store', 'sv48-load']:
    directory = root / 'output/fuzz-step2/replay' / scene / 'fuzz'
    actual = json.loads((directory / 'ledger.json').read_text())
    expected = [row for row in expected_ledger if row['scene'] == scene]
    assert len(actual) == len(expected)
    for left, right in zip(actual, expected):
        for key in right.keys() & left.keys():
            assert left[key] == right[key], (scene, left['sample_id'], key)
        assert left['judge_cause'] == right['j2_cause'] == right['old_isla_cause']
    for key, value in json.loads((directory / 'statistics.json').read_text()).items():
        assert value == expected_statistics[key], key
    repeated = root / 'output/fuzz-step2/repeat' / scene / 'fuzz'
    assert {p.name for p in directory.iterdir()} == {p.name for p in repeated.iterdir()}
    for path in directory.iterdir():
        if path.name != 'timing.json':
            assert path.read_bytes() == (repeated / path.name).read_bytes(), (scene, path.name)
    print(scene, len(actual), '逐字段与逐字节均相同')
PY
```
