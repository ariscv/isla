# fuzz 第 7 步：E2 四场景真实闭环

**四场景各 1000 例真实闭环已完成：3093 agree、907 条 mismatch 全部命中原有 R-XS-001、0 新分歧。** 四个完整结果集运行失败为 0；首次 Sv48 STORE 有 3 个超时、16 个取消，失败原件保留后按相同输入完整重跑。四场景相同初值的 4000 例确定性复跑全部通过，九个运行目录均无所属进程残留。

输入有效性依靠当前模型的第 0 步认证及逐例认证，不以二进制身份为门槛。没有新增或放宽规则，不自行判定新缺陷。

## 四场景闭环结果

下表只统计四个完整的 1000 例结果集。初轮 Sv39 结果在 `output/fuzz-step7/initial-1/`，两个 Sv48 完整结果在 `output/fuzz-step7/sv48-retry/`；首次失败尝试详见下文“首次 Sv48 STORE 的失败与重跑依据”，没有覆盖原件。每场景都为初值 1、反馈 none、八路 emu、T32。

| 场景 | corpus 第 0 步 | agree | 原始 mismatch | R-XS-001 | 新分歧 | 运行失败 | 循环秒/千例 | isarch 进程秒/千例 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 1359/1359 | 901 | 99 | 99 | 0 | 0 | 1005.4 | 1146.7 |
| Sv39 STORE | 609/609 | 702 | 298 | 298 | 0 | 0 | 1151.4 | 1230.8 |
| Sv48 LOAD | 2074/2074 | 761 | 239 | 239 | 0 | 0 | 1175.9 | 1527.4 |
| Sv48 STORE | 958/958 | 729 | 271 | 271 | 0 | 0 | 1085.0 | 1271.3 |

合计 **3093 agree、907 条 mismatch 全部命中原有 R-XS-001、0 新分歧**。规则命中仍计入原始 mismatch，不改算 agree。三方 cause 顺序为 Isla / emu / 独立 NEMU：338 条 LOAD 为 13 / 5 / 13，569 条 STORE 为 15 / 7 / 15。以上 cause 分布已逐例核对；不新增或放宽规则，不作新的缺陷判定。

循环墙钟包括生成、判定、逐例认证、worker 和反馈记录，排除一次性探索与 corpus 认证；进程墙钟包含这些一次性阶段。Python 准备 profile/对照及外层压缩不算入 isarch 进程时间。四个完整硬件进程墙钟合计约 86.3 分钟；这是共享主机本轮观测，不是稳定性能承诺，也不含失败尝试及模型复跑。

### 新分歧清单

**无。** 四个完整结果和首次失败尝试的已观察结果均没有未被规则归类的分歧。缺失 cause 的超时与取消保留为基础设施未完成，不作 agree 或新分歧。完整机器清单为 `output/fuzz-step7/new-disagreements.json`（`[]`）；未来有新条目时，汇总器会逐例保留前态、PTE 链、目标类与实际类、三方 cause，不自行判定缺陷。

### mismatch 中的 U / SUM / MXR

分母为各场景原始 mismatch；各列可重叠，“任一”按并集计数。

| 场景 | mismatch | U 态 | SUM=0 | MXR=1 | 任一条件 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 99 | 36（36.36%） | 54（54.55%） | 48（48.48%） | 85（85.86%） |
| Sv39 STORE | 298 | 118（39.60%） | 144（48.32%） | 126（42.28%） | 246（82.55%） |
| Sv48 LOAD | 239 | 82（34.31%） | 110（46.03%） | 128（53.56%） | 199（83.26%） |
| Sv48 STORE | 271 | 109（40.22%） | 128（47.23%） | 131（48.34%） | 219（80.81%） |
| 合计 | 907 | 345（38.04%） | 436（48.07%） | 433（47.74%） | 749（82.58%） |

每个场景的 1000 条 mutant 记录合起来均覆盖 U/S × SUM[0/1] × MXR[0/1] 的全部 8 种组合；逐例原始前态、认证前态与 worker 记录相同，全部满足本场景允许集合及 mstatus 位约束。STORE 的 MXR 位出现 1 不等于它改变写权限；本轮不据此另作语义判断。全部前态分布见总 `results.json`，以及各场景的 `contexts/mismatch_contexts`。

### 第 3、4 步指标与桶覆盖

每场景 950 个 A/B 和 50 个编码空间对照均接纳并完成真实回放。字段取值组合和完整前态唯一比例只统计 A/B，对照允许重复。桶为既有 PTE 字段桶，键包含完整 E2 类身份；不把 U/S、SUM、MXR 另创成新的桶定义。

| 场景 | A / B / 对照 | 认证命中目标 | 字段 / 完整前态唯一 | 实际命中类 / 目录类数 | 本轮覆盖桶 | 相对 corpus 新增桶 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 498 / 452 / 50 | 950/950 | 100% / 100% | 841 / 1359 | 29737 | 2583 |
| Sv39 STORE | 478 / 472 / 50 | 950/950 | 100% / 100% | 551 / 609 | 20935 | 2650 |
| Sv48 LOAD | 478 / 472 / 50 | 950/950 | 100% / 100% | 833 / 2074 | 41496 | 3599 |
| Sv48 STORE | 483 / 467 / 50 | 950/950 | 100% / 100% | 774 / 958 | 36648 | 3664 |

四场景的类身份互相隔离，因此本轮桶数可合计为 128816，新增桶合计 12496。全部 3800 个 A/B 都经完整认证命中目标，全部 4000 个输入的 worker 前态都与认证输入相同。

**目标类命中 100% 不等于覆盖全部类。** 初始 corpus 每类只有一个代表，1000 例预算没有覆盖每个场景的全部类，更没有穷举每类的所有权限位组合。所有目录与实际类数都原样报告；本轮反馈 none，不新增 corpus entry。

## 确定性与进程验收

四场景都用初值 1、相同 corpus、配置、T32、批次 64 和反馈 none，在独立模型进程重新生成全部 1000 例并做完整认证。比较包含原始两个文件的全部字节，没有删除字段或重算文件哈希；这两个文件本身不含耗时。硬件反馈不改变本轮调度。

| 场景 | mutants.jsonl 字节数 | judged.jsonl 字节数 | JSON 字段 / 全文件字节 |
| --- | ---: | ---: | --- |
| Sv39 LOAD | 33723528 | 65081453 | 全部相同 / 全部相同 |
| Sv39 STORE | 33633944 | 64620656 | 全部相同 / 全部相同 |
| Sv48 LOAD | 34140842 | 66275226 | 全部相同 / 全部相同 |
| Sv48 STORE | 33921697 | 65665220 | 全部相同 / 全部相同 |

完整证据为总 `determinism.json`，各组文件也分别保留。九次 isarch 运行（四个硬件、四个模型复跑、一个取消尝试）的 `remaining-processes.json` 全为 `[]`，检查发生在各自实际运行的进程环境中。原有超时、取消、独立会话和 native NEMU 子进程回收测试照常通过；附加八例回放全部正常退出。

最终机器验收入口为 `output/fuzz-step7/acceptance.json`：`complete=true`，但首次失败尝试仍明确记录 3 个超时和 16 个取消，不将其改写为通过。全量数据、总结果、新分歧清单、确定性和进程检查分别为同目录的 `results.json`、`new-disagreements.json`、`determinism.json`、`remaining-processes.json`、`incomplete-attempts.json`。

## 范围与实现

基于 `feat/isla-fuzz` 的 `19897328`，只修改本工作树，没有 Git 写操作。只读使用 `../isla-sym-config/output/fuzz-step6a/` 的四场景完整 E2 corpus、同组 `E2.toml`，以及 `../replay-p0/output/ecfg4b/` 的原 IR 和平台工具。Sv48 LOAD 显式选 `serial64/`。新场景配置 id 为 `sv39-load-e2` 等，逐场景重新认证全部 corpus entry。

本轮完整文件清单如下；`output/fuzz-step7/` 是被 Git 忽略的运行产物。

| 内容 | 文件 |
| --- | --- |
| 枚举取值变异与测试 | `isla-lib/src/executor/sample_mutation.rs`、`isla-lib/src/executor/sample_mutation_tests.rs` |
| E2 接线与对照生成 | `tools/fuzz/e2_campaign.py`（新增）、`tools/fuzz/run_campaign.py` |
| worker 前态与取消、测试 | `tools/fuzz/paging_worker.py`、`tools/fuzz/tests/test_paging_worker.py` |
| 四场景驱动与 E2 接线测试 | `tools/fuzz/step7_evaluate.py`（新增）、`tools/fuzz/tests/test_e2_campaign.py`（新增） |
| 本报告与议题摘要 | `agents/path_merge_call_support/fuzz-step7.md`（新增）、`agents/path_merge_call_support/status.md` |
| 公共说明与状态同步 | `README.md`、`agents/findings.md`、`agents/overview.md`、`specs/TODOs.md`、`docs/RESULTS.md` |

E2 约束是 `cur_privilege∈{User,Supervisor}`，以及 `mstatus & 0xfffffffffff3ffff == 0x0000000a00000000`；仅 SUM[18]、MXR[19] 可变。硬件仍使用 M 态指令和 MPRV+MPP 数据访问权限，不运行真 U 指令入口。

- `tools/fuzz/e2_campaign.py`：只读导入 `replay_symbolic_prestate.scenario_inputs/scenario_profile/bound_template`，复用四场景模板和平台域；不复制分页逻辑。对照重新调用 `paging_fuzz.mutate` 生成 150 条 M1/M2/M5 记录，保留 E2 前态；campaign 从中选择 5% 对照。只有既有平台边界拒绝可以记为未生成，内部错误照常中止。
- `tools/fuzz/run_campaign.py`：增加 `--e2-experiment`，指定 E2 corpus、配置、场景 id、对照和 DiffTest profile。旧 E0 入口保留。
- `isla-lib/src/executor/sample_mutation.rs`：枚举字段可参与形态 A；形态 B 放开枚举时，按声明成员构造候选并由 mutant 独立随机流打散，每个取值都由原约束判定后选择。沿用规范见证的枚举成员接口，不引入第二种类型表示或任意模型取值。
- `tools/fuzz/paging_worker.py`：继续用既有 `platform_case/build_case/run_probe/observe_run/MismatchTable`；将完整 `prestate_context` 保留到逐例结果。认证样本本身含原始 `cur_privilege/mstatus`，worker 入口由 E2 profile 检查域。`fuzz/difftest/CANCEL` 可请求取消；新 worker 先核对 Rust 父进程的 `--fuzz-output` 归属，再发送 SIGTERM，由原 Executor 清理已在途进程，不向其他任务发信号。
- `tools/fuzz/step7_evaluate.py`：最终采用硬件与模型复跑全部串行，每个 isarch 为 `-T 32`，硬件只有一个八路 emu 池。复用已有日志压缩和覆盖审计；不完整尝试单独写入 `incomplete-attempts.json`，不计作完成场景。
- `tools/fuzz/tests/`、`sample_mutation_tests.rs`：先记录 E2 接线缺失、worker 丢前态、枚举形态 A 无候选的失败，再补实现。新增 Rust 测试还覆盖形态 B、允许集合、有限域耗尽、目标类认证和确定性。

## 运行口径

每场景 1000 个 mutant，其中 A/B 合计 950、编码空间对照 50；随机数初值 1，`--fuzz-feedback none`，批量 64。先跑 20 例 Sv39 STORE 真实冒烟，20/20 agree，随后正式启动。冒烟使用枚举支持修复前的二进制，仅作入口检查，不代替正式验收。

耗时分开记录进程墙钟和循环墙钟；后者排除一次性探索及 corpus 认证。覆盖采用既有 `(完整类身份, PTE 层级, 字段, 取值桶)`，统计 mutant 自身覆盖和相对初始 corpus 新增值。多样性仅对 A/B 计同目标类完整前态、改动字段最终取值组合的唯一比例。原始 mismatch 包括被规则归类的实例，新分歧仅指未被任何规则归类且非基础设施失败的实例。

所有运行产物位于 `output/fuzz-step7/`。每次命令保存原始退出码；保留探索排除域导致的 partial/退出 1，不把完整闭环写成整个符号输入域探索完成。

## 已完成的代码验收

- `cargo test --workspace --offline -j 8`：1149 通过、0 失败、6 项既有忽略；原 1148 项无退化，新增 1 项枚举变异测试。
- 本树 Python 测试 9 项通过；外部指定测试目录 142 项通过，未修改或跳过测试。第一次外部测试命令将输出目录错误地指向只读工作树，出现 3 个 I/O 错误；改为本树绝对输出路径后全部通过。两次日志均保留。
- `cargo fmt --all -- --check`、release 构建通过。Make MRET 独立目录冒烟退出 0、4 条结果，保留既有 partial/unfinished-paths=1 和 Poison 提示；沿用 `TASTIC=default`，没有运行全量 `make solve`。
- TDD 证据：`test-e2-red.log`、`test-worker-red.log`、`test-enum-red.log`、`test-cancel-red.log`；最终测试为 `test-rust-final.log`、`test-enum-green.log`、`test-python-existing-final.log`、`test-python-final.log`。

## 首次 Sv48 STORE 的失败与重跑依据

首版驱动让一个 T32 模型复跑与下一场景的八路 emu 交叠；Sv39 的两个完整场景和两个确定性复跑均完成。在首次 Sv48 STORE 的首批 64 例中，输入 1、3、4 达到原 120 秒外限；成功结束的若干单例也耗时 101–119 秒。同期主机负载约 157（128 个逻辑核），可用内存约 130 GiB，没有 swap；CPU 压力升高。这里只记录运行时观察，不据此断定超时根因。

先停止这次尝试，保留 **20 agree、25 条 R-XS-001、3 个 timeout、16 个 cancelled、0 新分歧**。16 个取消中，8 个有逐例记录，8 个尚未启动；Rust 均保留为基础设施未完成。原始退出码为 1、mutant 数为 64，驱动按未完成预算报失败，未改算通过。`remaining-processes.json=[]`。目录是 `output/fuzz-step7/initial-1/sv48-store-1-difftest/`，完整失败清单为初轮 `incomplete-attempts.json`。

停止模型交叠后，用同一认证文件中的输入 0–7（包含全部 3 个超时输入），按原八路和 120 秒外限独立重放。8/8 正常结束，emu 耗时 5.301–9.107 秒，5 agree、3 条 R-XS-001，0 新分歧；证据为 `output/fuzz-step7/probe/results.json`。未替换输入、增加超时或改规则。

随后在新目录 `output/fuzz-step7/sv48-retry/` 完整重跑两个 Sv48 场景，每场景仍为同一初值 1、1000 个 mutant。失败目录和附加回放均不并入正式 4000 例的分母，也不从交付记录中删除。最终驱动将硬件与模型复跑分阶段串行；不保证主机负载与超时之间的具体因果关系。

首次 64 个输入与重跑的对应认证输入已按完整 JSON 逐字段比较，64/64 相同，见 `output/fuzz-step7/retry-input-comparison.json`。没有靠换输入绕过超时。

## 复现命令

在本工作树根目录执行；每个实验输出目录必须不存在，外部路径只读。

```sh
mkdir -p output/fuzz-step7/tmp
export TMPDIR="$PWD/output/fuzz-step7/tmp"
export PAGING_TEST_OUTPUT_DIR="$PWD/output/fuzz-step7/python-existing-repro"
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
export PT_DECODE_DIR="$(realpath ../isla-enumerate/agents/path_merge_call_support/pt_decode)"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
python3 -m unittest discover -s tools/fuzz/tests
(cd ../replay-p0/difftest-xiangshan/tests && python3 -m unittest discover -s .)
python3 tools/fuzz/step7_evaluate.py run --output output/fuzz-step7/reproduce --initial 1
python3 tools/fuzz/step7_evaluate.py report --output output/fuzz-step7/reproduce
```

单场景命令如下；四场景的 `--scenario` 分别为 `sv39-load/sv39-store/sv48-load/sv48-store`。`done.json` 保存实际完整 `isarch fuzz` 命令。确定性复跑使用相同参数及新的目录，改 `--executor model --certify-all`，逐字段、逐字节比较 `mutants.jsonl` 和 `judged.jsonl`，不比较计时。

```sh
python3 tools/fuzz/run_campaign.py --scenario sv39-store \
  --e2-experiment ../isla-sym-config/output/fuzz-step6a \
  --budget 1000 --random-seed 1 --threads 32 --executor difftest \
  --output output/fuzz-step7/reproduce-store --fuzz-feedback none \
  --fuzz-batch-size 64 --difftest-workers 8 --certify-all
```

## 未做与遗留

- 没有追加随机数初值 42。本轮四个完整硬件进程合计约 86.3 分钟，已高于最初约半小时的估计；优先完成初值 1、失败恢复和全部确定性复跑。没有触发单步 40 分钟或闭环 60 分钟无进展的停止条件。
- 没有真 U 指令入口、U 态取指或 CSR 测试，仍为 MPRV+MPP 数据访问路径；没有 E3 或 MPRV/MPP 新域。
- 原始探索仍退出 1、status=partial，Sv39 errors=5、Sv48 errors=7；执行/SMT/终值查询超时、未完成路径与待处理批次均为 0。本轮没有重新证明旧排除区的每条错误，不能将完成路径上的认证和闭环写成全域探索完成。
- 没有全量 `make solve`，仅完成前述 Make MRET 冒烟；没有穷举每类权限位组合、跨完成路径的形态 B、纯 DAG 求值器、RTL 覆盖或反馈策略优化。
- 初次 Sv48 STORE 超时的根因未被确定；记录了主机负载、原输入重放和完整重跑，不自行归因于硬件缺陷。已有规则原样保留，没有新增或放宽规则，也没有给新分歧作缺陷判定。
- 只修改本工作树，其他工作树和 emu/NEMU 只读；没有 Git 写操作。提交由协作者另行处理。
