# fuzz 第 5 步：覆盖反馈与真实对照

**反馈、corpus 增长与真实对照已完成；两场景均未同时达到“新增桶更多、已知问题耗时占比更低”的收益目标。** STORE 的已知问题耗时下降，但新增桶减少；LOAD 的新增桶略增，但已知问题耗时占比上升。8000 个正式 mutant 中 6725 一致、1275 条不一致全部被 R-XS-001 归类，0 新分歧、0 基础设施失败。评分在正式评估前确定，未根据结果调整参数。

基线为 `e08f4fd` 加本轮未提交修改，分支 `feat/isla-fuzz`。仅修改本工作树，未执行 Git 写操作。沿用 ecfg4b 的 IR、配置、固定 S 态和标准分页重放链；外部工作树只读。完整 1000 例硬件反馈重跑通过：含 DAG 的 50 个正式产物逐字段、逐字节相同，耗时文件中的非耗时元数据也相同；最终所属进程无残留。

## 特征与评分

字段桶直接调用只读 replay-p0 的 `paging_fuzz.Coverage`，以及标准分页适配后的 pt_decode。保留字段划分与 `ppn_bucket` 的九个区域，使用实际类身份替换旧的形状身份。键为 `(场景配置 id, path_signature, 规范守卫向量, PTE 层级, 字段, 取值桶)`，不记录数据页为 PTE，不用任意字节的高四位代替字段。

不一致签名为 `(实际目标类, 不一致字段, 阶段)`，另外保留 `filtered` 和第 4 步给出的规则编号 R-XS-001。基础设施失败不构成不一致签名。`is_novel` 在出现新字段桶，或第一次出现尚未被规则归类的签名时为真。同一签名先命中规则、随后有未归类实例，后者仍是新分歧；规则命中只作用于具体实例。

每类已见桶数为 C，字段可能桶数的上界为 P：单个位 2，RSW、RSW_60t59b、PBMT 为 4，reserved 为 32，PPN 为 9；只合计已经见过的 PTE 层级及字段。P 是字段范围上界，包含该类不可达的桶，不是求解器证明的可达总数。B 为当前已提交批次数，L 为最近观察到新桶时的已提交批次数；初始 corpus 的 L 为 0。每批结束后：

```text
基础分 = 1 + 4 × max(P − C, 0) / max(P, 1)
若该类出现过已知不一致、从未出现未知不一致，且 B − L ≥ 2：
    score = 基础分 / 8
否则：
    score = 基础分
```

未知不一致一旦出现，该类不再因已知规则降权。已知实例带来新桶时照常接纳并恢复基础分。评分不跳过硬件验证、不放宽窄规则、不把整类判成已知问题。

## 调度与 corpus

默认 `--fuzz-feedback coverage`。按 `(已调度次数 + 1) / score` 最小者选择父类，同分按稳定目录顺序；类内按同式选择 corpus entry，同分按加入顺序。形态 B 沿用同路径最近守卫距离，距离相同再按 `(已命中和预约次数 + 1) / score` 选择目标。反馈模式不使用原来的等额目标上限，以免上限抵消加权；`--fuzz-feedback none` 保留既有类轮转、父代表和邻类额度策略，仍观察同样的反馈以便对照。

批次开始时固定评分、corpus 和已提交次数，批内只在临时副本中预约。生成与硬件结果按 mutant 编号收齐，之后才提交覆盖、签名、corpus、次数与评分。每个 mutant 继续使用既有独立随机流。新 corpus entry 必须先经认证档，并用 `(完整类身份, input_id)` 标识；`input_id` 为 `initial:原输入编号` 或 `mutant:本轮编号`，不以整数类号为身份。`corpus-added.jsonl` 同时保存完整认证样本与父身份。批内相同新特征只接纳首个输入，后续批次可选新条目为父输入。

新增代码分工：`feedback.rs` 保存特征、新颖性和评分；`value_features.py` 只调用既有解码和覆盖接口；`campaign.rs` 接入批次提交与血缘；`step5_evaluate.py` 顺序运行真实对照并统计。三方原始结果保留在逐例 `result.json`，确定性的根目录结果只保留三方语义字段；耗时单列 `hardware-timing.jsonl`。DAG 文件升级为版本 2，只把内部守卫编号重排成已有规范坐标；原始 SMT 定义及其顺序不变，通用导出 API 保留版本 1。大日志无损压缩为 `difftest.log.gz`。原 `observations.jsonl` 继续兼容旧报表，实际调度使用 `feedback-observations.jsonl` 的字段桶。

## 评估口径

计划 Sv39 STORE、LOAD，各对比 none / coverage，各两个随机数初值 1、42，每设置 1000 个 mutant，总计 8000。每批 64，保持既有 5% 记录池对照；每个 isarch `-T 32`，真实实验顺序执行，仅一个 8 路 emu 池。两种模式先后交替，不依据结果调参。先用独立小批估算时间；若预计超过约三小时，统一缩减两种模式的预算并记录依据。

分别报告 mutant 自身覆盖的不同类字段桶、相对初始 corpus 新增桶、不同签名及其规则归类、已知问题占 emu 时间的比例。时间比例使用各例 emu `elapsed` 之和，不拿命中次数代替；并行服务时间之和不是整批墙钟。循环每千例墙钟使用 `timing.json.loop_seconds`，排除一次性探索和 corpus 认证；进程时间另列。新分歧只列输入与三方 cause，不自行认定缺陷。

## 真实评估结果

正式八组均完成 1000 例，未缩减预算。两个初值 1、42；每批 64，950 个路径引导加 50 个记录池对照；各 isarch 为 `-T 32`。设置顺序为 STORE 的 none/coverage 初值 1、coverage/none 初值 42，再按同样顺序执行 LOAD。始终只有一个 8 路 emu 池，没有增加至上限 12。

本轮覆盖桶统计本轮 mutant 出现的不同键；新增桶统计其中初始 corpus 未见的键。初始 STORE/LOAD 分别有 13216/26152 个桶，最终累计桶数为初始桶数加新增桶数。不一致签名按完整目标类、字段和阶段去重；表中已知/新分别为窄规则归类与未归类签名数。

| 场景 / 初值 | 调度 | 本轮覆盖桶 | 新增桶 | 已知 / 新签名 | 已知 emu 时间占比 | 循环秒 / 千例 |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| STORE / 1 | none | 14877 | 2247 | 129 / 0 | 20.56% | 928.1 |
| STORE / 1 | coverage | 14503 | 2199 | 111 / 0 | 15.86% | 887.9 |
| STORE / 42 | none | 14931 | 2432 | 148 / 0 | 23.64% | 900.1 |
| STORE / 42 | coverage | 14656 | 2299 | 120 / 0 | 19.84% | 897.4 |
| LOAD / 1 | none | 24254 | 2633 | 97 / 0 | 11.14% | 952.1 |
| LOAD / 1 | coverage | 24988 | 2633 | 96 / 0 | 11.17% | 944.2 |
| LOAD / 42 | none | 24686 | 2688 | 91 / 0 | 9.48% | 996.8 |
| LOAD / 42 | coverage | 25769 | 2744 | 92 / 0 | 12.21% | 1032.1 |

合并两个初值时，新增桶数是两次运行各自增量的合计，已知时间占比使用服务时间加权，不把两个百分比直接相加：

| 场景 | 新增桶：基线→反馈 | 已知 emu 占比：基线→反馈 | 循环秒 / 千例：基线→反馈 |
| --- | --- | --- | --- |
| STORE | 4679→4498（-3.87%） | 22.06%→17.86% | 914.1→892.6 |
| LOAD | 5321→5377（+1.05%） | 10.29%→11.74% | 974.4→988.1 |

**收益目标未达，未调参重做。** STORE 的已知执行次数 453→373，但新增桶 4679→4498。LOAD 的新增桶 5321→5377，仅增加约 1.05%；已知执行次数 224→225，基本没有减少，已知问题耗时占比反而上升。两场景合计新增桶 10000→9875。

原因与证据：

- 分数只影响类和父输入，变异器仍按原有字段取值偏好生成，尚不会主动求解一个未见的 PPN 区域或字段桶。类的字段范围上界还包含不可达桶，因此“剩余比例高”未必意味着下一次容易增加覆盖。
- 已知问题位于类内的一部分输入。降低整个类的分数，也会减少该类其他桶的探索。STORE 初值 1 的实际命中类数 375→372，PPN 新桶 796→771，RSW 新桶 776→756；同轮 B 的已知命中 193→146，A 为 23→25。减少已知执行与降低部分覆盖同时发生，不能据此认为两项目标均通过。
- B 保留最近守卫距离优先，分数用于同距离候选；唯一最近邻即使分数低仍会被选中。反馈模式取消等额目标上限，保留加权；基线保留原上限。这些选择均在评估前确定，本轮没有做消融，不能把差异归因于其中某一项。
- LOAD 有 728 个初始类，950 次引导请求下，新条目再次作父输入仅 37/55 次；STORE 为 329/360 次。LOAD 的反馈学习和新父输入复用较少。共享主机上的具体输入成本和占用变化也进入耗时测量，不把墙钟差异全部归因于调度；LOAD 已知次数几乎没变，已经说明它未减少这一类执行。

96 例独立校准的循环为 92.0 秒，进程为 142.1 秒，按 8 路并行墙钟估算完整预算约 2.3 小时，因此保留全部 8000 例。正式八组进程墙钟合计 **8087.0 秒（约 2.25 小时）**；另有 96 例校准和 1000 例完整复现，不计入上表。三部分进程墙钟合计 **9225.7 秒（约 2.56 小时）**，仍低于约三小时；包含批间压缩和等待的总经过时间略长。emu 服务时间是并行实例各自 elapsed 之和，正式合计 38550.961 秒；它与整轮经过的墙钟不同。每轮完整 argv、原始退出码与进程耗时都在 `done.json`，详细服务时间在 `hardware-timing.jsonl`。

## 新分歧清单

**0 条。** `output/fuzz-step5/evaluation/new-disagreements.json` 为 `[]`。原始 1275 条不一致全部由既有 R-XS-001 归类，没有改规则。已知 cause 顺序为 Isla / XiangShan / NEMU：STORE 为 15 / 7 / 15，LOAD 为 13 / 5 / 13。本轮不作新的缺陷判定。逐例输入、认证输出、ELF、三方结果与压缩日志均保留。

## 验收结果

- **Rust：** `cargo test --workspace --offline -j 8` 最终为 1142 通过、0 失败、6 项既有忽略，保留原 1138 项并新增 4 项。新增测试覆盖类身份隔离、桶新颖性、已知与未知签名、降权及恢复、批次评分冻结、基础设施失败不构成新颖性。证据为 `test-workspace-final.log`。
- **TDD：** 调度缺接口、空桶基础设施和 DAG 确定性分别保留红测，修复后通过。最初一次筛选误选 bin 测试目标、实际运行 0 项，不作为红测证据。
- **Python：** 原有 127 项、worker 的 6 项通过。原有测试按用户指定目录只读执行，额外设置 `PAGING_TEST_OUTPUT_DIR` 与 `TMPDIR` 到本工作树，并禁用字节码写入；未修改或跳过测试。证据为 `python-existing-tests-final.log`、`python-new-tests.log`。
- **桶与血缘：** 八组各 1000 例逐条审计通过，覆盖增量、实际目标身份、认证、接纳条件、父引用、批次边界均一致。反馈新增 corpus entry 为 STORE 716/746、LOAD 813/823；实际使用新条目作父输入为 329/360、37/55。证据为 `functional-validation.json`。
- **确定性：** 最终模型模式的两个独立进程，根目录 21 个正式文件加 26 个 DAG，共 47 个产物，逐字段与逐字节相同。计时文件里的非耗时元数据也相同。完整硬件反馈的 1000 例重跑同样通过：根目录 24 个正式文件加 26 个 DAG，共 50 个产物逐字段、逐字节相同，耗时文件中的非耗时元数据相同。证据为 `hardware-determinism.json`。逐例原始运行目录和外层诊断日志保留来源路径与运行信息，确定性数据接口为 fuzz 根目录及 DAG。
- **进程：** 八个正式设置的 `remaining-processes.json` 均为 `[]`；1000 例完整复现及最终全目录检查也无所属进程残留，见 `remaining-processes-final.json`。超时与取消清理的原有 Rust/Python 测试照常通过。
- **Make：** `make solve-MRET THREADS=32` 的独立输出冒烟退出 0、4 条用例；保留既有 `partial / unfinished-paths=1` 和 Poison 提示。未跑全量 `make solve`。
- **构建与格式：** 离线 release 构建通过，`cargo fmt --all -- --check` 与 `git diff --check` 通过。

首个基线启动于 DAG 编号修复前，保留版本 1 文件；其余设置使用版本 2。26 条路径除 schema 版本和内部守卫编号外，原始定义、守卫及完整状态逐字段相同，见 `dag-format-only-change.json`。此次格式修复不改变变异、评分、认证或窄规则；最终版本的完整硬件确定性验收使用同一版本 2。

以上证据均在本工作树 `output/fuzz-step5/`。正式机器对照为 `evaluation/comparison.json`、合并结果为 `evaluation/aggregate.json`；完整交付记录为 `acceptance.json`（`complete=true`，但 `feedback_goals_met=false`）。原探索的 partial 和退出 1 原样保留，不把当前完成路径目录的闭环验收写成全域探索完成。

## 复现

从工作树根运行，所有输出目录使用新名字：

```sh
mkdir -p output/fuzz-step5/tmp
export TMPDIR="$PWD/output/fuzz-step5/tmp"
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
export PT_DECODE_DIR="$(realpath ../isla-enumerate/agents/path_merge_call_support/pt_decode)"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
python3 tools/fuzz/step5_evaluate.py run --output output/fuzz-step5/repro --budget 1000
python3 tools/fuzz/step5_evaluate.py report --output output/fuzz-step5/repro
python3 tools/fuzz/run_campaign.py --scenario sv39-store --budget 1000 \
  --random-seed 1 --threads 32 --executor difftest \
  --output output/fuzz-step5/repro-repeat --fuzz-feedback coverage \
  --fuzz-batch-size 64 --difftest-workers 8
python3 tools/fuzz/step5_validate.py --evaluation output/fuzz-step5/repro \
  --left output/fuzz-step5/repro/sv39-store-coverage-1 \
  --right output/fuzz-step5/repro-repeat --output output/fuzz-step5/repro-validation.json
export PAGING_TEST_OUTPUT_DIR="$PWD/output/fuzz-step5/python-tests-repro"
(cd ../replay-p0/difftest-xiangshan/tests && python3 -m unittest discover -s .)
```

单场景复现沿用 `tools/fuzz/run_campaign.py`，增加 `--fuzz-feedback coverage` 或 `none`、`--fuzz-batch-size 64`；连接硬件使用 `--executor difftest`。输入有效性由当前模型认证，比较使用 JSON 字段与必要的逐字节比较，不以平台或程序身份哈希作为有效性门槛；保留既有重放链的 ELF 来源记录。

## 未做与遗留

不做符号前态 U 态、跨路径形态 B、DAG 纯求值器、RTL 覆盖、可达桶穷举或新规则。完整类目录继续固定于场景；实际类缺失会直接终止。动态 corpus 在同一进程内扩充并落盘，尚无跨进程恢复这些同类多条目与血缘的入口；初始 `--fuzz-corpus` 仍使用每类一个代表的既有认证接口。字段范围上界会给不可达桶留下分数，类内字段与桶的选择仍沿用原有偏好；本轮未同时达成两项收益目标。扩大预算或直接选择未见桶能否改善，尚未验证。原探索排除域的 partial 和退出 1 保留。
