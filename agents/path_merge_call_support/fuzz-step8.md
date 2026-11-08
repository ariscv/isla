# fuzz 第 8 步：引导避开已知 PPN 超宽区域

**选项完成：已知问题占 emu 服务时间由 27.28% 降至 0.05%。** 开启组 4000 例为 3999 agree、1 条不一致、1 条 R-XS-001、0 条新分歧；关闭组 4000 例为 2899 agree、1101 条不一致、1101 条 R-XS-001、0 条新分歧。两种初值、四场景均按每设置 500 例统计，真实运行失败为 0。覆盖下降如实列于下表。

## 选项和保留超宽的含义

新增 `--fuzz-avoid-known-ppn-overflow`，默认关闭。只影响分页形态 A/B；默认 5% 的 M1/M2/M5 编码空间对照仍走原来的记录池和独立随机流。Sail、标准行为、worker 三方比较和窄规则 R-XS-001 均保持原有实现。

变异器先在目标类约束下尝试让所有活动叶 PTE 的 `PTE[53:46]` 为零，不加入父值绑定和历史排重。可满足时，生成阶段采用这组偏好，并允许清除父 corpus entry 中对应的高位；非叶的这些位仍遵守原来的绑定。不可满足时，再确认原目标类可满足，显式撤下该请求的偏好，按原约束生成超宽值。后一个分支是设计要求的可满足性选择，不用于处理内部错误；SMT unknown/error 和不变量违反照常中止。

每个 A/B 的 `mutations.jsonl` 记录开关和 `ppn_overflow_retained_for_class`；`ppn-preference-summary.json` 记录请求总数及因类要求而保留超宽的请求数。一次请求只计一次，不把求解查询次数当作请求数，也不把父值或排重冲突误报为类要求。关闭选项时该计数为零。

分页偏好单独放在 `isla-lib/src/executor/sample_mutation_ppn.rs`，复用现有按位依赖：当前 Sv39/Sv48 LOAD/STORE 中参与守卫判定的 64 位读取为 PTE，普通数据读取不参与分页守卫。叶条件为读取活动、V=1、R/X 至少一位为 1，且排除 R=0/W=1；非叶、未活动读取和普通数据读取不施加高位清零。适用范围为本轮分页数据访问场景，没有声称能识别任意程序中的页表读取。

## 实验预算与比较口径

第 7 步四场景各 1000 例硬件进程合计约 86.3 分钟；本轮原计划需新增 12 组硬件运行，预计超过约三小时。32 例真实冒烟的循环为 32.6 秒、进程为 104.1 秒，支持保留缩小规模的决定。因此四场景、两个随机数初值、开关两种设置均按 **500 例**统计，每组 475 个 A/B、25 个编码空间对照。

初值 1 的关闭组复用第 7 步原有 1000 例结果，取编号 0–474 的 A/B 和 950–974 的对照；所有原件保留。其墙钟按原完整 1000 例测量报告，不冒称量到这个抽样子集的墙钟。初值 1 的两个设置不是逐输入配对：预算影响邻类额度，对照编号也不同；该限制须与结果一起阅读。初值 42 的开/关组均重新运行 500 例，另核对 25 个对照逐字段相同。

确定性验证选用初值 42，四场景的开/关设置各完整复跑 500 例；两种初值都再做一轮模型复跑的额外耗时超出本轮预算。初值 1 关闭组仍保留第 7 步已有确定性证据，本轮不再追加它的模型进程。`step8_evaluate.py` 默认 `--repeat-initial 42`，`repeat` 子命令可独立启动这组复跑。

反馈均为 `none`、批次 64、isarch `-T 32`、八路 emu、原 120 秒外限；硬件、探索及模型确定性复跑串行，不与本任务另一个 isarch 交叠。其他工作树只读，不做真 U 执行。

emu 已知问题时间占比按逐例 emu elapsed 服务时间相加后计算，分子只包括实际命中 R-XS-001 的实例；不同 worker 的时间可重叠，不等于整轮墙钟。桶沿用既有 `(完整类身份, PTE 层级, 字段, 取值桶)`，新增桶相对初始 corpus 计算。

## 真实对比结果

每行 500 例。原始不一致包含被规则归类的实例，规则命中不改算 agree；只有 R-XS-001 一条原有规则。

| 场景 | 初值 | 选项 | agree | 不一致 | R-XS-001 | 新分歧 | 已知 emu 时间占比 |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 1 | 关 | 412 | 88 | 88 | 0 | 17.24% |
| Sv39 LOAD | 1 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv39 LOAD | 42 | 关 | 414 | 86 | 86 | 0 | 17.02% |
| Sv39 LOAD | 42 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv39 STORE | 1 | 关 | 366 | 134 | 134 | 0 | 28.13% |
| Sv39 STORE | 1 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv39 STORE | 42 | 关 | 365 | 135 | 135 | 0 | 25.94% |
| Sv39 STORE | 42 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv48 LOAD | 1 | 关 | 349 | 151 | 151 | 0 | 29.98% |
| Sv48 LOAD | 1 | 开 | 499 | 1 | 1 | 0 | 0.38% |
| Sv48 LOAD | 42 | 关 | 346 | 154 | 154 | 0 | 30.37% |
| Sv48 LOAD | 42 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv48 STORE | 1 | 关 | 316 | 184 | 184 | 0 | 36.47% |
| Sv48 STORE | 1 | 开 | 500 | 0 | 0 | 0 | 0.00% |
| Sv48 STORE | 42 | 关 | 331 | 169 | 169 | 0 | 32.50% |
| Sv48 STORE | 42 | 开 | 500 | 0 | 0 | 0 | 0.00% |

| 场景 | 初值 | 选项 | 覆盖桶 | 新增桶 | 因类要求保留超宽请求 | 循环秒/千例 | 进程秒/千例 |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 1 | 关 | 12320 | 1290 | 0 | 1005.4 | 1146.7 |
| Sv39 LOAD | 1 | 开 | 12307 | 1257 | 0 | 963.4 | 1200.5 |
| Sv39 LOAD | 42 | 关 | 12326 | 1157 | 0 | 840.2 | 1085.4 |
| Sv39 LOAD | 42 | 开 | 12322 | 1132 | 0 | 843.4 | 1086.8 |
| Sv39 STORE | 1 | 关 | 13463 | 1440 | 0 | 1151.4 | 1230.8 |
| Sv39 STORE | 1 | 开 | 14714 | 1511 | 0 | 1033.5 | 1165.5 |
| Sv39 STORE | 42 | 关 | 14411 | 1686 | 0 | 845.4 | 973.5 |
| Sv39 STORE | 42 | 开 | 14408 | 1669 | 0 | 836.4 | 955.5 |
| Sv48 LOAD | 1 | 关 | 20186 | 1808 | 0 | 1175.9 | 1527.4 |
| Sv48 LOAD | 1 | 开 | 20274 | 1794 | 0 | 1071.7 | 1770.8 |
| Sv48 LOAD | 42 | 关 | 20522 | 1750 | 0 | 1023.2 | 1675.1 |
| Sv48 LOAD | 42 | 开 | 20521 | 1746 | 0 | 1033.2 | 1707.0 |
| Sv48 STORE | 1 | 关 | 20531 | 1979 | 0 | 1085.0 | 1271.3 |
| Sv48 STORE | 1 | 开 | 21235 | 1989 | 0 | 1163.8 | 1466.8 |
| Sv48 STORE | 42 | 关 | 21403 | 1851 | 0 | 995.9 | 1311.3 |
| Sv48 STORE | 42 | 开 | 21409 | 1840 | 0 | 1008.3 | 1301.2 |

初值 1 关闭组的墙钟来自历史完整 1000 例；其余行实测 500 例后折算每千例。循环墙钟包含生成、判定、认证和 worker，排除一次性探索、索引和 corpus 认证；进程墙钟包含这些阶段。共享主机上的墙钟差异不全部归因于选项。

| 场景 | 初值 | 物理地址 ≥2^48 的 PPN 桶：关→开 | 丢失的具体桶 | 增加的具体桶 |
| --- | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 1 | 176→13 | 659 | 646 |
| Sv39 LOAD | 42 | 161→10 | 218 | 214 |
| Sv39 STORE | 1 | 179→16 | 504 | 1755 |
| Sv39 STORE | 42 | 204→19 | 245 | 242 |
| Sv48 LOAD | 1 | 206→8 | 776 | 864 |
| Sv48 LOAD | 42 | 198→9 | 240 | 239 |
| Sv48 STORE | 1 | 199→11 | 1004 | 1708 |
| Sv48 STORE | 42 | 196→2 | 242 | 248 |

丢失与增加按完整类身份和原字段桶坐标逐项比较；总桶数持平或上升也可能丢失某些原桶。初值 1 两组调度不完全配对；初值 42 的四组各 475 个 A/B 目标序列与 25 个编码对照已逐字段核对一致。各字段和取值区域的完整增减在 `output/fuzz-step8/evaluation/coverage-deltas.json`。

正式开启组因类要求保留超宽共 0 请求；关闭组没有提交偏好请求，因此该计数为 0。强制要求 PTE 高位非零时仍可生成并认证的分支由新增单元测试覆盖。没有把父值绑定或排重导致的冲突计为类要求。

Sv48 LOAD、初值 1、开启组的编号 482 是 M2 编码对照，保留了超宽叶 PPN，三方 cause 为 13/5/13，仍被原规则计数。未屏蔽该输入，也未修改规则。

## 新分歧清单

**无。** 机器清单 `output/fuzz-step8/evaluation/new-disagreements.json` 为 `[]`。不把未观察到新分歧写成不存在缺陷。

## 确定性与测试

- 初值 42 四场景、开关两种状态共 8 次完整 500 例模型复跑，316 个正式文件逐字段及逐字节相同，包含 mutants、judged、mutations、classified、覆盖统计、PPN 请求统计及 DAG；未删除被比较文件的字段，未计算文件哈希。
- 全部 7600 个 A/B 命中目标类，且同目标类的字段取值组合、完整前态唯一比例均为 100%；各组的 475 个 A/B 原始前态与认证前态逐字段完全相同。
- `cargo test --workspace --offline -j 8`：1150 通过、0 失败、6 项既有忽略；保留第 7 步实际 1149 项并新增 1 项。新增测试包含 A/B、开关状态、目标类强制超宽、未活动读取、非叶、数据读取和确定性。
- 外部指定 Python 测试 142 项、本树 Python 测试 11 项全部通过。外部测试只读运行，输出与临时文件均在本树。新增两项测试检查历史抽样的 95:5 比例，以及对照里实际读取字节的严格核对。
- release 构建、`cargo fmt --all -- --check` 和 `git diff --check` 通过；独立目录 Make MRET 冒烟退出 0，保留原 partial/unfinished-paths=1 与 Poison 提示。未运行全量 `make solve`。
- 20 个正式新进程目录和独立冒烟的所属残留检查均为空；既有超时、取消、独立 emu 会话及 NEMU 回收测试照常通过。

新硬件进程墙钟合计 130.8 分钟，8 次模型复跑合计 34.2 分钟；前者不含第 7 步复用结果。完整命令与原始 isarch 退出码都在每组 `done.json`。

首次报表将 M5 对照编号 476 的所有初始内存字节要求为原样，因认证输出将不读取的初始字节记为 null 而失败；日志 `report-first-complete.log` 保留。修正报表以复用 `SamplePath::bind` 的读取语义：每个实际读取字节必须一致；额外初始化但不读取的字节不改变行为。新增回归测试验证真实读值不同仍会失败；没有改输入、认证档、worker 或规则。

旧驱动在启动时已加载两种初值都复跑的计划；调整为只复跑 42 后，使用新输出目录保护在第一个多余模型进程启动前终止旧计划。该驱动退出 1 的原件与 `repeat-plan.json` 保留，没有启动对应 isarch。随后用当前 `repeat` 子命令完成全部 8 次计划内复跑。此处为有意结束冗余调度，不计作真实 mutant 的运行失败。

## 产物与边界

机器验收为 `output/fuzz-step8/acceptance.json`；三方结果、输入、认证、PPN 请求计数、覆盖增减、确定性和进程检查均保留。基线为 `37dbbe32` 加本轮改动，没有 Git 写操作。

本轮没有每设置 1000 例、初值 1 的额外模型复跑、真 U 执行、E3 前态、跨完成路径形态 B、可达桶穷举或全量 `make solve`。原探索仍为 partial，Sv39 errors=5、Sv48 errors=7；没有把完成路径上的认证与闭环写成全域探索完成。PTE 识别适用于当前分页 LOAD/STORE，未扩展到任意程序。

## 验证与复现

所有命令在本工作树根执行；输出目录必须是新目录。环境沿用第 7 步官方 Z3，以下路径只读使用其他工作树。

```sh
mkdir -p output/fuzz-step8/tmp
export TMPDIR="$PWD/output/fuzz-step8/tmp"
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
export PT_DECODE_DIR="$(realpath ../isla-enumerate/agents/path_merge_call_support/pt_decode)"
export PAGING_TEST_OUTPUT_DIR="$PWD/output/fuzz-step8/python-existing-repro"
cargo fmt --all -- --check
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
python3 -m unittest discover -s tools/fuzz/tests
(cd ../replay-p0/difftest-xiangshan/tests && python3 -m unittest discover -s .)
python3 tools/fuzz/step8_evaluate.py run --output output/fuzz-step8/reproduce --budget 500
python3 tools/fuzz/step8_evaluate.py report --output output/fuzz-step8/reproduce --budget 500
```

单场景示例；去掉最后一个参数即关闭，使用另一个新输出目录：

```sh
python3 tools/fuzz/run_campaign.py --scenario sv39-store \
  --e2-experiment ../isla-sym-config/output/fuzz-step6a \
  --budget 500 --random-seed 42 --threads 32 --executor difftest \
  --output output/fuzz-step8/reproduce-store --fuzz-feedback none \
  --fuzz-batch-size 64 --difftest-workers 8 --certify-all \
  --fuzz-avoid-known-ppn-overflow
```
