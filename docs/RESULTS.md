# 验证记录


## 2026-11-05 路径合并区域化推演（Sv39 LOAD 与函数级 pte_is_invalid）

受测版本：`feat/postprocess-enumeration` HEAD 36433cf；IR 为 `isla/.worktrees/memory-consistency/rv64d.ir`；Sv39 配置为 `.worktree/mmu-symbolic-experiment/symbolic/config.toml`（含 45 键 `[const_primops]`）。单次测量，未重复。

| 测量 | 命令要点 | 结果 |
| --- | --- | --- |
| 函数级 `pte_is_invalid` | `isla-execute-function`，带常量配置 `agents/path_merge_call_support/baseline_config_const.toml`，开关合并各一次 | 分叉 10 条 → 合并 1 条；23 项 Z3 检查通过；投影枚举 10 类 |
| Sv39 LOAD 开合并 | `isarch -T 1 --instruction-bits 0x0000b103 … --path-merging solve-state --clause=LOAD` | 20 秒（最近一次）完整结束，52 条路径，状态 finished，错误/超时/未完成均 0；合并 226 次尝试、175 次成功，51 次 `state_effect` 拒绝（经核对为联合类型构造子调用与列表模式匹配被静态摘要保守拒绝，不是访存；2026-11-06 更正）；合并记录 175 行 |
| Sv39 LOAD 不合并 | 同上去掉 `--path-merging`，外层 `timeout 1800` | 1800 秒未结束（退出码 124），已输出 8705 条路径，累计分叉 46085 次 |
| 单元测试 | `cargo test -p isla-lib --offline --features smt-thread-interrupt` | 682 通过、12 失败（与 HEAD 基线逐名相同）、2 忽略 |

限制：未做 Sv39 级覆盖等价性对照（分叉路径集合不完整）；耗时收益只有"能否跑完"的对比，没有同路径下的加速比；寄存器读取取并集，不适用于需要精确读写顺序的使用者。


## 2026-11-05 可选执行统计

受测版本：`feat/postprocess-enumeration`，基线 `dc76449` 加本轮统计及测试改动。起始工作树干净；rustc/Cargo 1.93.1。没有修改 IR 或模型，也没有运行 ISA 负载。

全部构建和测试使用以下环境，沿用官方 Z3 的链接目录、rpath 及 thread-interrupt feature：

```sh
export Z3_PREFIX="$HOME/.local/opt/z3-official-1fd1d3613"
export RUSTFLAGS="-L native=$Z3_PREFIX/lib -C link-arg=-Wl,-rpath,$Z3_PREFIX/lib"
```

每条构建或测试命令均用 `timeout 600` 限制。实际测试二进制经 ldd 核对链接到上述前缀中的 `libz3.so.5.3`。

| 命令 | 结果 | 日志 |
| --- | --- | --- |
| `timeout 600 cargo test --offline -p isla-lib path_merging_diamond_reduces_forks --features smt-thread-interrupt`（仅新增测试时） | 预期失败，退出 101：统计接口尚未实现 | [red](../agents/execution_stats/evidence/red.log) |
| 同上（实现后） | 通过，1/1 | [diamond](../agents/execution_stats/evidence/diamond.log) |
| `timeout 600 cargo check --offline --features smt-thread-interrupt` | 通过，退出 0；有既有代码警告 | [check](../agents/execution_stats/evidence/check.log) |
| `timeout 600 cargo test --offline -p isla-lib execution_stats --features smt-thread-interrupt` | 通过，2/2，覆盖禁用计数、多线程正确性及前 30 项 | [unit](../agents/execution_stats/evidence/unit.log) |
| `timeout 600 cargo test --offline -p isla-lib path_merging --features smt-thread-interrupt`（首次） | 3 通过、1 失败：新增的拒绝原因断言分类错误，原行为断言均通过 | [merging](../agents/execution_stats/evidence/merging.log) |
| 同上（修正断言） | 通过，4/4 | [merging-final](../agents/execution_stats/evidence/merging-final.log) |
| `timeout 600 cargo test --offline -p isla-lib multi_thread_read_mem_event_survives_fork --features smt-thread-interrupt` | 通过，1/1，真实子任务及函数名计数正确 | [multi](../agents/execution_stats/evidence/multi.log) |
| `timeout 600 cargo test --offline -p isla-lib monomorphize_enumerates_all_two_bit_models_with_three_path_forks --features smt-thread-interrupt` | 通过，1/1，四个模型对应三次实际分叉 | [monomorphize](../agents/execution_stats/evidence/monomorphize.log) |
| `timeout 600 cargo test --offline -p isla-lib review7_retry_preserves_finite_operand --features smt-thread-interrupt` | 通过，1/1，操作数重试分叉计数正确 | [retry](../agents/execution_stats/evidence/retry.log) |

`timeout 120 cargo fmt --all` 已执行；恢复了其对任务无关旧代码的排版，`git diff --check` 通过。最终共 9 个不同定向测试通过，没有全量测试。首次误分类依据：Decl 可在臂内模拟，单臂作用域差异在 `merge_two_frames` 返回 false，故应断言 `frame_merge_rejected`，不是 `then_arm_unsupported`。

未测：CLI 两行输出的动态验收及未设环境变量时完整输出对照、全部失败枚举、Sv39、release、make solve、性能收益及额外 feature 组合。本次不回答真实页表遍历是否触发合并。输出字段和范围见 [状态](../agents/execution_stats/status.md)。

## 2026-11-04 Review 36

受测基线：`985e0a93645367cdcb8fb10d5491adf494255802` 加本轮未提交修复。开始时目标工作树干净。审查补丁已成功应用，只新增 `tests/review36.rs`；补丁 SHA-256 为 `a4b612d09168d763f6ff5fbb05dcf66ef84683fe3af548a8869c942c830b783f`，测试文件 SHA-256 为 `e39a534c5f7ae6fcec14845878a54a9ff33a2386ae73004781398eb808f0c1a5`，与报告一致。范围见 [计划](../agents/review36/plan.md)。

工具：rustc 1.93.1、Cargo 1.93.1。测试程序实际链接系统动态库 `libz3.so.4`，调用该库 `Z3_get_full_version` 核对为 4.13.3.0。默认 debug，构建并行度 8；扩展验证使用 `itrace,smtperf`。日志位于系统临时目录，文件名如下，未覆盖审查人员的原日志。

| 阶段 | 命令 | 结果 | 日志文件名 |
| --- | --- | --- | --- |
| 仅应用复现补丁 | `cargo test -p isla --test review36 -j 8 -- --nocapture` | 退出 101：2 通过、6 失败，与审查一致 | `isla-review36-fix-before.log` |
| 首版修复 | 同上 | 8 通过，后续代码修订后须重新验证 | `isla-review36-fix-after.log` |
| 补充边界首轮 | `cargo test -p isla --test review36 --test review36_boundaries -j 8 -- --nocapture` | 审查 8 通过；补充 3 通过、3 失败：一个暴露 Concrete 遮蔽区域后读旧初值，另两个误把 SMT 定义事件当作内存事件；已补齐实现并使断言专门检查 ReadMem／WriteMem | `isla-review36-fix-final-repro.log` |
| 补充边界独立确认 | `cargo test -p isla --test review36_boundaries -j 8 -- --nocapture` | 同上 3 通过、3 失败；最终修订尚待后续结果 | `isla-review36-fix-shadow-before.log` |

首轮最终复验：审查 8/8（`isla-review36-final-repro.log`）、补充边界 6/6（`isla-review36-final-boundaries.log`）通过；`cargo test -p isla-lib --lib -j 8` 为 572 通过、2 失败（`isla-review36-final-lib.log`）。失败分别为 Review 23 对排除谓词旧表达式形状的断言，以及 Review 28 的旧不回绕区间预期。后者还包含 `u32::MAX` 长度，暴露逐字节生成约束不适合大长度，因此实现改为等价的模距离判断；预期改用两个不回绕区间独立计算，保留全部长度并新增零长度。Review 23 保留完整子域 SAT 验证，不绑定排除谓词内部形状。旧日志保留，最终复验另用新文件名。

模距离版定向核对的首轮失败仅发生在新增零长度的测试 oracle：将空区间误算为重叠（`isla-review36-modular-oracle.log`），已增加非零长度条件，生产实现的零长度直接返回真保持不变。随后最终核心库全量 574/574 通过（`isla-review36-verified-lib.log`）。要求的 Rust 测试及格式检查均通过；额外 MRET smoke 运行成功，但仍存在基线已有的 partial 边界。命令及结果如下。

| 命令 | 结果 | 日志文件名 |
| --- | --- | --- |
| `cargo test -p isla-lib --lib -j 8` | PASS：574/574 | `isla-review36-verified-lib.log` |
| `cargo test -p isla --test review36 -- --nocapture` | PASS：8/8 | `isla-review36-verified-repro.log` |
| `cargo test -p isla --test review36_boundaries -j 8 -- --nocapture` | PASS：6/6 | `isla-review36-verified-boundaries.log` |
| `cargo test -p isla --lib isarch::memory_model::tests -j 8` | PASS：33/33 | `isla-review36-verified-memory-model.log` |
| `cargo test --workspace -j 8` | PASS：累计 807 通过、0 失败、0 忽略，包含应用库 152、核心库 574、集成及文档测试 | `isla-review36-verified-workspace.log` |
| `cargo test -p isla-lib --lib --features itrace,smtperf -j 8` | PASS：637/637 | `isla-review36-verified-features.log` |
| `CARGO_BUILD_JOBS=8 make solve-MRET -j 1 THREADS=8` | 运行通过／覆盖有限：退出 0、4 条用例、diagnostics 为空，summary.partial、unfinished-paths=1 | `isla-review36-smoke.log`、`output/log/MRET.log` |
| `cargo fmt --check`、`git diff --check` | PASS：退出 0 | `isla-review36-fmt-check.log`、最终复核输出 |

以上套件统计有重叠，不能相加解释为独立覆盖。补充测试覆盖设备／RAM 混合域拆分前无写事件和无设备变更、129 位地址唯一低位分派、多字节生成器整区域合同、原始事件地址、全部切片宽度逐位 oracle、B64 全部宽度整数极值、32／64 位数组回绕的合法候选保留，以及区域遮蔽时的写后读。


MRET 使用 `smt-thread-interrupt` 构建，IR `rv64d.ir` SHA-256 为 `c65b26c8518042c67bfcb48c9feaf2a13a6eb7d741bc01ae8688d78c4370e5d9`，配置 `configs/riscv64_difftest.toml` SHA-256 为 `9a315cbcc83837a4a245a03a5f8d4c9c88d69622ffe1abb47777cb761b909fc2`。旧 `output/` 已保存在系统临时目录 `isla-review36-output-before.7r4qsoxr/output/`；新结果为 `output/rv64_zMRET.json`。逐字段核对备份中的旧 JSON：原本即为相同 summary（partial、1 条 unfinished、0 errors／timeouts）和 4 条 gen。新旧日志均包含 `zMRET` 返回 Poison 的模型 `_inner_error_` 路径；这是该 IR／配置已有的覆盖边界，不记为整 Clause 完整 PASS，不在 F1～F5 修复中改写模型。未生成新 IR，未执行全部 ISA clause 或硬件差异测试，未提交改动。

最终受测源码／新增测试 SHA-256（验证期间逐文件复核一致）：

| 文件 | SHA-256 |
| --- | --- |
| `isla-lib/src/memory.rs` | `7b817939cc2abdd797907a8d0e1f0ffab1d2026b03247754c1902754f6b5a4b6` |
| `isla-lib/src/bitvector.rs` | `e80cef0a088dd3e969d1676584cb666a4534663bc81db1df4ea486444578f59b` |
| `isla-lib/src/bitvector/b129.rs` | `a594e4774c1c8557b2b86968ddc43a40264d0f6dcefa0fe2456d75f3dc03e347` |
| `src/isarch/memory_model.rs` | `afc23aa609c43aa7e59846919ba109b053be8fa66fe4d569ba8f6e46f8feaee5` |
| `isla-lib/src/executor.rs` | `fb0a8585da5b4bc0e72a9b041ea03f8f350a65a656663adc096589d69a75c5ce` |
| `isla-lib/src/executor/tests/review28_tests.rs` | `c46847b99d8c165c3528e872e7ecec6865440f68816b7dfe117db152f06631c9` |
| `tests/review36.rs` | `e39a534c5f7ae6fcec14845878a54a9ff33a2386ae73004781398eb808f0c1a5` |
| `tests/review36_boundaries.rs` | `8695c256ddfecb9a32f8eaf9a7337c324cbd66dc92cadde268fbabb96d7059a1` |


## 2026-11-04 Review 35

受测基线：`ea45622cdd09ab6b9239d99d367fcd0a3e991d3c` 加本轮未提交修复。开始时工作树干净。审查全量测试补丁预检查与应用均成功，补丁 SHA-256：`96778c534fe93fc64ac89252be72537e1bbd1955e8ae56290dbe4464d58e282b`。范围见 [计划](../agents/review35/plan.md)。

工具：rustc 1.93.1、Cargo 1.93.1；测试程序实际动态链接系统 Z3 4.13.3.0，已按动态库实际路径调用版本接口核对。默认 feature，Cargo 构建并行度 8；扩展验证启用 `itrace,smtperf`，MRET 构建启用 `smt-thread-interrupt`。逐进程运行器指定 `CARGO_TARGET_DIR=target`，分别使用独立临时日志目录，未覆盖审查人员的原始日志。

| 阶段 | 命令 | 结果 | 临时日志文件名 |
| --- | --- | --- | --- |
| 仅应用复现补丁 | `python3 tests/review35_run.py` | 退出 1；20 项中 6 通过、14 失败，与报告一致 | `isla-review35-fix-before.log`，逐项目录 `isla-review35-fix-before` |
| 首版修复 | `cargo test -p isla-lib --lib -j 8 review35 -- --nocapture` | 9 通过、0 失败，后续修改须以最终复验为准 | `isla-review35-fix-core.log` |
| 补充测试初版 | `cargo test -p isla-lib --lib -j 8 boundary_regression_tests -- --nocapture` | 编译失败：临时闭包和编码字符串生命周期不足；已使用独立任务及字符串绑定修正 | `isla-review35-extra-before.log` |
| 补充测试修正后 | 同上 | 3 通过、1 失败；复现 REG_DEREF 未过滤整个 `_TLB`，随后补齐该入口 | `isla-review35-extra-before2.log` |
| 首轮全量回归 | `cargo test -p isla-lib --lib -j 8` | 6 项旧断言失败；Review 31 旧过滤断言所在多线程测试超过 3 分钟仍未结束，主动 SIGTERM 终止，不能记作全量完成 | `isla-review35-all-lib-first.log` |
| 最终修复及断言修订后 | `cargo test -p isla-lib --lib -j 8` | PASS：574 通过、0 失败 | `isla-review35-all-lib-final.log` |
| 最终复验 | `cargo test -p isla-lib --lib -j 8 review35 -- --nocapture` | PASS：9 通过、0 失败 | `isla-review35-core.log` |
| 最终复验 | `cargo test -p isla --test review35_memory -j 8 -- --nocapture` | PASS：11 通过、0 失败 | `isla-review35-memory.log` |
| 最终复验 | `cargo test -p isla --lib -j 8 isarch::memory_model::tests` | PASS：33 通过、0 失败 | `isla-review35-memory-model-final.log` |
| 最终逐进程复验 | `python3 tests/review35_run.py` | PASS：20 通过、0 失败 | `isla-review35-runner-final.log`，逐项目录 `isla-review35-fix-final` |
| 扩展 feature 全量 | `cargo test -p isla-lib --lib --features itrace,smtperf -j 8` | PASS：637 通过、0 失败 | `isla-review35-features.log` |
| 应用库全量 | `cargo test -p isla --lib -j 8` | PASS：152 通过、0 失败 | `isla-review35-all-isla.log` |
| MRET smoke | `CARGO_BUILD_JOBS=8 make solve-MRET -j 1 THREADS=8` | PASS：退出 0，产出 4 条用例 | `isla-review35-smoke.log`，仓库 `output/log/MRET.log` |
| 最终格式 | `cargo fmt`、`cargo fmt --check`、`git diff --check` | PASS：全部退出 0 | 无独立日志 |

旧断言修订依据：Review 11 越界切片更新现在必须返回 OutOfBounds；Review 8 的向量值验证先检查混合域请求拆分及非法候选仍可满足，再显式限定合法域；Review 9 的递归元素值验证明确限定合法域，独立复现测试检查越界分叉。符号构造子旧测试对不确定标签改为检查 RetryCondition 及两侧均可满足。Review 24／28／31／32 的寄存器读取预期统一为精确 `_TLB` 过滤，保留其事件顺序、数量和路径覆盖检查。

五项补充核心测试覆盖：直接／字段解包在 0／1／4 worker 下保留互斥成功与 Type 错误路径且只读一次；三种切片入口的具体／符号数据边界；位更新与表达式切片保留越界路径；REG_DEREF 和单候选符号寄存器向量的精确过滤；末尾空更新及超长更新。新增内存模型测试覆盖 32／64／65／129／1024 位地址、多字节初值、宽地址写后通过具体 64 位地址读回，以及读写事件保留原始地址。

MRET 使用 `rv64d.ir`（SHA-256 `c65b26c8518042c67bfcb48c9feaf2a13a6eb7d741bc01ae8688d78c4370e5d9`）和 `configs/riscv64_difftest.toml`（SHA-256 `9a315cbcc83837a4a245a03a5f8d4c9c88d69622ffe1abb47777cb761b909fc2`）。旧 `output/` 已移至系统临时目录 `isla-review35-output-before.bcd_jnrz/output/` 保存。未生成新 IR，未执行全部 ISA clause 或硬件差异测试，未提交改动。

最终源码 SHA-256：

| 文件 | SHA-256 |
| --- | --- |
| `isla-lib/src/error.rs` | `cc3910b71376bb440bcfb56d80ceaea53f78e1e3e8ea0818d7a4050426a4d771` |
| `isla-lib/src/executor.rs` | `68d94472bbd9dcdcd837bb4cb280e652b53292524015eb11faf849c4585a9da8` |
| `isla-lib/src/executor/symbolic_length.rs` | `72d72a329679dd14f94b9c8d2397877cf576ed1ce150a024cc7db29c3165bf7d` |
| `isla-lib/src/primop.rs` | `5b28aa5d0c88878958abf12396e15a2d1590e6e02da44a6714dd0516d8e01a01` |
| `src/isarch/memory_model.rs` | `56746f9c4c62611fbbbaf08b21bda382fb2150fc51980bfeda2c20ba1e79fbd7` |

## 2026-11-04 Review 34

受测基线：`e88842fb2ecd5c6ec367598ff7e700667722784b` 加本轮未提交修复。开始时工作树干净，审查测试补丁已成功应用，补丁 SHA-256 为 `56c8e3c629a4e2356014338a5f58ac6800bc239f285204eb95ef9ec8ad169dc1`。计划见 [Review 34](../agents/review34/plan.md)。

工具：rustc 1.93.1、Cargo 1.93.1；测试可执行文件动态链接系统 Z3 4.13.3.0（已读取实际库版本），与审查人员使用的 Z3 4.16.0 不同。默认 feature，构建并行度 8；MRET 构建另启用 `smt-thread-interrupt`。

| 阶段 | 命令 | 结果 | 日志文件名（临时目录） |
| --- | --- | --- | --- |
| 仅应用复现补丁 | `cargo test -p isla-lib --lib -j 8 review34 -- --nocapture` | 退出 101；3 失败，直接解包、字段解包和向量越界均复现 | `isla-r34-before-lib.log` |
| 实施中的首次内存尝试 | `cargo test -p isla --test review34_memory -j 8 -- --nocapture` | 编译失败：新增约束表达式括号错误，随后已修正；该次运行不能作为修复前内存语义验证 | `isla-r34-before-memory.log` |
| 初版修复与事务测试 | `cargo test -p isla-lib --lib -j 8 review34 -- --nocapture` | 4 通过；审查的三个核心引擎反例及事务隔离通过，后续新增测试仍须复验 | `isla-r34-lib.log` |
| 补充位向量测试初版 | `cargo test -p isla-lib --lib -j 8 review34 -- --nocapture` | 5 通过、1 失败；新增测试误要求具体返回表示，已改为用求解器证明成功值为零，仍检查越界路径数 | `isla-r34-lib-final.log` |
| 首轮全量回归 | `cargo test -p isla-lib --lib -j 8` | 558 通过、2 失败；旧宽度测试未预先限定合法索引，旧操作数缓存测试未处理现已保留的越界错误路径 | `isla-r34-all-lib.log` |
| 旧测试修订中的编译检查 | `cargo test -p isla-lib --lib -j 8` | 编译失败：诊断分支尝试格式化未实现 Debug 的 Run；已改为分别处理错误、结束值和未结束状态 | `isla-r34-all-lib-final.log` |
| 最终测试修订后 | `cargo test -p isla-lib --lib -j 8 review34 -- --nocapture` | PASS：7 通过、0 失败 | `isla-r34-review34-confirmed.log` |
| 最终测试修订后 | `cargo test -p isla --test review34_memory -j 8 -- --nocapture` | PASS：1 通过；关闭／开启合流都只能读出零，事件区域均为 concrete | `isla-r34-memory-verified.log` |
| 最终测试修订后 | `cargo test -p isla-lib --lib -j 8 review33 -- --nocapture` | PASS：10 通过；该筛选也包含 review33_tests 模块中的新增 Review 34 测试 | `isla-r34-review33-confirmed.log` |
| 最终测试修订后 | `cargo test -p isla --lib -j 8 isarch::memory_model::tests -- --nocapture` | PASS：32 通过，包含具体初值、0xa5 写后读与具体／符号地址一致性 | `isla-r34-memory-model-verified.log` |
| 最终测试修订后 | `cargo test -p isla-lib --lib -j 8` | PASS：560 通过、0 失败 | `isla-r34-all-lib-final2.log` |
| 最终测试修订后 | `cargo test -p isla --lib -j 8` | PASS：151 通过、0 失败 | `isla-r34-all-isla-verified.log` |
| 扩展 feature | `cargo test -p isla-lib --lib --features itrace,smtperf -j 8 review34 -- --nocapture` | PASS：7 通过、0 失败，最终旧测试修订后已复验 | `isla-r34-features-verified.log` |
| 扩展 feature 全量单元 | `cargo test -p isla-lib --lib --features itrace,smtperf -j 8` | PASS：623 通过、0 失败 | `isla-r34-all-features.log` |
| MRET smoke | `CARGO_BUILD_JOBS=8 make solve-MRET -j 1 THREADS=8` | PASS：退出码 0，产出 4 条用例 | `isla-r34-smoke.log`、仓库 `output/log/MRET.log` |
| 格式检查 | `cargo fmt`、`cargo fmt --check`、`git diff --check` | PASS：均退出码 0 | 无独立日志 |

MRET 使用 `rv64d.ir`（SHA-256 `c65b26c8518042c67bfcb48c9feaf2a13a6eb7d741bc01ae8688d78c4370e5d9`）及 `configs/riscv64_difftest.toml`（SHA-256 `9a315cbcc83837a4a245a03a5f8d4c9c88d69622ffe1abb47777cb761b909fc2`）。既有 `output/` 已完整备份至临时目录 `isla-r34-output-before.ke76mpxg/output/`，未删除历史产物。本轮未重新生成 IR，未执行全部 ISA clause 或硬件差异测试。

旧测试修订保留验证强度：宽度测试在访问前明确约束合法索引，操作数缓存测试同时要求成功宽度为 8／16 且出现一条 `OutOfBounds`；具体零快照测试以 SMT 证明返回值只能为零，适应普通具体读改走共享数组后的符号表示。诊断格式的同一次编译错误也出现在 `isla-r34-review34-lib-verified.log` 和 `isla-r34-review33-lib-verified.log`；最终结果以表中的 confirmed 日志为准。MRET 之后只修订测试断言，生产逻辑未变。

最终文件 SHA-256（`executor.rs` 同时包含最后修订的测试）：

| 文件 | SHA-256 |
| --- | --- |
| `isla-lib/src/executor.rs` | `0299bd031c8c92c84ea2a44193654310ce128d8ef22c945c5c7761191ca7ee1f` |
| `isla-lib/src/executor/symbolic_length.rs` | `2a5ae83fa9b8c24746f442f043dbb84e1c7dfff03de0f4f6f65b5401df11d760` |
| `isla-lib/src/memory.rs` | `1571a3ec2f6a0a1dc1c94e61baebfc1e360ecfa07336bc1913c81ad66fb61691` |
| `isla-lib/src/primop.rs` | `8eb8a95b95a3af21f172e3ef549fd020a50c9821eab56fc78e110fef589b21cc` |
| `isla-lib/src/smt.rs` | `fb85c7d14c9163fd2e2dc6c2cd317356a3bf5375cf6666de57febcc13aa40fd0` |
| `src/isarch/memory_model.rs` | `ae717dd24c2595ae97b67e448e445c6ff6233bec09d6d1db68fc16628ec7bc9d` |

## 2026-11-04 Review 33

受测基线：`7ff465024ab1c7a0ffccc9133cac299fa7103680`；默认 feature；复现补丁仅增加测试。补丁预检查和应用均成功，应用前目标工作树干净。

工具：rustc 1.93.1、Cargo 1.93.1、Z3 4.16.0；构建并行度 16。实现计划见 [Review 33](../agents/review33/plan.md)。

| 阶段 | 命令 | 结果 | 日志文件名（系统临时目录） |
| --- | --- | --- | --- |
| 仅应用复现补丁 | `cargo test -p isla-lib --lib -j 16 review33 -- --nocapture` | 1 通过、3 失败；构造子错误路径丢失及普通读提前返回 SymbolicLength | `isla-review33-fix-before-lib.log` |
| 仅应用复现补丁 | `cargo test -p isla --lib -j 16 review33_自约束数组在具体区域内必须保持符号写后读一致性 -- --nocapture` | 0 通过、1 失败；读值不等于 0xa5 的查询为 Sat | `isla-review33-fix-before-array.log` |
| 两项生产修复后 | `cargo test -p isla-lib --lib -j 16 review33 -- --nocapture` | PASS：4 通过、0 失败 | `isla-review33-fix-lib.log` |
| 两项生产修复后 | `cargo test -p isla-lib --lib -j 16` | PASS：553 通过、0 失败 | `isla-review33-fix-all-lib.log` |
| 两项生产修复后、修订旧断言前 | `cargo test -p isla --lib -j 16 isarch::memory_model::tests -- --nocapture` | 30 通过、1 失败；新增数组写后读已通过，唯一失败是旧写侧错误类型断言 | `isla-review33-fix-memory-integration.log` |
| 最终测试断言修订后 | `cargo test -p isla --lib -j 16 isarch::memory_model::tests -- --nocapture` | PASS：31 通过、0 失败，包含 0xa5 写后读一致性回归 | `isla-review33-fix-memory-integration-final.log` |
| 最终测试断言修订后 | `cargo test -p isla --lib -j 16` | PASS：150 通过、0 失败 | `isla-review33-fix-all-isla.log` |
| 两项生产修复后 | `CARGO_BUILD_JOBS=16 make solve-MRET -j 1 THREADS=16` | PASS：退出码 0，产出 4 条用例；构建启用 `smt-thread-interrupt` | `isla-review33-fix-smoke.log`、仓库 `output/log/MRET.log` |
| 最终格式检查 | `cargo fmt`、`cargo fmt --check`、`git diff --check` | PASS：均退出码 0 | 无独立日志 |

旧测试 `默认内存保留具体区域重叠写入错误` 仍期待 `BadWrite("possible symbolic address overlap")`，而基线的 `Memory::write` 已使用 `SymbolicLength("write_mem_address", …)` 请求地址拆分。本轮更新该测试以精确检查现行错误类型，并检查重试前不提交 `WriteMem`；未修改写侧运行时逻辑。

受测实现是基线加本轮未提交改动。生产文件 SHA-256：`isla-lib/src/executor.rs` 为 `2bd9c77ba02c0f1b37f4672baa08df8562714064b1ce7899478577918ca01492`，`isla-lib/src/memory.rs` 为 `908b142a50e8302be92a58e14d6329898e87c1e2d412306933e51384b8119e54`。后续测试断言修订未改动这两个文件。

MRET 使用默认 `rv64d.ir`（SHA-256 `c65b26c8518042c67bfcb48c9feaf2a13a6eb7d741bc01ae8688d78c4370e5d9`）及 `configs/riscv64_difftest.toml`（SHA-256 `9a315cbcc83837a4a245a03a5f8d4c9c88d69622ffe1abb47777cb761b909fc2`），未重新生成 IR。既有 `output/` 已在运行前复制到系统临时目录 `isla-review33-fix-output-before/` 留存；本次 smoke 不代表全部 ISA clause 验收。


## 2026-11-06：枚举分量诊断（edee95d + 未提交诊断，测量完成）

只写指定 isla-enumerate 独立工作树；使用用户指定 scratchpad/target_f7 release 二进制，ISLA_ENUM_COMPONENTS=1、count/class_cap=1/path_cap=1000000、-T 64，前态与 x_cmd2.sh 一致。

| 场景 | 退出／耗时 | 完成路径／守卫类 | 结果 |
| --- | --- | --- | --- |
| Sv39 LOAD，satp=0x8000000000080200 | 0／49s | 20／16592 | 原约束图 1 分量／路径；候选 1–10 分量，20 条路径守卫域乘积均相等 |
| Sv48 LOAD，satp=0x9000000000080200 | 0／454s | 27／122654 | 原约束图 1 分量／路径；候选 1–12 分量，6 条路径乘积不等且有 UNSAT 缺失组合 |
| Sv48 STORE，0x0020b023、clause=STORE | 0／97s | 27／51638 | 原约束图 1 分量／路径；候选 1–11 分量，6 条路径乘积不等且有 UNSAT 缺失组合 |

全部 path_truncated=false；片段类内域并未完整枚举。两两／全分量抽样 SAT 查询分别为 5841/1024、14411/1472、14081/1472；Sv39 全部 SAT，LOAD Sv48 各有 1 个 UNSAT，STORE 抽样全部 SAT 但明确缺失组合有 6 个 UNSAT。只完成测量和设计，无生产加速或离线展开实现。

3 项诊断测试通过；最终开启诊断的 isla-lib 全量 **709 通过、12 失败、6 忽略**，与 `output/stride-validation/full-lib-final-default.log` 逐名比较无新增／缺失失败项。cargo fmt、cargo fmt --check、git diff --check 和指定 target_f7 release 构建通过。原始证据为指定 scratchpad/components/final/ 三场景及 full-lib-final-enabled.log；[受测哈希和全部路径机器记录](../agents/path_merge_call_support/component-results.json)、[前六条胖路径与设计](../agents/path_merge_call_support/enumeration.md)、[当前状态](../agents/path_merge_call_support/status.md)。

## 2026-11-07 judge 模式（ae1a335 加本轮未提交改动）

格式化、release 构建及 `cargo test --workspace --offline -j 8` 通过：1108 通过、0 失败、6 项既有忽略。基线新 IR 与配置只读沿用 replay-p0/ecfg4b；四场景 2836 种子的路径唯一接纳、指定后态字段相同、守卫和后态唯一、守卫向量排序类号、J1 新旧完整报告一致五项全部通过，生成的 2836 行完整样本外部再喂入 J1 也全部通过。三个负对照各接纳 0 条路径。

保留原始退出 1、partial 和 errors=5/5/7/7，本轮未重做旧观察器的排除域逐查询证明；四场景无超时或未完成路径。Make MRET 退出 0、4 条，保留既有 unfinished=1。没有修改其他工作树或执行 git 写操作。完整命令、逐项结果、限制及日志位置见 [judge 说明](../agents/path_merge_call_support/judge-mode.md)，机器结果为 `output/judge/verification.json`。
