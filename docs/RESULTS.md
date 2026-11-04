# 验证记录

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
