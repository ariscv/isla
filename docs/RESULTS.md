# 验证记录

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
