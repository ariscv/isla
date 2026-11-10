# 初态语义配置迁移验收记录

已实现 `[constraints].initial`，全部初态注入后、首次可满足性检查前施加。矛盾初态沿用报错路径。

```toml
[symbolic_registers.cur_privilege]
allowed = ["Machine", "Supervisor", "User"]

[constraints]
initial = [
    "= ((_ extract 35 34) mstatus.bits) #b10",
    "= ((_ extract 33 32) mstatus.bits) #b10",
    "or (= ((_ extract 12 11) mstatus.bits) #b00) (= ((_ extract 12 11) mstatus.bits) #b01) (= ((_ extract 12 11) mstatus.bits) #b11)",
]
```

完整配置另含 VLEN=128、ELEN=64 的 RVV 普通域与 vill 域表达式；16 份 riscv64 系列配置声明一致，注释记录 Sail 源位置。

等价证明：删除前直接调用旧生产规则，合法域与 RVV 各自两个方向均为 unsat。删除后用测试专用旧规则参照重跑，两项仍通过。证据：equivalence-before-removal.log、after-top.log。

| 指令 | 参考状态／用例 | 本轮状态／用例 | 秒 |
| --- | --- | --- | ---: |
| RTYPE | finished／10 | finished／10 | 6.923 |
| C_LD | finished／8 | finished／8 | 10.833 |
| CSRReg | finished／859 | finished／859 | 77.886 |
| JALR | finished／1 | finished／1 | 4.625 |
| C_FLW | not-applicable／0 | not-applicable／0 | 1.414 |
| FLI_S | finished／16 | finished／16 | 8.327 |
| VSETVLI | finished／3 | finished／3 | 6.92 |

七项退出码均为 0、未完成路径均为 0，无 panic。串行执行、每次 -T 16；前六项外限 600 秒，VSETVLI 外限 300 秒。命令和独立输出在各指令子目录，汇总见 regression-results.json。
对比依据：/data1/baiyifan/workplace/isla-runner/agents/isarch_quick_failures_20261110/after-fix-20261110.md。
正式 Make 冒烟：make solve-MRET -o build-isarch THREADS=16，复用本轮 release 二进制；显式指定原始 IR，OUTER_TIMEOUT=10m，未设置 execution limit。结果 finished、4 用例、unfinished-paths=0。

改动文件：

- `README.md`
- `configs/riscv64.toml`
- `configs/riscv64_difftest.toml`
- `configs/riscv64_difftest_fd.toml`
- `configs/riscv64_difftest_mem.toml`
- `configs/riscv64_difftest_mem_excluded.toml`
- `configs/riscv64_difftest_mem_excluded_pma.toml`
- `configs/riscv64_difftest_mem_excluded_pma_csr_sym.toml`
- `configs/riscv64_difftest_mem_excluded_pma_csr_sym_vs.toml`
- `configs/riscv64_difftest_mem_excluded_pma_csr_sym_vs_t2.toml`
- `configs/riscv64_difftest_mem_excluded_pma_csr_sym_vs_vctx.toml`
- `configs/riscv64_difftest_mem_excluded_pma_csr_sym_vs_vh.toml`
- `configs/riscv64_difftest_mem_excluded_pma_sym.toml`
- `configs/riscv64_difftest_mem_excluded_pma_vh.toml`
- `configs/riscv64_difftest_vabs_v.toml`
- `configs/riscv64_memory_coverage.toml`
- `configs/riscv64_ubuntu.toml`
- `isla-lib/src/config.rs`
- `isla-lib/src/executor.rs`
- `isla-lib/src/init.rs`
- `isla-lib/src/ir.rs`
- `isla-lib/src/register.rs`
- `src/isarch/exec.rs`
- `src/isarch/platform.rs`
- `src/isarch/target.rs`
- `src/isarch_main.rs`
- `test/float_ir/runner/src/state.rs`
- `test/softfloat_legacy/runner/src/main.rs`
- `src/isarch/initial_constraints_tests.rs`

删除的硬编码：Rv64Domain、扩展能力探测、特权枚举白名单、SXL/UXL/MPP 字段规则、initial_state_rv64_domain 及默认值逻辑、RVV 合法组合推导和断言、domain_manifest 的模型能力与 Sail 来源字符串。
get_16_random_bits 的平台适配保持原逻辑；编码／译码映射名迁移已在 README 登记后续。

测试新增和修改：

- initial_constraints_share_reset_parser_and_validate_input：复用 reset 解析器，覆盖缺省、非法数组类型、非法表达式。
- initial_constraints_default_empty_and_independent_from_reset：替换旧库开关测试，验证新字段缺省为空、reset 与 initial 独立。
- configured_domain_equivalent_to_legacy_rules、configured_rvv_equivalent_to_legacy_rules：同一组自由符号，逐方向检查反例不可满足。
- vector_context_smt_constraint_accepts_only_legal_vtype_and_vl_pairs：改为读取配置规则，保留边界、保留编码、vill 的合法／非法组合检查。
- collector_rejects_unsatisfiable_prestate_instead_of_not_applicable、collector_reports_empty_encoding_domain_as_not_applicable：已有 collector 夹具改从 initial_constraints 施加限制，区分矛盾与不适用。
- 删除旧模型能力探测和旧开关测试；原规则的语义覆盖由等价证明承担。

失败名单对比：

- 基线确认为 c1559ad8，未做 Git 写操作。
- cargo fmt --check、git diff --check 均干净。
- cargo test -p isla-lib：基线 844 passed / 7 ignored → 当前 845 passed / 7 ignored；集成测试全通过。三个文档失败名单完全一致，均因 rustdoc 未继承 RUSTFLAGS、运行时加载 Z3 4.13.3.0。
- 为文档测试补充同值 RUSTDOCFLAGS 后，cargo test -p isla-lib --doc：3 passed / 0 failed。
- 顶层 cargo test：基线 241 passed / 7 failed → 当前 235 passed / 7 failed。测试数减少来自删除模型能力探测和旧开关测试、增加两项等价证明；新增失败为 0。
- 七项原有失败均因当前工作树根目录缺少 rv64d.ir；本轮语义回归通过 -A 使用现有原始 IR，未修改或复制 IR。

- `isarch::exec::tests::encdec_guard_f5_继承策略与固定前置权限`
- `isarch::exec::tests::encdec_guard_压缩编码回环与构造子校验`
- `isarch::exec::tests::encdec_guard_向量段store编码回环`
- `isarch::exec::tests::encdec_guard_回环拒绝amoswapq非法编码`
- `isarch::exec::tests::encdec_guard_回环拒绝ldu非法编码`
- `isarch::exec::tests::encdec_guard_回环放行合法load编码`
- `isarch::exec::tests::encdec_guard_非位向量编码报错`

构建和环境偏差：

- 所有构建使用用户给定的官方 Z3 RUSTFLAGS。指定 CARGO_TARGET_DIR=/data1/baiyifan/build/config-domain-target 的首次构建被沙箱只读文件系统拒绝（release-build.log）。
- release 实际目录为本工作树 target/config-domain-target，构建 -j 8；Make 通过 target/release/isarch 符号链接复用该二进制，未另行构建。
- 所有修改和输出均在指定工作树的 /data1 路径；未访问实测工作树 integration-run-20261110 的文件；未修改 Sail、原始 IR 或 isla-sail；未追加 execution limit 或 workaround；未计算哈希。
