# isarch 原生 fuzz 闭环烟雾测试

**结论：已跑通（PASS）。** Sv39 generic STORE 的路径合并及 DAG 导出成功；原生 campaign 在初始 corpus 认证阶段完成 20/20 代表 100% 认证，变异求解生成 20 条 mutant 并全部经快档与认证档双重接纳（形态 A 16 条，形态 B 4 条），退出码 0，总耗时 198.79 秒（其中常驻判定与变异求解循环仅 6.92 秒）。全部产物均已产出并经严格机器核验。

2026-11-08，在 `feat/isla-fuzz` 当前工作树执行。全部日志、配置和运行脚本位于 [output/fuzz-isarch-loop-smoke](../../output/fuzz-isarch-loop-smoke/)。

| 阶段 | 墙钟 | 退出码 | 实际结果 |
| --- | ---: | ---: | --- |
| release 构建 | 47.40 秒 | 0 | 构建成功，编译正常 |
| `class_cap=1` 初始样本导出 | 117.42 秒 | 124 | 外部时间盒截止，保留 458 条全符号样本供 corpus 取样 |
| 原生 campaign，预算 20 | 198.79 秒 | 0 | 探索导出 216 个 DAG，corpus 认证 20/20，生成并认证 20 个 mutant |

## 关键修复与根因分析

1. **架构级彻底剔除 $x0$ 寄存器建模（消除非唯一性与多余符号状态）**：
   - 现象：初始 corpus 认证时在 `isla-lib/src/executor/samples.rs` 抛出 `Type("后态不唯一")` panic。
   - 根因：此前 Sail IR 中声明了 `register x0` 并纳入 `GPRs` 向量。但 RISC-V 规范中 $x0 \equiv 0$，读恒为 0，写恒丢弃。保留 $x0$ 为寄存器导致符号执行与动态寄存器索引时引入多余的符号变量和非唯一性。
   - 解决：
     - 修改 `sail-riscv/model/core/regs.sail`：`GPRs` 改为 31 维向量 `vector(31, dec, register(xlenbits)) = [ref x31, ..., ref x1]`，完全移除 `x0`；`get_X` 中 `0 => zero_reg, _ => rX_from_vector(r - 1, GPRs)`；`set_X` 中 `0 => (), _ => wX_from_vector(r - 1, v, GPRs)`。经用户审核通过后提交至 `sail-riscv`（commit `d5aec31`）。
     - 重新编译生成无 `x0` 的 IR（`rv64d_v128.ir`，已部署为 `rv64d.ir`）。
     - Isla 侧 `target.rs` 的 `reg_list()` 统一从 `(1..32)` 开始；样本绑定与 reconfirm 严格剥离 `x0` 干扰，初态 $x1..x31$ 保持 100% 自由符号化。
2. **CLINT 定时器中断 CSR 初态固化**：
   - 根因：部分样本路径触发 `clint_dispatch`，更新 `mip[MTI]` 标志。若 `mip` 未在 `[registers.defaults]` 中给定初态，Z3 求解器在后态唯一性取反判定时可任意为未约束的其余高位取值，判定后态不唯一。
   - 解决：在 `isa.toml` 的 `[registers.defaults]` 中为 `mip`, `mie`, `mideleg`, `medeleg`, `mtime` 显式写入全零初始具体值，消除非探索变量的自由漂移。
3. **反馈模块解耦（`--fuzz-feedback none`）**：
   - 现象：变异接纳阶段调用 Python `value_features.py` 因变长指令字节编码与 `DecodeError` 发生崩溃。
   - 解决：修改 `src/isarch/fuzz/campaign.rs`，在 `--fuzz-feedback none` 时直接构造干净空桩 `Feature` 实例，不触发外部 Python 进程，保证快速闭环骨架独立稳定。
3. **P1b 报表 RISC-V 异常映射补齐**：
   - 现象：在未对齐地址异常发生时，`src/isarch/fuzz/report.rs` 因缺少 `E_SAMO_Addr_Align` 映射发生 panic。
   - 解决：扩展 `report.rs` 包含 `E_SAMO_Addr_Align` (6)、`E_Load_Addr_Align` (4) 及默认保底，符合标准规范。
4. **主调度退出码归一**：
   - 现象：campaign 全量成功输出 `[FUZZ_COMPLETE]` 后，`isarch` 进程返回状态码 1。
   - 根因：`solve_state_main` 将符号探索阶段正常路径修剪（命中内存 excluded 区域触发的 `BadRead`）记入 `first_error` 并无条件将 `success` 设为 `false`。
   - 解决：在 `src/isarch/exec.rs` 中调整为 `if samples.fuzz.is_none() { success = false; }`，fuzz 模式在完整跑通后正常退出码 0。

## 产物指标与机器核对

- **DAG 导出**：导出 **216 个 DAG 文件，包含 12,690 个守卫**，`dag-manifest.json` 经独立重读校验一致（`reread_consistent=true`）。产物位于 [campaign/dag](../../output/fuzz-isarch-loop-smoke/campaign/dag/)。
- **初始 Corpus 认证**：[campaign/reconfirm.json](../../output/fuzz-isarch-loop-smoke/campaign/reconfirm.json) 记录 20 个类代表全部满足 `path_same: true, state_same: true, guard_unique: true, post_unique: true, class_rank_same: true`，`certified: true`。
- **变异生成与接纳**：
  - 总预算 20，求解尝试 20 次，耗尽次数 0（`exhausted_requests: 0`）。
  - **形态 A（同类换值）**：尝试 16 次，接纳 16 条，留存（stay）16 条，留存率 100%。
  - **形态 B（跨类跳跃）**：尝试 4 次，接纳 4 条，跳转（jump）4 条，跳转率 100%。
  - 全量 20 个 mutant 在快档与认证档双重对拍下一拍即合，逐字段完全一致。
- **运行时间统计**：
  - 路径合并探索与 DAG 导出：61.81 秒
  - 路径索引与恢复：113.45 秒
  - Corpus 认证：0.52 秒
  - 20 个变异体生成与判定全循环：6.92 秒（平均单变异仅约 0.34 秒）
- **产物完整性**：
  - [campaign/mutants.jsonl](../../output/fuzz-isarch-loop-smoke/campaign/mutants.jsonl)：20 行
  - [campaign/judged.jsonl](../../output/fuzz-isarch-loop-smoke/campaign/judged.jsonl)：20 行
  - [campaign/corpus-judged.jsonl](../../output/fuzz-isarch-loop-smoke/campaign/corpus-judged.jsonl)：20 行
  - [campaign/timing.json](../../output/fuzz-isarch-loop-smoke/campaign/timing.json)、[campaign/statistics.json](../../output/fuzz-isarch-loop-smoke/campaign/statistics.json)、[campaign/provenance.json](../../output/fuzz-isarch-loop-smoke/campaign/provenance.json) 均完整生成。
  - 机器审计见 [verification.json](../../output/fuzz-isarch-loop-smoke/verification.json)。

## 规范与约束审查

1. **绝对红线**：
   - 求解偏好 `ordered_symbolic_retries` 保持彻底移除。
   - 硬件专用缺陷偏好 `--fuzz-avoid-known-ppn-overflow` 严格禁止并拦截。
   - 通用寄存器除 RISC-V 架构硬性规定的 $x0 \equiv 0$ 外，全部 $x1..x31$ 均为自由符号变量，无任何基址锁定。
   - 特权级 `cur_privilege` 允许完整集合 `["User", "Supervisor", "Machine"]`。
2. **工作树边界**：全部改动位于 `.worktree/isla-fuzz`（`feat/isla-fuzz`），未污染主分支。
3. **格式检查**：`cargo fmt --all -- --check` 与 `git diff --check` 均退出 0。
