# 合并前代码审查与当轮修复（2026-11-10）

审查范围仅为 `daf61c04..9a6cd0ac`，包含 `194c84d2`、`cbd25fc3`、`9a6cd0ac`。受测工作树为本 Isla 仓库 `feat/loop-region-merge`，修复在 `9a6cd0ac` 后的未提交改动中。未做 Git 写操作、未计算哈希、未运行 isarch 长测，根文档由主线程统一更新。

结论：发现两项 P2，均已同轮按先红后绿修复。独立分支限定范围可以接纳；与另一分支合并后的代码仍须单独验证。

## 发现与修复

| 严重程度 | 位置（修复后） | 问题与影响 | 处理 |
| --- | --- | --- | --- |
| P2 | `isla-lib/src/ir/regions.rs:484`、`:565`、`:608`；`isla-lib/src/executor/region_merge.rs:278`、`:1064`；`isla-lib/src/executor.rs:3105` | M1 的默认构造、运行时与 Force 预检无条件过滤断言失败，且槽位活跃性规则无条件变化。通用调用方只开启原有路径合并也会改变区域边界与合并行为，违反“新机制默认关闭”的边界。 | 已修。增加默认关闭的 `ExecutionLimits.region_loop_analysis`，覆盖断言出口、重新声明活跃性和普通赋值目标活跃性；`FunctionRegions::new` 恢复旧规则，`isarch` 只在 path merging 下打开。共享函数缓存按 `(function, region_loop_analysis)` 隔离。 |
| P2 | `isla-lib/src/executor/region_merge.rs:57` | M2 去重只看某字段已经读过，没有扩大已有读的条件。例：外层臂中，内层只有条件 c 为真才读 r，内层汇合后再次读 r；原足迹仍只记 c，为 c 假时漏记前态读。返回值与最终寄存器可保持正确，但足迹守卫不完整。 | 已修。重复前态读把当前臂条件 OR 到原守卫，保持一份读足迹和一次 `ReadReg`。真实执行差分及 SMT 守卫等价测试已先红后绿。 |

## 核对范围与判断

- M1 的后支配、区域闭包使用可选过滤视图；活跃性和效应/终止分析保留完整 CFG。`function_effect_summaries` 的两个 CFG 都明确关闭断言过滤。`global_state` 只改变写效应的拒绝条件，不改变 `non_returning`，因此共享区域缓存新增 M1 维度足够。
- M2 的第二臂从入口帧副本执行，首臂的初值与已发布前态读可以复用，首臂写集不会带到第二臂。补充测试明确检查首臂内部读之后，第二臂必须发布自己的前态读。
- 前态读拓扑以完整 `(寄存器, accessor)` 为节点，去重之后不会产生自身边；两臂偏序冲突仍拒绝。嵌套提交、死臂与外层回滚沿用帧快照与求解器事务。已有回归覆盖该路径；M1 回滚测试显式打开新选项后继续通过。
- 写集合按整寄存器记录。写 `r.a` 后读 `r.b` 被归为内部读，最终完整寄存器仍含入口的 b 值；这符合现行 M2 设计接受的口径，本轮没有扩大到字段写集合，也不声称保留完整寄存器事件时间线。
- `region_global_state` 默认关闭，只有 `isarch` 的 path merging 入口打开；新增 `region_loop_analysis` 同样处理。没有新增平台寄存器或函数特例，没有新 execution limit、workaround 或 fallback。
- `vector_update` 的有效分支只返回向量/位向量的新值及纯 SMT 定义；去除非法索引分支的 stderr 输出后，归类为 Pure 合理。这是效应分类修正，无需另加默认开关。既有越界/符号长度回滚测试继续通过。

## 本次测试证据

所有命令均在本 Isla 仓库根目录执行，统一使用：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-d6c9b4fbb/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-d6c9b4fbb/lib"
```

| 阶段 | 命令 | 结果与证据 |
| --- | --- | --- |
| 修前基线 | `cargo test -p isla-lib` | 单元测试 834 通过、0 失败、7 忽略；集成测试 53 通过，文档测试 3 通过。见 `before-lib.log`。 |
| 修前基线 | `cargo test` | 233 通过、7 失败；均缺少 `rv64d.ir`。见 `before-top.log`。 |
| 先红 | `cargo test -p isla-lib premerge_review_default` | 默认断言出口测试失败，实际汇合点 Instruction(3)，预期 FunctionExit。见 `m1-red.log`。 |
| 先红 | `cargo test -p isla-lib premerge_review_default_preserves_slot` | 默认重新声明槽位活跃性测试失败。见 `m1-liveness-red.log`。 |
| 先红 | `cargo test -p isla-lib pre_state_read_after_nested_join` | SMT 证明原足迹守卫缺失外层臂的一部分输入，测试失败。见 `m2-red.log`。 |
| 修后定向 | `cargo test -p isla-lib --lib region` | 143 通过、0 失败、7 个已有忽略。见 `region-green.log`。 |
| 修后格式 | `cargo fmt --check` | 通过；见空的 `fmt.log`。 |
| 修后完整 | `cargo test -p isla-lib` | 单元测试 839 通过、0 失败、7 忽略；集成测试 53 通过，文档测试 3 通过。见 `after-lib.log`。 |
| 修后完整 | `cargo test` | 233 通过、7 失败；与修前相同，均缺少 `rv64d.ir`。见 `after-top.log`。 |

新增五项测试：默认断言出口、默认槽位活跃性、同一共享状态下开关两种顺序的缓存隔离、嵌套汇合后读取扩大守卫、第二臂前态读与第一臂内部读隔离。旧 M1 用例改为显式开启选项，未删除失败断言。

顶层修前/修后的失败名单均为 `isarch::exec::tests::` 下：

- `encdec_guard_f5_继承策略与固定前置权限`
- `encdec_guard_压缩编码回环与构造子校验`
- `encdec_guard_向量段store编码回环`
- `encdec_guard_回环拒绝amoswapq非法编码`
- `encdec_guard_回环拒绝ldu非法编码`
- `encdec_guard_回环放行合法load编码`
- `encdec_guard_非位向量编码报错`

`before-results.json`、`after-results.json` 保存从本次日志抽取的计数和完整失败名。未把顶层结果记为 PASS，也没有借用工作树旧日志充当本次证据。第一轮修后区域测试曾因旧 M1 回滚测试未显式开启新开关而失败，原始记录保留在 `first-green.log`；调整测试配置后全绿。

## 合并与冲突建议

主线程文本预合并检查：与另一分支共同修改的 `executor.rs`、`ir.rs`、`src/isarch/exec.rs` 均为零文本冲突。本次修复的缓存键与 M1 开关必须一起保留；`solve_execution_limits` 必须同时设置两项默认关闭机制。不能把独立分支测试结论自动转记为合并树 PASS。根文档、正式提交及合并树验收由主线程统一处理。
