# 快速失败分支审查与修复

本轮确认并修复三个 P2 问题。通用库恢复原有默认行为；RISC-V 平台接口只在 isarch 接入；矛盾前态不再被写成“不适用”。完整库测试通过，顶层测试仍被七个既有的缺 IR 夹具阻断。

## 审查范围

- 受审提交：`daf61c04..9a4f5c91`，修复保留为当前工作树未提交内容。
- 写入范围：本工作树源码、README 和本目录证据。根文档及另一工作树未修改。
- 原 `diag/` 保留，`target` 仍指向原 `diag/build`；没有 Git 写操作，没有计算哈希。
- 不审历史实现；LOAD_FP 的 IR 类型约束缺失、浮点 helper 和 CPOP/CPOPW 既有未完成事项继续保留，不纳入本轮修复。

## 问题与修法

| 严重程度 | 问题及影响 | 状态 | 现行修复位置 |
| --- | --- | --- | --- |
| P2 | `ISAConfig` 将 `initial_state_rv64_domain` 缺省改为 true，改变所有调用方；README 仍声明默认关闭。 | 已修 | [config.rs](../../isla-lib/src/config.rs#L2734) 恢复 false；[isarch_main.rs](../../src/isarch_main.rs#L588) 单独启用 isarch 缺省；[platform.rs](../../src/isarch/platform.rs#L7) 保留显式 false；[README](../../README.md#L677) 同步说明。 |
| P2 | 通用加载器把所有同名无体 `Def::Val` 自动转换为注册原语，例如未声明 extern 的 `undefined_bool` 被替换；RISC-V `get_16_random_bits` 也进入全局注册表。 | 已修 | [ir.rs](../../isla-lib/src/ir.rs#L1443) 恢复只按显式 extern 接线；从通用原语和 effects 表移除该平台函数；[platform.rs](../../src/isarch/platform.rs#L11) 仅在 isarch 适配。 |
| P2 | 初态约束自身不可满足时，编码结果同样为空，原实现会误写 `not-applicable`。配置冲突因此被成功退出遮住。 | 已修 | [exec.rs](../../src/isarch/exec.rs#L1829) 先检查初态可满足性；Unsat 报错，Unknown/SMT 错误继续传播；[solve_summary.rs](../../src/isarch/solve_summary.rs#L45) 给不适用结果增加范围说明。 |

平台适配复用已有 `ISAConfig.const_primops`、动态 `Reset` 和 `WritesState`。无体 val 转成 extern，显式 extern 使用相同通道；每次调用声明新的自由 16 位符号值。已有模型函数体和未知平台声明保持原样，用户已配置的原语值也不被默认适配覆盖。新增测试同时检查真实加载器产生 `PrimopReset`，避免只测试闭包而漏掉接线。

## 通用性和正确性判断

- 通用库已有 `platform_read_mem`、`platform_write_mem`、分支通知和 cycle 计数等外部原语。这些表达可跨架构使用的概念，不能据此把 RISC-V 熵接口名称加入通用表。当前局部适配足够，不增加注册框架或通用函数名特例。
- RV64 合法初态域仍复用既有 `Rv64Domain`；S/U/H 能力通过模型 `zhartSupports` 探测，不按 clause 名称限制前态。运行态 FS/VS、特权和其他字段仍保留合法取值范围。
- 运行时 Z3 检查放在统一 `Context::new`，每进程检查一次，最低四元版本号为 5.4.0.0。所有实际建立 Z3 上下文的可执行程序都会生效；没有使用仅 isarch 的检测。该位置和失败即 panic 符合要求，保持不改。
- 编码探查前已安装数组内存声明，并完成初态、符号 CSR 和 PMA 边界约束；初始 memory 对象稍后装入执行帧。编码候选重新带回完整执行约束校验，未发现该顺序丢失现有约束。
- `not-applicable` 仅说明本次配置、前态和输入约束域没有合法编码。一个 clause 在其他配置中仍可适用。新增 `scope=current-config-prestate-and-input-domain`，保留原 reason，便于已有消费者兼容。
- 正常／压缩编码的原优先关系、合法编码多见证、ExecuteAs 续执行、完整执行约束校验相关测试保持通过。没有 clause 白名单，没有新增 fallback、execution limit、workaround、有序重试、PPN 规避、固定 x1 或 Sail 标准行为改动；nat 不变量断言保留。

## TDD 证据

| 测试 | 修前 | 修后 | 证据 |
| --- | --- | --- | --- |
| 通用库缺省域关闭 | 缺省实际 true，断言失败 | false/true/false 三种配置通过 | [修前](tdd-config-before.log)、[修后](tdd-lib-after.log) |
| 无体同名 val 保留调用、通用表不含 RISC-V 熵接口 | 两项失败 | 两项通过 | [修前](tdd-before.log)、[修后](tdd-lib-after.log) |
| isarch 局部熵适配 | 未适配的声明测试失败 | 平台四项通过：缺省覆盖、独立自由 16 位值、加载器副作用通道、保留已有函数体/未知声明 | [修前](tdd-platform-before.log)、[修后](tdd-platform-after.log) |
| 矛盾初态不冒充不适用 | collector 断言失败 | collector 明确返回错误 | [修前](tdd-prestate-before.log)、[修后](tdd-prestate-after.log) |

第一版配置测试夹具把要求字符串的地址字段写成数字，最初因夹具错误提前失败；修正后 [tdd-config-before.log](tdd-config-before.log) 才记录实际默认值回归。此夹具错误不计入生产缺陷。

## 完整验证

受测代码为 `9a4f5c91` 加本轮未提交修复。所有测试使用：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-d6c9b4fbb/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-d6c9b4fbb/lib"
cargo fmt --check
cargo test -p isla-lib
cargo test
```

| 命令 | 修前 | 修后 |
| --- | --- | --- |
| `cargo fmt --check` | 未单独运行 | 退出 0，见 [格式记录](after-fmt.log) |
| `cargo test -p isla-lib` | 单元 815 通过、6 忽略；53 集成通过；3 doctest 因加载系统 Z3 4.13.3 而失败，退出 101 | 增加下述 `RUSTDOCFLAGS` 后完整退出 0：814 单元、53 集成、3 doctest 全通过，6 忽略 |
| 顶层 `cargo test` | 235 通过、7 个缺 IR 失败，退出 101 | 240 通过、同样 7 个缺 IR 失败，退出 101 |

Cargo 的 rustdoc 子进程没有继承普通 rustc 的链接参数；仅增加 `LD_LIBRARY_PATH` 也没有解决加载系统库的问题。环境修正为：

```sh
export RUSTDOCFLAGS="$RUSTFLAGS"
cargo test -p isla-lib
```

没有为通过测试而放宽版本检测。库单元数量变化来自删除通用库中的平台专用测试，并把相应验证移到 isarch；新增通用库隔离回归仍保留。

完整日志：[修前库](before-isla-lib.log)、[修前顶层](before-workspace.log)、[修后首次库](after-isla-lib.log)、[修正 rustdoc 环境后的完整库](after-isla-lib-rustdocflags.log)、[修后顶层](after-workspace.log)、[退出码说明](after-exit-codes.txt)。

七个失败测试保持如下，均在 [exec.rs](../../src/isarch/exec.rs#L4759) 读取缺少的 `rv64d.ir` 时失败：

- `encdec_guard_f5_继承策略与固定前置权限`
- `encdec_guard_压缩编码回环与构造子校验`
- `encdec_guard_向量段store编码回环`
- `encdec_guard_回环拒绝amoswapq非法编码`
- `encdec_guard_回环拒绝ldu非法编码`
- `encdec_guard_回环放行合法load编码`
- `encdec_guard_非位向量编码报错`

本轮未补 IR、未跳过或删除这些既有测试，因此不能宣称顶层测试全通过。没有运行 isarch clause 长测，也不把旧 clause PASS 改署到修复后的代码。

## 合流建议与可复用发现

保留本轮 `src/isarch/platform.rs` 新文件及 `src/isarch_main.rs` 的初始化接线。它经 `PrimopReset/WritesState` 进入现有执行机制，与循环区域合并分支的 `vector_update` 副作用分类互不替代，应分别保留。其他分支若也修改 `ISAConfig`、平台函数注册或不适用摘要，按以上职责边界合并，避免恢复全局 val 猜测接线或通用缺省 true。

可供主线程同步到根发现记录的事实：`const_primops` 虽名为常量原语，其值实际可为动态 `Reset`，能安全表达每次调用的新鲜符号值并携带副作用分类；rustdoc 的 Z3 链接须通过 `RUSTDOCFLAGS` 传递，普通 `RUSTFLAGS` 不够。
