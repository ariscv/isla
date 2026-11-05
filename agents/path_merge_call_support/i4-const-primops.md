# I4：常量原语效应与函数级对照

**固定配置值现已归 `Pure`，`undefined` 与任意动态 Reset 仍保守归 `WritesState`；未声明调用保留未知分类。`pte_is_invalid` 在旧配置和新增常量配置下均为 10 → 6，两组各 23 项 Z3 检查及 10 类投影枚举通过。** 新配置消除了 `hartSupports` 中常量原语的拒绝，但全函数摘要仍包含另一条异常路径，因此没有达到单路径。

本轮基于分支 `feat/postprocess-enumeration`、HEAD `ac90792`，仅编辑文件，未进行 git 写操作。实验日志与辅助脚本位于 `/tmp/i4/`。IR 沿用 `/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir`，SHA-256 为 `c0e4661a73888c56438a6f76059370667d141a026502d0511291586067bd31c0`。

## 实现与测试依据

`get_const_primops` 复用现有 TOML → `URVal` 解析。`URVal::Init` 只复制固定值，归 `Pure`；`URVal::Uninit` 在每次调用时生成新符号，归 `WritesState`。`URVal::into_reset` 由普通复位和配置原语共用，运行时闭包的行为保持原有语义。

原有 `Reset` 是不透明闭包，无法从其类型恢复配置来源。因此 `ISAConfig.const_primops` 和 `Primops.consts` 的值改为 `(Reset, Effect)`，加载器将分类保存在 `Instr::PrimopReset` 新增的效应字段中；`region_merge` 的直接效应、传递摘要及静态/动态预筛统一读取该字段。其他指令匹配只补齐字段，未改变执行方式。任意闭包继续由 `reset_effect` 保守分类，未知 Call 继续走既有分类入口，没有按原语名字建立纯度名单。

测试先行记录：`red-configured.log` 观察到 `configured = false` 原先得到 `WritesState` 而非 `Pure`；`red-effects.log` 记录新增值分类接口尚不存在。新增测试覆盖同名原语取 `true`、`false`、`undefined` 和完全未声明四种情况；固定值通过真实执行及 Z3 差分检查实现 2 → 1，`undefined` 保持 2 条且没有提交合并记录。分类契约另覆盖固定布尔、单位值、机器整数，以及未初始化布尔与位向量；既有任意闭包保守测试保留。

真实 IR 回归同时加载两种配置，并检查 45 个配置值中有 43 个 `Pure`、两个 `WritesState`。

| 函数 | 旧配置摘要 | 带常量配置摘要 |
| --- | --- | --- |
| `hartSupports` | `MayFork` | `ReadsState` |
| `currentlyEnabled` | `MayFork` | `MayFork` |
| `pte_is_invalid` | `MayFork` | `MayFork` |
| `pte_is_non_leaf` | `Pure` | `Pure` |

`hartSupports` 仍读取全局 let `vector_support_level`，所以不是 `Pure`，但其摘要已无静态拒绝证据。`currentlyEnabled` 的整个函数体仍传递依赖 `get_xLPE → internal_error<o>`；后者 pc 11 调用 union 构造子 `Error_internal_error`，既有摘要将这种 Call 按未知调用归 `MayFork`，后面还写异常状态。这里如实保留现有分类，没有将异常路径或构造子另行放行。函数摘要没有实参特化，具体运行未经过该异常路径仍会被静态拒绝。

## 配置核对

- 新增 `agents/path_merge_call_support/baseline_config_const.toml`。已先确认旧 `baseline_config.toml` 没有 `[const_primops]`；新增文件保留原内容，再原样追加真实 `isla/configs/riscv64.toml` 的该段，含格式与全部取值。旧文件未修改，SHA-256 仍为 `39d5a7eaad3c42526fb3408dc69b5a9f22f0a5a515869c99526e3c0e022cda90`。
- 直接使用 `/data1/baiyifan/workplace/isla-runner/.worktree/mmu-symbolic-experiment/symbolic/config.toml`，未新增任务最初提出的临时副本，也未修改源文件。其 `[const_primops]` 的 45 个键和值与真实配置逐键完全一致，无差异。
- 新配置的 45 个键和值与真实配置及 Sv39 配置完全一致。只有两项为非固定值：`plat_get_16_random_bits = "undefined : %bv16"`、`speculate_conditional = "undefined : %bool"`。`sys_pmp_count = "0 : %i64"` 等取值均原样保留。
- 新 baseline 配置完成解析和本函数分叉/合并执行；Sv39 原配置也额外完成不合并的本函数执行，10 条路径，退出 0。未遇到类型或宽度错误。Sv39 配置有既有警告：IR 缺少 `__isla_always_aligned` 寄存器；没有为此修改配置。此次函数执行不构成对全部未执行原语返回签名的校验。

两份实验使用配置的其余内容本来不同：baseline 的寄存器默认值表为空；Sv39 配置含寄存器初值、内存区域等。主对照只使用 baseline 与它追加常量段的副本，避免混入这些差异。

## 路径、等价检查与投影

均使用 `-T 1 --timeout 540 --traces --error-traces pte_is_invalid _ _`，合并侧只增加 `--path-merging`；环境为 `ISLA_STATS=1`，并为两组设置不同的 `ISLA_MERGE_RECORDS` 文件。四个子进程全部退出 0，耗时约 1.2–2.6 秒，完整命令见 `/tmp/i4/measure.json`。

| 配置 | 不合并路径数 | 合并路径数 | Z3 检查 | 投影枚举类数 |
| --- | ---: | ---: | ---: | ---: |
| `baseline_config.toml`，无常量段 | 10 | 6 | 23/23 通过 | 10 |
| `baseline_config_const.toml`，45 键常量段 | 10 | 6 | 23/23 通过 | 10 |

两配置不合并路径数没有变化；分叉侧 stdout 和合并侧 stdout 分别逐字相同。本函数在当前模型初态下没有因新增配置而减少实际分叉，不能将这个结果推到其他函数或其他初态。

复用 I2/I3 的辅助脚本，每组检查返回关系等价、原始覆盖恒真、覆盖一致，以及十个基线类各自可行性与回投返回值一致。各组投影枚举均为 8 类固定 `true`、2 类保留 `reserved != 0` 的符号返回；最终未覆盖域为 `unsat`。产物为 `/tmp/i4/pte-{old,const}-equivalence.{py,smt2,json}` 与 `/tmp/i4/pte-{old,const}-projection-enumeration.json`。

两组均尝试 6 次、成功 1 次、拒绝 5 次；成功记录均为本函数 pc 20 → 30，见 `/tmp/i4/pte-{old,const}-on.jsonl`。其余分叉的拒绝原因分布均为 `state_effect: 5`。

| 剩余分叉 pc | 旧配置拒绝位置 | 带常量配置拒绝位置 | 每组次数 |
| --- | --- | --- | ---: |
| 9 | `hartSupports` pc 46 | `internal_error<o>` pc 11 | 1 |
| 32 | 同上 | 同上 | 1 |
| 43 | 同上 | 同上 | 1 |
| 71 | 同上 | 同上 | 1 |
| 99 | 同上 | 同上 | 1 |

旧位置为 `core/extensions.sail 75:41 - 75:77` 的 `sys_enable_experimental_extensions`；新位置为 `prelude/errors.sail 21:47 - 21:106` 的异常构造调用。统计按分叉点计数，不是按六条返回路径计数。完整拒绝证据在各组 stderr。

令 `F` 为 8 位 flags，`E` 为 10 位 ext，`P = (F[2]=1 ∧ F[1]=0)`。两组剩余路径相同：

| 路径 | 条件 | 返回值 |
| --- | --- | --- |
| 1 | `F[0]=0` | `true` |
| 2 | `F[0]=1 ∧ P` | `true` |
| 3 | `F[0]=1 ∧ ¬P ∧ E[9]=1` | `true` |
| 4 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]≠0` | `true` |
| 5 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]=0 ∧ E[6:5]≠0` | `true` |
| 6 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]=0 ∧ E[6:5]=0` | `E[4:0]≠0` |

## 验证与构建

所有 Cargo 验证均使用：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
```

使用 `--offline --features smt-thread-interrupt -j 16`。主机有 128 个逻辑 CPU，本次仅分配 16 个构建任务，函数级测量固定单线程。每个验证/构建命令均有不超过 600 秒的外层限时，无命令超时。

- `region_merge`：24 通过、真实 IR 回归默认忽略；真实 IR 回归单独执行通过。
- `primop`：91 通过，唯一失败为已有基线项 `special_primop_retry_counts_call_once`。
- `speculation`：14 通过；`path_merging`：6 通过；附加的 `regions`：27 通过、1 忽略；`stats`：12 通过。
- 两个二进制 `cargo check` 通过，isarch CLI 的 24 项测试通过。
- 完整 `isla-lib`：671 通过、12 失败、2 忽略。已程序化比较完整失败名称集合，与用户列出的 12 项基线及 I3 日志完全一致，无新增失败；证据见 `/tmp/i4/failure-set.json`。
- `cargo fmt` 已运行。
- `make -j1 solve-MRET THREADS=16 OUTER_TIMEOUT=540s SOLVE_TIMEOUT=500s` 冒烟通过，产出 `output/rv64_zMRET.json`，包含 4 条用例。原 `output/` 已移到 `/tmp/i4/output-before-smoke` 后再运行，未混入旧日志。
- `cargo build --release --offline --bin isarch --bin isla-execute-function --features smt-thread-interrupt -j 16` 完成；二进制保留在本工作树 `target/release/isarch` 和 `target/release/isla-execute-function`。

脚本与日志索引：`/tmp/i4/verify.py`、`verify-rest.py`、`verify-final.py`、`verification.json`、`verification-final.json`、`measure.py`、`measure.json`、`manifest.json`、`real-effects-final.log`、`release-final.log`、`full-final.log`、`smoke-MRET-final.log`。`manifest.json` 记录 IR、配置和 release 二进制的 SHA-256。

已按用户确认解决两项原规格冲突：非固定配置值不归纯；Sv39 配置复用已有常量段。剩余六条路径是现有全函数保守摘要的实测限制，本任务没有扩展到构造子/异常路径分类修复或实参特化。
