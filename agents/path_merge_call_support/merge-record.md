# 区域合并记录（I3 / I4）

I4 已完成固定配置值的原语效应分类与新旧配置对照：两种配置均为 **10 → 6**，两组各 23 项 Z3 检查及 10 类投影枚举通过。新配置的剩余拒绝来自 `internal_error<o>` 异常路径。详见 [I4 完整记录](i4-const-primops.md)。以下保留 I3 历史记录。

I3 已接入调用图最小不动点摘要、两个入口的加载期校验、JSON Lines 输出，以及正常结束和 Force 强退前的按规则统计。真实基线配置下，`pte_is_invalid` 的路径数为 **10 → 6**；23 项 Z3 检查及 10 类投影枚举通过。剩余拒绝来自未知原语调用，详见下文。

## 启用与提交语义

两个入口均支持：

```sh
export ISLA_MERGE_RECORDS=/tmp/isla-merge-records.jsonl
export ISLA_STATS=1
# isarch solve-state 或 isla-execute-function 的其余参数照常使用。
# --path-merging 开启全局 adaptive；也可仅通过 merge_policy 开启局部规则。
```

`ISLA_MERGE_RECORDS` 在首次成功提交时读取，进程内固定该路径。以追加方式打开，已有文件不会截断；新实验应使用新路径或先自行清空。每条记录是一个 UTF-8 JSON 对象，末尾有换行；进程内所有执行线程共用互斥写端，完整序列化后持锁写入，行不会交错。文件不经用户态缓冲，不依赖正常退出时析构刷新。不同进程应使用不同文件。

内层记录先随帧和求解器事务保留，最外层提交成功后统一发布。外层回滚时不会输出其已丢弃的内层记录；后续普通分叉重新完成的合并会输出新记录。只发布本次新增的记录，冻结、恢复或后续区域提交不会重复输出历史记录。两臂都死亡的剪枝也记一条 `outcome = "dead"`，与成功提交统计对应；失败尝试不输出记录。

记录是“合并时刻”的副产物；其后执行失败、断言过滤或收尾 `case_quota` 抽样不会撤销此前记录。它不是最终测试用例清单，也不替代 SMT 迹。

## 字段

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `schema_version` | 整数 | 当前为 `1` |
| `record_id` | 整数 | 本进程的唯一记录编号；并发时文件顺序不保证编号递增 |
| `task_id` | 整数 | 执行任务编号；符号不能跨任务仅凭变量号视为同一个输入 |
| `function` | 字符串 | 分支所属函数的 Sail 解码名 |
| `branch_pc` | 整数 | 函数内原始 IR 分支下标 |
| `join` | 对象 | `{"instruction": pc}`，或 `{"function_exit": true}` |
| `source_loc` | 对象 | 原始 SourceLoc：`file/line1/char1/line2/char2`；`file = -1` 表示未知 |
| `location` | 字符串 | 经 IR 文件表解析的源码位置，便于阅读 |
| `condition` | 符号对象 | 本区域的布尔条件符号 |
| `input_symbols` | 符号对象数组 | 合并值及条件的自由输入；展开 `DefineConst` 与纯计算新鲜等式依赖后，仅保留自由声明，按变量号排序 |
| `single_arm_reads` | 数组 | 单臂寄存器读取及完整外层保护条件 |
| `depth` | 整数 | 合并嵌套深度，从 `1` 开始；普通函数调用不单独增加此值 |
| `outcome` | 字符串 | `merged` 或 `dead` |

符号对象包含 `name`（迹中的 SMT 名称，如 `v17`）、`smt_id`（变量号，如 `17`）、`type`。这里的 `name` 是符号名，不是推测的 Sail 局部变量名。类型编码如下：

| `type.kind` | 额外字段 |
| --- | --- |
| `bool` | 无 |
| `bitvector` | `width` |
| `enum` | `name`，Sail 解码名 |
| `array` | `domain`、`range`，递归类型对象 |
| `float` | `exponent`、`significand` |
| `rounding_mode` | 无 |

`single_arm_reads` 的每项包含：`register`（解码寄存器名）、`accessor`（字段访问路径数组）、`value`（读取值的迹格式）、`guard.expression`（使用 `vN` 命名的 SMT-LIB 表达式）、`guard.symbols`（该表达式直接引用的布尔符号）。嵌套读取保留所有外层条件的合取。guard 的派生符号定义仍应从对应执行迹读取；本文件不复制整份 SMT 定义。

例如下面这一行描述：分支为真时读取寄存器 `record_register`，返回值与该读取有关，两个自由输入分别为分支条件和寄存器初值。

```json
{"schema_version":1,"record_id":0,"task_id":3,"function":"example","branch_pc":0,"join":{"instruction":4},"source_loc":{"file":0,"line1":10,"char1":0,"line2":10,"char2":8},"location":"example.sail 10:0 - 10:8","condition":{"name":"v0","smt_id":0,"type":{"kind":"bool"}},"input_symbols":[{"name":"v0","smt_id":0,"type":{"kind":"bool"}},{"name":"v1","smt_id":1,"type":{"kind":"bool"}}],"single_arm_reads":[{"register":"record_register","accessor":[],"value":"v1","guard":{"expression":"v0","symbols":[{"name":"v0","smt_id":0,"type":{"kind":"bool"}}]}}],"depth":1,"outcome":"merged"}
```

## 适用范围

**寄存器读取采用并集语义。** 只在一臂读取的寄存器，在合并路径的主迹中也被视为读取过。前置状态和 JSON 访问足迹仍适用；需要精确寄存器读写顺序、逐条执行迹或事件因果顺序时，该合并路径的迹不可信。单臂读取及 guard 为以后恢复精确路径保留信息，本次没有实现全消费方的 guarded events。

含内存访问及被调函数写状态的区域仍被拒绝。静态调用摘要不是函数实参特化，也不是纯函数求值缓存；摘要安全地考虑整个函数体，所以某个具体实参不会执行的未知调用仍可导致拒绝。

## Force、校验与统计

`--execution-limits-config` 加载后，两个入口在架构初始化完成、正式执行前调用同一套校验：函数选择器必须命中实际 IR 函数；strict 源码区域必须命中 Jump；Force 区域无后支配点或含回边时在执行前拒绝。普通配置校验错误返回 `1`，Force 结构拒绝及运行期强制合并失败返回 **86**。两个入口的 `--help` 均说明退出码。

`ISLA_STATS=1` 时，正常结束和 Force 强退均输出 `[MERGE_STATS]`、`[FORK_STATS]`、`[SPECULATION_REJECT_STATS]`。`MERGE_STATS.rules` 的键是 TOML 规则从 `0` 开始的序号，每项包含 `attempts/successes/failures/failure_reasons`，未尝试及 Off 规则也有零值条目。isarch 的周期快照继续包含规则统计。进程被外部 SIGKILL 终止时无法执行收尾代码。

## 真实 IR 重测（2026-11-05）

使用 `/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir`，以及仓库内 `baseline_config.toml`；没有为提高合并率增加常量原语覆盖。

| 函数 | 不动点摘要 |
| --- | --- |
| `currentlyEnabled` | `MayFork` |
| `hartSupports` | `MayFork` |
| `pte_is_invalid` | `MayFork` |
| `pte_is_non_leaf` | `Pure` |

前三者传递依赖 `hartSupports` pc 46 的 `sys_enable_experimental_extensions`。该外部调用不在已注册原语中，基线配置也未替换它，按规格取最保守 `MayFork`。这是实际模型与配置的限制；没有绕过它放行。

默认忽略的真实 IR 回归运行方式：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
ISLA_REGIONS_IR=/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
  cargo test -p isla-lib region_merge_real_ir_effects --offline --features smt-thread-interrupt -- --ignored --nocapture
```

函数级测量命令（去掉 `--path-merging` 得到分叉基线）：

```sh
ISLA_STATS=1 ISLA_MERGE_RECORDS=/tmp/i3/pte-records.jsonl \
  target/release/isla-execute-function \
  -A /data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
  -C agents/path_merge_call_support/baseline_config.toml -T 1 --timeout 540 \
  --traces --error-traces --path-merging pte_is_invalid _ _
```

结果为 **10 → 6**。合并尝试 `6`、成功 `1`、拒绝 `5`；原先的 `recursive_effect` 消失，五项现在均为 `state_effect`，触发点是 `hartSupports` pc 46，`core/extensions.sail 75:41 - 75:77`。

| 剩余分叉 pc | 源码位置 | 拒绝标签 |
| --- | --- | --- |
| 9 | `sys/vmem_pte.sail 83:4 - 91:32` | `state_effect` |
| 32 | `sys/vmem_pte.sail 84:4 - 91:32` | `state_effect` |
| 43 | `sys/vmem_pte.sail 88:5 - 88:59` | `state_effect` |
| 71 | `sys/vmem_pte.sail 89:5 - 89:65` | `state_effect` |
| 99 | `sys/vmem_pte.sail 90:5 - 90:76` | `state_effect` |

令 `F` 为 8 位 flags 输入，`E` 为 10 位 ext 输入，`P = (F[2]=1 ∧ F[1]=0)`。六条剩余结果逐项如下；表中的分叉均因上面的未知调用被 `state_effect` 拒绝。

| 路径 | 条件 | 返回值 | 尚未合并的分叉 |
| --- | --- | --- | --- |
| 1 | `F[0]=0` | `true` | pc 9 真侧 |
| 2 | `F[0]=1 ∧ P` | `true` | pc 9 假侧、32 真侧 |
| 3 | `F[0]=1 ∧ ¬P ∧ E[9]=1` | `true` | pc 9、32 假侧，43 真侧 |
| 4 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]≠0` | `true` | pc 9、32、43 假侧，71 真侧 |
| 5 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]=0 ∧ E[6:5]≠0` | `true` | pc 9、32、43、71 假侧，99 真侧 |
| 6 | `F[0]=1 ∧ ¬P ∧ E[9]=0 ∧ E[8:7]=0 ∧ E[6:5]=0` | `E[4:0]≠0` | 五个分叉均走假侧 |

对应完整路径条件在 `/tmp/i3/pte-on.stdout` 中。拒绝统计按分叉点记账，因此同一拒绝点可出现在多条结果路径上。

复用 I2 的 `/tmp/i2-pte-equivalence.py` 辅助，将输入/输出路径改为 `/tmp/i3/pte-*`，Z3 完成 23 项检查：返回关系等价、分叉覆盖恒真、覆盖一致，以及原有 10 类各自的可行性和回投返回值一致。投影枚举完整复现 10 类（8 个 `true`、2 个保留关于 `reserved` 的符号返回值），最终未覆盖域为 Unsat。检查产物为 `/tmp/i3/pte-equivalence.{py,smt2,json}` 和 `/tmp/i3/pte-projection-enumeration.json`。最终 release 实测的完整单行记录保存在 `/tmp/i3/pte-records-final.jsonl`（`pte_is_invalid` pc 20 → 30，条件 `v4`，自由输入 `v0: BitVec(8)`，深度 1）。

## 验证记录

所有实现项先观察失败测试，再补代码；没有修改 12 项基线失败或受限的求解器/原语文件。

- `region_merge`：23 通过，真实 IR 回归默认忽略；单独执行真实 IR 回归通过。
- `speculation`：14 通过；`regions`：27 通过、1 忽略；`path_merging`：6 通过；`stats`：12 通过。
- 两个入口的 `cargo check --offline --features smt-thread-interrupt` 通过；isarch CLI 测试 24 通过。
- TOML Force 子进程测试在 10 秒内以 86 退出，并验证结构化诊断和规则失败计数；既有静态拒绝、动态拒绝、Force/Off 冲突测试均通过。
- JSON Lines 测试：8 线程各执行 4 次单臂读取合并，加双死臂与单存活臂剪枝各一次，共 34 行，全部可独立解析，编号唯一、字段正确。
- 全量 `isla-lib`：669 通过、12 失败、2 忽略，最终失败集合与基线完全一致。首次全量曾额外遇到 `deadline到期中断check返回超时错误` 的 1ms 时序测试抖动，未改代码，再次全量已通过该项。
- 修复非 strict 未解析区域规则被过滤后，后续规则序号压缩导致的统计/诊断错指；新增测试验证 TOML 原始编号稳定。
- 真正启动函数级 release 二进制，合成 IR 的 Force 写后读拒绝约 55ms 以 86 退出，并输出规则计数。真正启动 isarch 验证未知函数、strict 未匹配区域均返回 1。
- `make -j1 solve-MRET THREADS=16` 冒烟通过，产出 4 条用例。另一次全局 adaptive 冒烟也产出 4 条；4 次尝试均因静态副作用拒绝，成功 0，因此没有凭空创建记录文件。两条显式规则均保留零值统计。没有在本任务中执行用户后续的 60 秒 Sv39 实验。
- 构建和测试日志均在 `/tmp/i3/`。release 二进制保留在本工作树 `target/release/isarch` 与 `target/release/isla-execute-function`。
