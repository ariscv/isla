# Sail 内层合并失败用例骨架审核

核心用例可以用 Sail 表达。验收要求 S1 从 9 条路径合成 2 条，并保留两个指定的输入集合。当前共享合并核心有整批退回的可能，须保留这两项断言，用运行结果判断能力。

本页记录场景架子建立时的设计。缺省开启具体值合并后的验收见 [README](README.md)及[内层合并验收](../property/README-nested-merge.md)。

## 骨架核对

- **a. 具体值。** [值合并](../../isla-lib/src/primop_util.rs)中，等宽不同 bitvector 可用 ITE 合并，不同具体 `I64` 或字符串会产生 `IncompatibleMerge`。普通 Sail 局部整数可能是 `I128`，[帧合并](../../isla-lib/src/executor/region_engine.rs)会为两个 `I128` 构建 ITE，也可能删除不再活跃的局部槽位。选用字符串 `k`，在待测汇合点之后用 `eq_string` 消费它。该原语要求两边都是具体字符串。不同字符串触发 `IncompatibleState`。不同联合体标签本身可以合并，有重叠标签且载荷无法合并时才会得到 `UnionPayload`。
- **b. 汇合顺序。** 用 `if z == 1 then … else if z == 2 then … else …` 表达二叉嵌套，在汇合后消费同一个 `k` 和 `r`。S1 的 c2、c3 共用字符串 `k`，各自写入不同的等宽位向量 `r`，允许先合成 ITE。b1 的 `k` 不同。S3 让三个 `k` 两两不同。编译后核对 IR 中的分支和写入位置。
- **c. 外层形状。** 外层 `a` 的三条臂都计算内层三种情况，写入不同但等宽的外层位向量。字符串继续活跃到外层之后，因此期望按 `k` 将外层片段分组。S1 的两个守卫分别覆盖 `a ∈ {1,2,3} ∧ z = 1` 和 `a ∈ {1,2,3} ∧ z ∈ {2,3}`。当前 [finish_arrivals](../../isla-lib/src/executor/region_engine.rs#L231) 先折叠同一侧的所有片段，失败时保留整批片段，没有逐组配对的步骤。此处可能导致现行实现达不到预期。
- **d. 路径计数。** [execute-function](../../src/execute-function.rs#L268) 为每条成功且可满足的终态输出一行 `Result:`，再按需输出 `(trace …)`。错误单独输出并令进程退出码为 1，dead 终态不输出。它接受位置参数函数名和实参，`_` 表示保持符号输入，具体值按 IR 语法解析，`--model` 只取一个求解模型，无法证明每条守卫完整覆盖的输入。按最新要求，计数和形状校验都迁入 property。
- **e. 策略配置。** `execute-function` 已经接受 `-C` 中的 `[execution_limits.path_merge]`，包括 `enabled` 和 `strategy = "recursive" | "flat"`。`--path-merging` 打开合并；`--merge-strategy` 属于 isarch 的 [CLI](../../src/isarch/path_merge_options.rs)。`--isla-preserve` 将函数加入 [Sail 插件](../../isla-sail/sail_plugin_isla.ml#L409) 的初始调用集合，property 入口也可使用 `$property` 保留。旧基线 `966486b7` 有递归合并，配置结构没有 `strategy` 字段。

## property 框架扩展方案

- 现有 [Ruby 框架](../run_tests.rb#L140) 对 B64 和 B129 各运行一遍 property。`.unsat.sail` 期望退出 0，`.sat.sail` 期望退出 1，`.timeout.sail` 沿用超时约定。`.sail_opts` 传给 Sail，`.opts` 传给 property。共用模型放入 `test/property/include`，各入口的 `prop` 比较候选结果与独立规格，规格用直接位向量表达式避免在候选执行完后引入额外路径。另设预期为假的对照。
- [B64 入口](../../src/property.rs#L73) 写死三个执行限制，[B129 入口](../../src/property129.rs#L73) 直接构建默认任务。当前两者均没有把 `path_merge` 传给任务。共用选项处理复用 `-C` 配置和 `ExecutionLimits::with_config`，`--path-merging` 覆盖开关。B64 保留原有三个限制，与 A2 的交叉处是 [ExecutionLimits 初始化](../../src/property.rs#L73)。合并 A2 时保留配置传递和路径收集，以 A2 的限制初始值为准。
- `--expect-paths N` 比较最终完成的路径数，排除 dead、错误和其他未完成终态。持续使用现有性质收集器判断 SAT/UNSAT。计数失败用独立的非零退出码，确保错误的路径数无法让 `.sat` 假通过。`--print-paths` 与 `--dump-paths` 通过同一收集回调输出守卫、返回值和合并记录数，未指定三个选项时沿用原收集路径。取守卫的时机在性质收集器添加返回值否定断言之前。
- 多配置使用 `<basename>.<variant>.opts`，例如 `nested_merge_s1.unsat.flat.opts`。`--expect-paths` 直接写进选项；`-C` 可选用包含公共基础配置的测试 TOML。已有单份 `.opts`、默认配置、编译和退出码约定沿用。记录原有用例通过数并在扩展后重跑。
- S1 的 `.shape` 每行一个期望 SMT-LIB 谓词，并声明观测输入的位宽。用 Sail 入口的专用寄存器写入把输入映射到求解器表达式。Ruby 调用 Z3 枚举完整的两位输入域，并逐条比较守卫在这些输入上的投影集合，检查遗漏、重叠和错误分组。Z3 CLI 已确认可用。JSON 来自真实执行终态，旧基线以相同性质比较语义，以递归默认策略比较形状。
- S4 两个二路外层包住三路内层，预期 12→2，按 `z=1` 和 `z∈{2,3}` 分组。S5 三路调用方分别调用同一三路被调函数，字符串跨调用边界存活，预期 9→2，形状同 S1。S6 内层两个位向量可合并，中层自身的字符串失配，边界用例预期 4→2；再套一个二路外层，预期 8→2，按中层选择分组。另用 S1 的模型只改 b1 的字符串，预期 9→1。
