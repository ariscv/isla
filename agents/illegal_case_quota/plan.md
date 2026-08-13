# 抑制 Illegal_Instruction 用例数量的方案与决策记录

> **当前实现**：档 B（区间 Truncate 抽样）已否决、未实现，由**具体化抽样的方向偏置**取代；
> 档 A 已作为收尾配额实现，档 C 保持默认关闭。评审意见、历史方案及修订理由见文末。

## 1. 问题与历史基线数据

`make solve-VVTYPE`（SEW/LMUL 全展开，40m 内跑完，intime）产出 1345 条用例：

- 951 条 `Retire_Success` + 394 条 `Illegal_Instruction`
- 逐子指令：19 条落在 44~83 ✓，两条超标：`vrgather.vv` 161（其中 **141 条非法**）、
  `vrgatherei16.vv` 144（其中 **132 条非法**）
- 这 141 条非法用例：**没有一条完全重复**，但只有 **25 种不同汇编串**，即同一个非法编码
  （例如 `vrgather.vv v0, v0, v0`）被配上 26 种不同 vtype 各算一条
- 全部 1345 条用例里操作数高度集中：`v0` 出现 2870 次、`v31` 655 次（未被路径约束的
  位向量字段仍取 Z3 默认值；上一轮的 `diversify_unconstrained_enums` 只处理了枚举）

目标：把非法用例的数量压下来，同时**不要**削掉成功路径的覆盖。

## 2. 两条硬约束（不可让步）

1. **多线程可复现**：判定只能依赖路径自身状态（`ExecutionLimitPathState`）或 run 级常量，
   不能用跨路径的全局计数器；否则结果随 `-T` 的 worker 数变化。
   现有 `path_local_sampling_is_stable_across_worker_counts` 是这条约束的回归防线。
2. **预算独立**：给 A 子指令加的限制不能改变 B 子指令的路径数/覆盖。

## 3. 为什么现成机制大多用不上（调研结论）

- angr `Bucketizer` / `LocalLoopSeer` 是调研里唯一同时满足两条硬约束的限流器，但它们治的是
  **单条路径内重复命中同一个类**（循环）。我们的冗余是**跨路径**的：141 条非法用例是 141 条
  不同路径、每条只产出一条用例，路径局部计数器互相看不见 → 不适用。
- S2E `CUPASearcher` 的 class-uniform 调度是"按类别配额"的工业标准，但桶容器是进程全局的
  （违反约束 1），且它**只调度不删路径**，对产出条数没有直接作用。
- S2E `ForkLimiter`、riscv-dv 的 `illegal_instr_ratio` 都是全局计数器 → 违反约束 1。
- KLEE 的错误去重（`emittedErrors`，key = 源码位置 + 错误消息）是最贴近的原型，
  其关键设计是**限流只作用在输出层、执行路径一条不少**（约束 2 天然成立）；
  它的全局 static 集合可以用"路径局部指纹 + 收集阶段确定性归并"替换掉。

因此只剩两类可用手段：**(a) 按路径签名做确定性抽样**、**(b) 收集阶段确定性归并/配额**。

---

## 4. 档 A：已实施的输出层按指纹配额

### 4.1 机制

不动执行，只决定"哪些完成的路径落盘成用例"。

- 分组键（指纹）：`(汇编助记符, 完整 test-ins, ret_val 类别)`。数据支持：141 条非法用例只有 25 种汇编串，
  按此分组每组平均 5.6 条，配额 N=2 即可压到 ~50 条。
- 保留策略：组内按 `path_signature` 全序排序后**均匀取样** N 条
  （下标 `round(i * (k-1) / (N-1))`，i = 0..N-1），而不是取前 N 条——后者会系统性偏向
  签名小的路径，前者能让保留下来的用例在 vtype/寄存器上更分散。
- 确定性：排序键 `path_signature` 只由路径自身分叉序列决定，与线程数、调度顺序无关；
  归并发生在所有 worker join 之后的单线程收尾阶段 → 结果逐字节可复现。
- 独立性：配额按 `(助记符, 完整 test-ins, 类别)` 分桶，`vrgather.vv` 的桶满了不影响 `vadd.vv` 的桶。

### 4.2 落点

- `src/isarch/exec.rs` 以不序列化的 `CollectedCase { path_signature, item }` 收集结果；在
  `run_symbolic_execute_with_target` 收尾、`to_json` 之前分组、均匀取样并 canonical sort。
- 配置位于 `configs/workarounds/vvtype.toml`：
  ```toml
  [execution_limits.case_quota]
  # 每条具体汇编指令、每种返回值类别最多保留多少条用例；未列出的类别不限量。
  Illegal_Instruction = 2
  ```
  该表由 `isla-lib/src/config.rs` 解析进 `ExecutionLimitsConfig`，再由 isarch 收尾阶段消费。

### 4.3 成本与收益

- 收益：立刻把 141 → ~50，且每个 (子指令, 类别) 的配额天然独立。
- 成本：**不省执行时间**。非法路径照跑，且照样要在 collector 里解一次汇编串和 encdec
  （日志里 `vext_arith 45:7-46:83` 那 979 次 fork 就是 encdec 查询的开销）。
- 风险：低。结构上不可能影响探索。唯一的判断是"丢掉的那几条是不是更有价值"。

---

## 5. 已否决的历史方案：档 B，illegal-only 区间 Truncate 抽样（未实现）

### 5.1 曾考虑的机制

在执行侧把"注定通向 `return Illegal_Instruction()`"的路径按比例砍掉。

- 新配置：
  ```toml
  [[execution_limits.region_path_sampling]]
  keep_numerator = 1
  keep_denominator = 4        # 经过该区间的路径只保留 1/4
  file = "extensions/V/vext_arith_insts.sail"
  start_line = 74             # then return Illegal_Instruction();
  ...
  ```
- 判定：在 `Instr::Jump` 处，若某一侧的**目标指令**的 `SourceLoc` 落在采样区间内，则用
  `splitmix64(path_signature ^ region_seed) % denominator >= numerator` 判定丢弃，
  丢弃时直接 `ExecutionLimitDecision::Truncate`（这条路径注定非法，丢掉不损失成功覆盖）。
- 需要新增 `Instr::source_loc()` 访问器（`isla-lib/src/ir.rs`，各变体最后一个字段就是 info）。
- 确定性：只依赖 `path_signature` + 配置常量 ✓
- 独立性：区间只覆盖那一个 `then return Illegal_Instruction()`，成功路径不经过它 ✓

### 5.2 为什么否决

理想做法（论文里的 Chopper/veritesting 思路）是加载 IR 后做一次**静态反向可达性**：标记
"从该基本块出发的每条路径都终止于同一个返回值"的块，只允许在这类块上配采样。这样
"不删任何成功路径"是可证的而不是靠人写坐标。代价是要在 isla 里实现 IR 级 CFG 分析。

折中：先靠配置坐标 + 文档约定，加载时不做验证；把静态验证列为后续增强。

### 5.3 历史评估

- 收益：省下非法路径在 collector 里的汇编/encdec 求解开销（这才是大头）。
- **弱点（需要评审）**：非法路径在前导就 return，本身执行很便宜；真正的开销在 collector。
  如果只在执行侧砍，省的是"整条路径 + collector"，收益是实打实的；但如果档 A 已经把它们
  过滤掉了，档 B 的边际收益取决于**档 A 的过滤发生在 collector 之前还是之后**。
  当前档 A 的设计是收尾阶段过滤（collector 已经跑过了）→ 两档收益不重叠，可以叠加。

---

## 6. 档 C：前置合法性约束（不推荐）

在执行前把 gather 的寄存器组重叠规则写成 SMT 约束 assert 掉，非法路径根本不产生。

不推荐的理由：
- isla-testgen 的对应机制（`StopConditions + StopAction::Kill` 杀异常入口）在我们这儿不适用：
  `valid_reg_overlap` 这类谓词在合法/非法两侧都会被调用（返回 bool，不是异常入口），
  Kill 掉就全灭；`--fun-assumption` 也用不了（实参是符号寄存器号，证不出相等）。
- 手写的合法性条件与 Sail 模型漂移时会**静默丢覆盖**，这正是 Genesys-Pro 把架构约束标
  mandatory、testing knowledge 标 non-mandatory 的原因，而我们没有那套交叉校验。

---

## 7. 未实施的后续设想：把取值多样化扩展到位向量字段

`diversify_unconstrained_enums`（`src/isarch/exec.rs`）目前只处理枚举。扩展到位向量字段
（寄存器号）后，25 种汇编串能变成上百种——同样的用例条数，覆盖面更高。这与 riscv-dv 的
寄存器加权表、sail-riscv-test-generation 的 `frequency` 权重是同一思路。

实现：对每个符号位向量字段，按 `splitmix64(path_signature ^ 序号)` 取候选值，
`check_sat_with(sym == candidate)` 能满足就 `Assert`。成本是每条完成路径多几次求解。

## 8. 当前验收口径

当前实现应使用 `rm -rf output && make solve-VVTYPE THREADS=64` 验收；下列是需要实测确认的
验收断言，而非代码自动保证：

- 配额只配置 `Illegal_Instruction`，`Retire_Success` 不受输出层配额影响；
- 成功用例数及成功用例的 vtype 覆盖不低于方向偏置与配额前基线；
- 每条子指令的每个 vill 类别至少保留一条非法代表；
- 每条具体汇编指令的用例数不超过 100；
- 使用 `THREADS=1/4/64` 运行后，JSON 逐字节一致。

## 9. 历史设计取舍

1. 档 A 的分组键该不该带上 vtype/SEW/LMUL 维度？带上会让配额变松（组数变多），
   不带则同一编码的不同 vtype 会互相挤掉。
2. 档 A 的"均匀取样"是否值得，还是取前 N 更简单可预测？
3. 档 A 应该放在 collector 之前（省 encdec 求解）还是之后（分组键需要汇编串，只能在之后）？
   有没有办法用执行侧就能拿到的信息构造分组键？
4. 档 B 的 `Truncate` 是否会破坏"非法用例本身也是有价值的覆盖"？比例该怎么定？
5. 档 B 不做静态 illegal-only 验证、只靠人写坐标，风险有多大？
6. 第 7 节扩展到位向量字段后，每条路径多几次 `check_sat_with` 的开销是否可接受？


---

## 10. codex 对抗性评审后的定稿（2026-08-13）

### 10.1 评审结论（verdict: needs-attention）

- **[high] 档 A 保证不了 vtype 覆盖不下降**：56 种 vtype 里 `Retire_Success` 只覆盖 26 种。
  核对属实，但那 30 种"只由非法用例提供"的 vtype 里 **28 种是 vill=1**（该配置下任何 V 指令
  必然非法，不存在成功路径）。结论仍然成立：**验收指标要改**。
- **[high] 档 A 的可复现性没闭环**：collector 往共享 `Vec` push，顺序由调度决定；原方案只说了
  组内排序，没要求最终 `gen` 全量稳定排序；`path_signature` 是 64 位混合值、可能碰撞。
- **[high] 档 B 的采样区间在 funct6 dispatch 之前**：`vext_arith_insts.sail:70-74` 是所有子指令
  共享的，按它采样会同时削掉 vadd/vsub/vrgather 等所有子指令的非法路径。
- **[high] 档 B 把源码坐标命中误当成 illegal-only 证明**：`SourceRegion` 只表达源码跨度、不表达
  可达终点，`Truncate` 可能静默丢失成功路径。
- **[medium] 档 C 约束范围不足**：保持默认关闭的有损实验。

### 10.2 定稿方案：方向偏置取代档 B

**根因**：`branch_sample`（`execution_limits.rs:687-688`）是 50/50 pair-balanced 抽样。gather 的
几个 region 预算已经是 0（不 fork、只抽样），于是**一半路径被均匀抽进了非法侧**——217 条 gather
非法用例不是"探索出来的"，是被采样器送过去的。

**机制**：给 `region_fork_limits` 增加可选的方向偏置，预算耗尽后具体化时不再 50/50，而是
只有 `1/sample_bias` 的路径抽到被压制的那一侧。

```toml
[[execution_limits.region_fork_limits]]
max_forks_per_region = 0
sample_bias = 16                      # 每 16 条路径只有 1 条抽到下面这个方向
sample_bias_direction = "fallthrough" # 被压制的方向："jump" 或 "fallthrough"
file = "..." ...
```

**为什么它比档 B 更可控**：`concretize_branch_condition` 会先试偏好方向，不可满足时再尝试另一侧，
因此不会因偏好方向不可满足而直接截断当前可行执行；但它仍是覆盖抽样。当前哈希绑定的 gather
重叠 region 中，`jump` 才是被压制的非法侧；方向与成功覆盖须通过最终验收实测确认。

**方向怎么定**：配置里显式写，靠 `ir_sha256` 锚定 IR，再用实测条数及成功覆盖校验；若 IR 或
源码控制流改变，必须重新确认方向，不能把历史判断泛化为任意 region 的语义。

### 10.3 修订后的覆盖契约（替换原第 8 节验收）

- `Retire_Success` 用例不受当前配额配置影响，配额只配置非法类别；
- 成功用例数、成功用例的 vtype 覆盖、每个 vill 类别的非法代表均为验收指标，不是
  `case_quota` 自动强制的保证；
- 每条具体汇编指令的用例数 ≤100，以及 `THREADS=1/4/64` 的 JSON 逐字节一致，均须通过实际运行验证。

### 10.4 档 A 的确定性闭环（按评审补齐）

- 收集结构改成 `CollectedCase { path_signature, item }`
- 排序键 `(分组键, path_signature, 序列化文本)`，最后一项做 tie-breaker，杜绝签名碰撞时的调度依赖
- 配额过滤之后**对最终 `gen` 做全量 canonical sort**
- 分组键 = `(助记符, 完整 test-ins 汇编串, ret_val 类别)`；桶内及最终输出均按
  `(path_signature, 序列化文本)` 稳定排序。用 `(助记符, vtype)` 会让 141 条落进 141 个桶、配额失效
