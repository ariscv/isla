# 状态：局部 loop/branch limit 的历史实验

> 本文记录方向偏置与输出层 `case_quota` 加入前的中间阶段，不能作为当前 VVTYPE 的验收结论。
> 当前最终配置采用 7 个 `region_fork_limits`、gather 重叠判断的 16:1 `jump` 方向偏置，以及
> `[execution_limits.case_quota] Illegal_Instruction = 2`；默认 `OUTER_TIMEOUT` 为 40m。

## 中间阶段结论

`make solve-VVTYPE` 实测 411 条路径 / 39m：**逐汇编指令的 path 数全部 ≤100**
（最大 vrgatherei16 82、vrgather 66），`vtype` 有 4 组 SEW/LMUL 取值（外加 vill=1 的变体），
不再是基线那样 64 条路径全是 `0x15`。

| 阶段 | 逐指令最大 path 数 | vtype 取值数 | 总路径 | 耗时 |
|------|--------------------|--------------|--------|------|
| 基线（assert_sew/assert_lmul 预算 0） | 12 | **1** | 64 | 3m54s |
| 只放开线性分支点 | 455 | 28 | >2200（未跑完） | 40m 超时 |
| + region 预算（SEW/LMUL/rounding） | 315 | 4 | >998（未跑完） | 110m 超时 |
| + per-scope 预算全局生效（去掉 regions） | 101 | 4 | 423（未跑完） | 中断 |
| + gather 逐 lane 循环体 region 预算（中间阶段） | **82** | 4 | 411 | 39m |

## 中间阶段改动

- `isla-lib/src/executor/execution_limits.rs`
  - 新增 region 级 fork 预算 `region_fork_limits`：整段源码区间内所有分支点共享一条路径的
    fork 次数，是唯一能压住 `match` 链（每个 arm 判定是独立 scope）的粒度。
  - `ExecutionLimitPathState` 增加 `path_signature`，`branch_sample` 把它混进偏好哈希。
- `isla-lib/src/executor.rs`：两处 fork 点（`Instr::Jump`、`Instr::Monomorphize`）分别按 true/false
  推进父/子路径签名，兄弟路径的具体化抽样从此分叉。
- `isla-lib/src/config.rs`：`[[execution_limits.region_fork_limits]]` 解析。
- 当时的 `configs/workarounds/vvtype.toml`：`max_forks_per_branch = 1` 不再配 `regions`（全局生效），
  5 个 region 预算（assert_sew、assert_lmul_pow、get_fixed_rounding_incr、两条 gather 逐 lane 循环体）。
- 当时的 `scripts/run.mk`：`solve-VVTYPE: OUTER_TIMEOUT = 60m`（实测 39m）；该覆盖已删除。

## 单路径超时的原因（2026-08-08 实测）

给路径超时加了 SMT 用时诊断后，`make solve-VVTYPE` 的 29 条超时路径**结论完全一致**：

```
路径超时: 预算 1800.0s, active_wall 2006.6s, executor_cpu 1957.4s
  SMT 调用 5248 次, 累计 1922.4s (占 active_wall 95.8%), 最慢单次 0.6s [CheckSatAssuming @ ...]
  判定: 没有操作被单次上限中断，时间由正常求解累积而成：确实需要更多路径预算
```

- 29 条超时路径里**没有任何一次 Z3 调用被 `--smt-timeout`(60s) 中断**；
- 每条路径 5208~11456 次受保护调用（平均 6763 次），累计占 active_wall 的 95%~96%；
- **最慢单次只有 0.5~0.6s**，离 60s 上限差两个数量级。

所以不是"少数操作超时吃掉预算"，而是**求解次数太多**：时间被 5000+ 次各自都不慢的
check-sat-assuming 累积掉了。放宽 `--smt-timeout` 对这批路径完全无效；要么放宽
`--timeout`，要么减少这些路径的求解次数（最慢调用集中在 `vext_arith_insts.sail` 165/169/173
的 `min`/`max` 逐 lane 比较，以及 gather 的符号索引）。

另外超时路径数会随机器负载变化（`active_wall` 含 CPU 争用）：空载时 12 条，与 cargo 构建
并跑时 29 条。

## 超时已修复（2026-08-10）

根因是 `primop.rs::proven_symbolic_i128` 用"逐个枚举候选常量各问一次 solver"来判断唯一性
（72 个常用值 + `0..=512` 的全部整数 ≈ 515 次查询），对向量元素这种证明不出唯一值的符号量
全部落空；`max_int`/`min_int` 对两个参数各做一次 ⇒ **一次 `max()` ≈ 1030 次 check-sat**。

改成模型法（取模型值 `v` + 查 `sym != v` 是否 unsat，固定 3 次求解）后：

| | 耗时 | 超时路径 | 状态 | 逐指令最大 | vmin/vmax 系列 |
|---|---|---|---|---|---|
| 改之前 | 52m | 29 | failed(1) | 82 | 2~6 条 |
| 改之后 | **6m27s** | **0** | **intime** | 82 | 各 8 条 |

对其它 clause 是中性的（`DIVW` 旧 47s/新 49s，`AES64IM` 620s 内旧 1179/新 1181 条路径），
`scripts/run.mk` 给 VVTYPE 单独放宽的 `OUTER_TIMEOUT` 已经删掉，回到默认 40m。

## 按子指令独立配预算（2026-08-11，方向偏置与 case quota 前的基线）

口径细化：**每条具体子指令的预算相互独立**，理论上 ≤100 条路径的子指令一条限制都不该有。
据此把 dispatch 之前的 SEW/LMUL 预算全部撤掉（它会同时削掉所有子指令的 vtype 覆盖），
只给实测超过 100 条的子指令配它们**自己代码上**的 region 预算：

| region | 只影响 |
|---|---|
| vext_arith 181-187 / 190-196（逐 lane 循环体，预算 0） | vrgather / vrgatherei16 |
| vext_arith 65:36-65:57（`vs1 == vd \| vs2 == vd`，预算 0） | 两条 gather（只在 funct6 已确定为 gather 的那侧求值） |
| vext_arith 121-124（预算 0） | vssubu |
| vext_arith 131-136（预算 0） | vsmul |
| vext_utils 728-750（预算 0） | vsmul / vssrl / vssra |
| vext_utils 71-85 `valid_reg_overlap`（预算 0） | 主要是 gather（其它子指令两个 EMUL 相等、内层是具体值） |

另外修掉一个标注 artifact：在 funct6 dispatch 之前就 `return Illegal_Instruction()` 的路径
没有约束过 funct6，Z3 每次都给同一个成员，于是这些非法用例全被记到 vadd.vv 头上（196 条）。
`src/isarch/exec.rs::diversify_unconstrained_enums` 按路径签名给未约束的枚举字段挑成员并钉住，
非法用例因此散布到各条子指令上。

中间基线实测（`make solve-VVTYPE THREADS=64`，SEW/LMUL 全展开）：

- **intime，40m 内跑完，0 条路径超时**，1345 条用例（951 成功 + 394 非法）
- **vtype 覆盖 56 种取值**（此前抽样版只有 4~8 种）
- 21 条子指令里 **19 条在 44~83 条**，全部 ≤100 ✓
- 仍超标的两条：`vrgather.vv` 161（其中 141 条非法）、`vrgatherei16.vv` 144（其中 132 条非法）。
  超出的部分几乎全是 gather 专属的合法性违规用例；再往下压只能动 `illegal_normal`、
  `valid_reg_group` 这些**共享**前导，会牵连其它子指令，与"预算独立"冲突，因此停在这里。

## 遗留

- `DIV`/`DIVW` 在 `make solve -j` 并行下会因为 `mext_insts.sail:128` 的 `quotient >= 2 ^ 31`
  单次查询冲过 60s `--smt-timeout` 而失败（单跑 ~50s 能过）。这是本来就有的边界情况，与本次
  改动无关，要修得从 `--smt-timeout` 或并行度上考虑。
- `Monomorphize` 的 k 路 case split 与条件分支共用 per-scope 预算，语义上前者是线性展开，
  详见 `agents/findings.md`。VVTYPE 全程 0 次 monomorphize fork，暂未触发。
