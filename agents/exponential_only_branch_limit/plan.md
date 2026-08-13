# 局部 loop/branch limit 的历史实验记录

> 本文记录方向偏置和输出层 `case_quota` 加入前的中间方案与测量，不是当前最终配置说明。
> 当前 `vvtype.toml` 使用全局 `max_forks_per_branch = 1`、7 个 `region_fork_limits`、gather
> 重叠判断的 `sample_bias = 16` / `sample_bias_direction = "jump"`，并在收集结束后按
> `(助记符, 完整 test-ins, 返回值类别)` 分桶、均匀取样及 canonical sort；外层超时保持默认 40m。

## 目标（用户口径）

限制的单位是**一条具体的 RISC-V 汇编指令**（例如 VVTYPE 里的 `vrgather.vv`），不是整个
VVTYPE clause：每条具体指令最终生成的 path 不超过 100 条，超过的用局部 loop/branch limit
做抽样采样；同时 `vtype` 必须有不同的取值，不能被"限制"钉死成单一值。

## 两个根因

1. **`branch_sample` 不按路径分叉**：偏好只由 `(seed, scope, 路径内序号)` 决定，兄弟路径
   在同一分支点上算出同一个方向，"具体化抽样"退化成"钉死成一个取值" —— 基线 64 条输出
   `vtype` 全是 `0x15` 就是这么来的。
2. **预算只有 per-scope 一种粒度**：Sail 的 `match` 在 IR 里是一串位于不同 pc 的 jump，
   每个 arm 判定都是独立分支点，per-scope 预算对 SEW/LMUL 的多路展开完全无效
   （实测一条路径 fork 3 次展开 4 路 SEW、fork 6 次展开 7 路 LMUL）。

另有一个决定性事实：路径规模最大的分支点 `zbool_bit_forwards`（`bool_to_bit` 逐 lane 调用）
在 IR 里**没有 Sail 源码位置**，任何 region 都选不中它，所以 per-scope 预算必须全局生效
（不配 `regions`），一次实测里它 fork 了 1304 次。

## 当时实施的中间方案

1. region 级 fork 预算 `region_fork_limits`：整段区间内所有分支点共享一条路径的 fork 次数，
   match 链 => N+1 个取值，多分支点的循环体 => ×2。
2. 路径签名：`ExecutionLimitPathState.path_signature` 在每个 fork 点按 true/false 推进父/子路径，
   `branch_sample` 把它混进哈希，兄弟路径从此抽到不同方向；只依赖本路径的分叉序列，
   与线程数无关，可复现性不变。
3. 当时的 `configs/workarounds/vvtype.toml`：`max_forks_per_branch = 1` 全局生效 + 5 个 region 预算。
4. 当时的 `scripts/run.mk`：`solve-VVTYPE: OUTER_TIMEOUT = 60m`（实测 39m）；该覆盖后来已删除。

## 中间验收（已通过）

- `cargo test`：isla-lib 228 项、isla 47 项全绿。
- `rm -rf output && make solve-VVTYPE`：411 条路径 / 39m，逐汇编指令 path 数全部 ≤100
  （最大 vrgatherei16 82），`vtype` 有 4 组 SEW/LMUL 取值。

实测细节与遗留问题见同目录 `status.md`。
