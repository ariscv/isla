# V 扩展 clause solve 验收台账

## 2026-09-13 覆盖审计与修复记录

此前的“当前通过”仅表示命令在预算内完成，**不是** Sail 语义分支全面覆盖。对
`output/rv64_z*.json`、对应日志、workaround 和 `../sail-riscv` 的逐 clause 只读复核发现：

- `region_fork_limits` 原先按整段 region 共用预算；首个逐 lane 条件会耗尽预算，导致同一区间
  的 `funct6`、`.vv/.vs`、rounding 和活动范围等普通分支首次到达即被具体化。
- 已实际观察到的严重缺口包括：`MVVTYPE`/`MVXTYPE` 的多个 opcode 无成功路径，
  `NVTYPE`/`NXTYPE` 缺 `vxrm=01/10/11`，`VAESDF`/`VAESDM`/`VAESEF`/`VAESEM` 无合法
  `.vs` 成功执行或循环体执行，`MVVCOMPRESS` 成功路径没有 `vl >= 2`。
- 其他逐 lane 指令即使有成功 JSON，也不能将“一个采样模型”误记为“每个 i、每个 mask
  方向、每个 operand 值均已穷尽”。这类数据域覆盖须以定向生成物或 trace 另行验收。

本轮修复将 region 预算改成“**region × 静态分支 scope**”计数：同一个循环条件重复到达仍在
首次 fork 后抽样，但同一区间内其他静态分支保留首次 fork。全部 workaround 的
`max_forks_per_region` 也从 `0` 调整为 `1`，因此不会再在首个命中点直接具体化。对应回归测试：
`region_fork_budget_keeps_the_first_fork_of_each_branch_point`。

重新生成后，以下是必须作为成功见证复核的高风险项：

| 范围 | 最低成功见证 |
|---|---|
| `MVVTYPE`、`MVXTYPE`、`VVTYPE` | 每个 Sail `funct6` arm 至少一条 `Retire_Success` |
| `NVTYPE`、`NXTYPE`、`NITYPE` | `vxrm=00/01/10/11` 各至少一条成功路径 |
| `VAESDF/DM/EF/EM`、`ZVKSM4RTYPE` | 合法 `.vv` 与 `.vs` 均进入 element-group body |
| `MVVCOMPRESS`、mask/reduction 类 | 合法 `vl >= 2`，且 trace 可见多个活动 lane |
| immediate 类 | 非零立即数的合法成功样本 |
| widening/restart 类 | 合法非零 `vstart` 成功样本；若 Sail 明定非法则记录该非法见证 |

在上述见证重跑完成前，本文件旧表的“当前通过”不得再被用作分支覆盖完成的声明。

## 口径

- 当前验收范围：只统计 `src/isarch/clause.rs` 中 `"v"` 扩展的 clause；
  `vector_crypto` 与 `zvabd` 不计入本轮完成条件。
- 按用户 2026-09-10 的最新要求，`"v"` 扩展中的浮点和内存相关 clause 暂时跳过；
  其余 clause 逐个运行 `make solve-<CLAUSE> THREADS=$(nproc)`，并在 `scripts/run.mk`
  的预算内通过。
- 遇到逐 lane 状态爆炸时，参照 `configs/workarounds/vvtype.toml` 增加 clause 专属配置：
  严格绑定 IR SHA-256，只限制有证据的源码 region/helper，不固定 `vtype`、`vl`、
  `vstart` 等运行态，不限制循环外子指令分派。
- `output/` 是易失验收产物。本文件记录已经完成的终态，继续工作时仍应以当前配置、日志和
  重跑结果复核；不能只凭本文件宣称全量完成。
- 主机 `nproc=12`；每个 clause 显式使用 `THREADS=12`，同时最多运行两个 clause。

## 逐 clause 汇总

下表覆盖 `"v"` 扩展定义的全部 89 条 clause。`当前通过` 表示本轮产物可解析、`.gen`
非空、唯一 `intime` 且无 `timeout/failed`；详细 path/助记符/配置见后续“已通过”表。

| Clause | 分类 | 状态 | 说明 |
|---|---|---|---|
| `FVFMATYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FVFMTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FVFTYPE` | 浮点 | 跳过 | 缺 Add/Sub/Mul/Div/Lt_quiet helper |
| `FVVMATYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FVVMTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FVVTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWFTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWVFMATYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWVFTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWVTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWVVMATYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `FWVVTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `MASKTYPEI` | 整数/掩码 | 当前通过 | 92 paths |
| `MASKTYPEV` | 整数/掩码 | 当前通过 | 104 paths |
| `MASKTYPEX` | 整数/掩码 | 当前通过 | 136 paths |
| `MMTYPE` | 整数/掩码 | 当前通过 | 10 paths |
| `MOVETYPEI` | 整数 move | 当前通过 | 57 paths |
| `MOVETYPEV` | 整数 move | 当前通过 | 69 paths |
| `MOVETYPEX` | 整数 move | 当前通过 | 101 paths |
| `MVVCOMPRESS` | 整数/压缩 | 当前通过 | 136 paths |
| `MVVMATYPE` | 整数算术 | 当前通过 | 315 paths |
| `MVVTYPE` | 整数算术 | 当前通过 | 183 paths |
| `MVXMATYPE` | 整数算术 | 当前通过 | 247 paths |
| `MVXTYPE` | 整数算术 | 当前通过 | 559 paths |
| `NISTYPE` | 整数/窄化 | 当前通过 | 265 paths |
| `NITYPE` | 整数/窄化 | 当前通过 | 212 paths |
| `NVSTYPE` | 整数/窄化 | 当前通过 | 289 paths |
| `NVTYPE` | 整数/窄化 | 当前通过 | 229 paths |
| `NXSTYPE` | 整数/窄化 | 当前通过 | 325 paths |
| `NXTYPE` | 整数/窄化 | 当前通过 | 325 paths |
| `RFVVTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `RFWVVTYPE` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `RIVVTYPE` | 整数/舍入 | 当前通过 | 40 paths |
| `RMVVTYPE` | 整数/舍入 | 当前通过 | 79 paths |
| `VCPOP_M` | 掩码 | 当前通过 | 6 paths |
| `VEXTTYPE` | 整数/扩展 | 当前通过 | 132 paths |
| `VFIRST_M` | 掩码 | 当前通过 | 6 paths |
| `VFMERGE` | 浮点 | 历史通过，不计入本轮 | 跳过要求前已 `intime` |
| `VFMV` | 浮点 | 历史通过，不计入本轮 | 跳过要求前已 `intime` |
| `VFMVFS` | 浮点 | 历史通过，不计入本轮 | 跳过要求前已 `intime` |
| `VFMVSF` | 浮点 | 历史通过，不计入本轮 | 跳过要求前已 `intime` |
| `VFNUNARY0` | 浮点 | 跳过 | 缺浮点/整数转换 helper |
| `VFUNARY0` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `VFUNARY1` | 浮点 | 跳过 | 缺 f16/f32 sqrt helper |
| `VFWUNARY0` | 浮点 | 跳过 | 未绑定 SoftFloat helper |
| `VICMPTYPE` | 整数比较 | 当前通过 | 145 paths |
| `VID_V` | 整数/索引 | 当前通过 | 135 paths |
| `VIMCTYPE` | 整数比较 | 当前通过 | 79 paths |
| `VIMSTYPE` | 整数比较 | 当前通过 | 91 paths |
| `VIMTYPE` | 整数比较 | 当前通过 | 79 paths |
| `VIOTA_M` | 掩码 | 当前通过 | 135 paths |
| `VISG` | 整数 gather | 当前通过 | 565 paths |
| `VITYPE` | 整数算术 | 当前通过 | 661 paths |
| `VLRETYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VLSEGFFTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VLSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VLSSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VLXSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VMSBF_M` | 掩码 | 当前通过 | 8 paths |
| `VMSIF_M` | 掩码 | 当前通过 | 8 paths |
| `VMSOF_M` | 掩码 | 当前通过 | 8 paths |
| `VMTYPE` | 掩码 | 当前通过 | 74 paths；PMP 早退生效 |
| `VMVRTYPE` | 整数 move | 当前通过 | 23 paths |
| `VMVSX` | 整数 move | 当前通过 | 41 paths |
| `VMVXS` | 整数 move | 当前通过 | 9 paths |
| `VSETIVLI` | 配置 | 当前通过 | 12 paths |
| `VSETVL` | 配置 | 当前通过 | 36 paths |
| `VSETVLI` | 配置 | 当前通过 | 22 paths |
| `VSRETYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VSSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VSSSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VSXSEGTYPE` | 内存 | 跳过 | 涉及内存符号化 |
| `VVCMPTYPE` | 整数比较 | 当前通过 | 157 paths |
| `VVMCTYPE` | 整数比较 | 当前通过 | 定向验收通过 |
| `VVMSTYPE` | 整数比较 | 当前通过 | 103 paths |
| `VVMTYPE` | 整数比较 | 当前通过 | 91 paths |
| `VVTYPE` | 整数算术 | 当前通过 | 864 paths；21/21 助记符 |
| `VXCMPTYPE` | 整数比较 | 当前通过 | 269 paths |
| `VXMCTYPE` | 整数比较 | 当前通过 | 定向验收通过 |
| `VXMSTYPE` | 整数比较 | 当前通过 | 135 paths |
| `VXMTYPE` | 整数比较 | 当前通过 | 137 paths |
| `VXSG` | 整数 gather | 当前通过 | 377 paths |
| `VXTYPE` | 整数算术 | 当前通过 | 900 paths |
| `WMVVTYPE` | 整数宽化 | 当前通过 | 1051 paths |
| `WMVXTYPE` | 整数宽化 | 当前通过 | 877 paths |
| `WVTYPE` | 整数宽化 | 当前通过 | 541 paths |
| `WVVTYPE` | 整数宽化 | 当前通过 | 1891 paths |
| `WVXTYPE` | 整数宽化 | 当前通过 | 1345 paths |
| `WXTYPE` | 整数宽化 | 当前通过 | 373 paths |

## 已通过（含范围外历史结果）

本表用于保留所有已经取得正式结果的 clause，不能直接用表格行数计算本轮完成度。其中
`vector_crypto`、`zvabd` 以及 4 条浮点 move/merge clause 仅作为历史结果保留；本轮必要
验收范围只看 `"v"` 扩展内的 58 条非浮点、非内存 clause。

| Clause | 结果 | 专属配置 | 最终摘要 |
|---|---|---|---|
| `MMTYPE` | intime | 无 | 10 paths；8 成功/2 非法；8/8 助记符；10 种汇编与 encdec；4 种 vtype |
| `MASKTYPEI` | intime | `masktypei.toml` | 92 paths；44 成功/48 非法；50 种汇编与 encdec；45 种 vtype |
| `MASKTYPEV` | intime | `masktypev.toml` | 104 paths；44 成功/60 非法；43 种汇编与 encdec；45 种 vtype |
| `MASKTYPEX` | intime | `masktypex.toml` | 136 paths；88 成功/48 非法；54 种汇编与 encdec；46 种 vtype |
| `MOVETYPEI` | intime | 无 | 57 paths；22 成功/35 非法；32 种汇编与 encdec；23 种 vtype |
| `MOVETYPEV` | intime | 无 | 69 paths；22 成功/47 非法；25 种汇编与 encdec；23 种 vtype |
| `MOVETYPEX` | intime | 无 | 101 paths；44 成功/57 非法；32 种汇编与 encdec；25 种 vtype |
| `MVVCOMPRESS` | intime | `mvvcompress.toml` | 136 paths，定向验收通过 |
| `MVVMATYPE` | intime | 无 | 315 paths，基线直接通过 |
| `MVVTYPE` | intime | `mvvtype.toml` | 183 paths；12/12 助记符；23 种 vtype |
| `MVXMATYPE` | intime | `mvxmatype.toml` | 247 paths，定向验收通过 |
| `MVXTYPE` | intime | `mvxtype.toml` | 559 paths；14/14 助记符；23 种 vtype |
| `NISTYPE` | intime | `nistype.toml` | 265 paths；2/2 助记符；23 种 vtype |
| `NITYPE` | intime | `nitype.toml` | 212 paths；2/2 助记符；23 种 vtype |
| `NVSTYPE` | intime | 无 | 289 paths；2/2 助记符；23 种 vtype |
| `NVTYPE` | intime | `nvtype.toml` | 229 paths；2/2 助记符；23 种 vtype |
| `NXSTYPE` | intime | `nxstype.toml` | 325 paths；2/2 助记符；23 种 vtype |
| `NXTYPE` | intime | `nxtype.toml` | 325 paths；2/2 助记符；23 种 vtype |
| `RIVVTYPE` | intime | `rivvtype.toml` | 40 paths；2/2 助记符；masked/unmasked 均覆盖；20 种 vtype |
| `RMVVTYPE` | intime | `rmvvtype.toml` | 79 paths；8/8 助记符；23 种 vtype |
| `VITYPE` | intime | `vitype.toml` | 661 paths；12/12 助记符；23 种 vtype |
| `VIMTYPE` | intime | `vimtype.toml` | 79 paths；`vmadc.vi`；24 种 vtype |
| `VIMCTYPE` | intime | `vimctype.toml` | 79 paths；`vmadc.vi`；24 种 vtype |
| `VIMSTYPE` | intime | `vimstype.toml` | 91 paths；定向验收通过 |
| `VICMPTYPE` | intime | `vicmptype.toml` | 145 paths；6/6 助记符；23 种 vtype |
| `VVCMPTYPE` | intime | `vvcmptype.toml` | 157 paths；6/6 助记符；23 种 vtype |
| `VXCMPTYPE` | intime | `vxcmptype.toml` | 269 paths；8/8 助记符；23 种 vtype |
| `VVMCTYPE` | intime | `vvmctype.toml` | 已定向验收通过 |
| `VXMCTYPE` | intime | `vxmctype.toml` | 已定向验收通过 |
| `VVMTYPE` | intime | `vvmtype.toml` | 91 paths；2/2 助记符；23 种 vtype |
| `VVMSTYPE` | intime | `vvmstype.toml` | 103 paths；2/2 助记符；23 种 vtype |
| `VXMSTYPE` | intime | `vxmstype.toml` | 135 paths；2/2 助记符；23 种 vtype |
| `VXMTYPE` | intime | `vxmtype.toml` | 137 paths，定向验收通过 |
| `VXTYPE` | intime | `vxtype.toml` + 专属 90m/85m 预算 | 900 paths；796 成功/104 非法；20/20 助记符；23 种 vtype |
| `VXSG` | intime | `vxsg.toml` | 377 paths；当前正式 JSON 完整；状态已精确去重 |
| `VISG` | intime | `visg.toml` | 565 paths，定向验收通过 |
| `VMVRTYPE` | intime | `vmvrtype.toml` | 23 paths，定向验收通过 |
| `VEXTTYPE` | intime | `vexttype.toml` | 132 paths，定向验收通过 |
| `VFMV` | intime | `vfmv.toml` + F/D ISA 配置 | 131 paths；26 成功/105 非法；`vfmv.v.f`；88 种汇编与 encdec；24 种 vtype |
| `VFMVFS` | intime | 无 workaround；F/D ISA 配置 | 16 paths；3 成功/13 非法；`vfmv.f.s`；14 种汇编与 encdec；11 种 vtype |
| `VFMVSF` | intime | 无 workaround；F/D ISA 配置 | 38 paths；20 成功/18 非法；`vfmv.s.f`；18 种汇编；20 种 vtype；encdec 全部非空 |
| `VFMERGE` | intime | `vfmerge.toml` + F/D ISA 配置 | 166 paths；52 成功/114 非法；`vfmerge.vfm`；113 种汇编；38 种 vtype；encdec 全部非空 |
| `VABS_V` | intime | `vabs_v.toml` + 专属 ISA 配置 | 111 paths；49 种汇编；25 种 vtype；encdec 全部非空 |
| `ZVABDTYPE` | intime | `zvabdtype.toml` + 专属 ISA 配置 | 111 paths；44 成功/67 非法；2/2 助记符；masked/unmasked 均覆盖；82 种汇编；23 种 vtype；encdec 全部非空 |
| `ZVWABDATYPE` | intime | `zvwabdatatype.toml` + 专属 ISA 配置 | 233 paths；53 成功/180 非法；2/2 助记符均有成功/非法；masked/unmasked 均覆盖；224 种汇编；23 种 vtype；encdec 全部非空 |
| `VANDN_VV` | intime | `vandn_vv.toml` | 124 paths；masked/unmasked 均覆盖；25 种 vtype |
| `VANDN_VX` | intime | `vandn_vx.toml` | 200 paths；masked/unmasked 均覆盖；25 种 vtype |
| `VCLMULH_VV` | intime | `vclmulh_vv.toml` | 91 paths；44 成功/47 非法；masked/unmasked 均覆盖；23 种 vtype |
| `VCLMULH_VX` | intime | `vclmulh_vx.toml` | 178 paths；88 成功/90 非法；masked/unmasked 均覆盖；23 种 vtype |
| `VCLMUL_VV` | intime | `vclmul_vv.toml` | 91 paths；44 成功/47 非法；encdec 全部非空 |
| `VCLMUL_VX` | intime | `vclmul_vx.toml` | 178 paths；88 成功/90 非法；masked/unmasked 均覆盖；24 种 vtype |
| `VROL_VV` | intime | `vrol_vv.toml` | 124 paths；44 成功/80 非法；masked/unmasked 均覆盖；25 种 vtype |
| `VROL_VX` | intime | `vrol_vx.toml` | 200 paths；88 成功/112 非法；masked/unmasked 均覆盖；25 种 vtype |
| `VROR_VI` | intime | `vror_vi.toml` | 112 paths；44 成功/68 非法；masked/unmasked 均覆盖；24 种 vtype |
| `VROR_VV` | intime | `vror_vv.toml` | 124 paths；44 成功/80 非法；masked/unmasked 均覆盖；24 种 vtype |
| `VROR_VX` | intime | `vror_vx.toml` | 200 paths；88 成功/112 非法；masked/unmasked 均覆盖；25 种 vtype |
| `VWSLL_VI` | intime | `vwsll_vi.toml` | 253 paths；78 成功/175 非法；masked/unmasked 均覆盖；24 种 vtype；encdec 全部非空 |
| `VWSLL_VV` | intime | `vwsll_vv.toml` | 267 paths；70 成功/197 非法；masked/unmasked 均覆盖；24 种 vtype |
| `VWSLL_VX` | intime | `vwsll_vx.toml` | 409 paths；156 成功/253 非法；masked/unmasked 均覆盖；25 种 vtype |
| `VAESDF` | intime | `vaesdf.toml` | 29 paths；5 成功/24 非法；2/2 助记符；14 种 vtype；encdec 全部非空 |
| `VAESDM` | intime | `vaesdm.toml` | 29 paths；5 成功/24 非法；2/2 助记符；14 种 vtype；encdec 全部非空 |
| `VAESEF` | intime | `vaesef.toml` | 29 paths；5 成功/24 非法；2/2 助记符；14 种 vtype；encdec 全部非空 |
| `VAESEM` | intime | `vaesem.toml` | 29 paths；5 成功/24 非法；2/2 助记符；14 种 vtype；encdec 全部非空 |
| `VAESKF1_VI` | intime | `vaeskf1_vi.toml` | 60 paths；36 成功/24 非法；`vaeskf1.vi`；39 种汇编；14 种 vtype；encdec 全部非空 |
| `VAESKF2_VI` | intime | `vaeskf2_vi.toml` | 45 paths；21 成功/24 非法；`vaeskf2.vi`；33 种汇编；26 种立即数；14 种 vtype；encdec 全部非空 |
| `VAESZ_VS` | intime | 无需 | 23 paths；均为非法指令返回；`vaesz.vs`；13 种汇编；12 种 vtype；encdec 全部非空 |
| `VGHSH_VV` | intime | `vghsh_vv.toml` | 41 paths；5 成功/36 非法；`vghsh.vv`；27 种汇编；15 种 vtype；encdec 全部非空 |
| `VGMUL_VV` | intime | `vgmul_vv.toml` | 29 paths；5 成功/24 非法；`vgmul.vv`；13 种汇编；15 种 vtype；encdec 全部非空 |
| `VSM3C_VI` | intime | `vsm3c_vi.toml` | 16 paths；均为非法指令返回；`vsm3c.vi`；16 种汇编；14 种立即数；12 种 vtype；encdec 全部非空 |
| `VSM3ME_VV` | intime | `vsm3me_vv.toml` | 27 paths；均为非法指令返回；`vsm3me.vv`；25 种汇编；12 种 vtype；encdec 全部非空；成功执行因 encdec=None 未输出 |
| `VSM4K_VI` | intime | `vsm4k_vi.toml` | 29 paths；5 成功/24 非法；`vsm4k.vi`；24 种汇编；20 种立即数；14 种 vtype；encdec 全部非空 |
| `VSHA2MS_VV` | intime | `vsha2ms_vv.toml` | 45 paths；9 成功/36 非法；`vsha2ms.vv`；27 种汇编；16 种 vtype；SEW=32/64 成功路径均覆盖；encdec 全部非空 |
| `ZVKSHA2TYPE` | intime | `zvksha2type.toml` | 58 paths；9 成功/49 非法；2/2 助记符成功覆盖；36 种汇编；22 种 vtype；SEW=32/64 成功路径均覆盖；encdec 全部非空 |
| `ZVKSM4RTYPE` | intime | `zvksm4rtype.toml` | 29 paths；5 成功/24 非法；2/2 助记符；16 种汇编；14 种 vtype；encdec 全部非空 |
| `VBREV8_V` | intime | `vbrev8_v.toml` | 112 paths；masked/unmasked 均覆盖；25 种 vtype |
| `VREV8_V` | intime | `vrev8_v.toml` | 112 paths；masked/unmasked 均覆盖；23 种 vtype |
| `VBREV_V` | intime | `vbrev_v.toml` | 112 paths；masked/unmasked 均覆盖；25 种 vtype |
| `VCLZ_V` | intime | `vclz_v.toml` | 112 paths；masked/unmasked 均覆盖；23 种 vtype |
| `VCTZ_V` | intime | `vctz_v.toml` | 112 paths；masked/unmasked 均覆盖；25 种 vtype |
| `VCPOP_M` | intime | `vcpop_m.toml` | 6 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VCPOP_V` | intime | `vcpop_v.toml` | 112 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VFIRST_M` | intime | `vfirst_m.toml` | 6 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VMSBF_M` | intime | `vmsbf_m.toml` | 8 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VMSIF_M` | intime | `vmsif_m.toml` | 8 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VMSOF_M` | intime | `vmsof_m.toml` | 8 paths；成功/非法与 masked/unmasked 均覆盖 |
| `VID_V` | intime | 无需 | 135 paths；成功/非法与 masked/unmasked 均覆盖；23 种 vtype |
| `VIOTA_M` | intime | `viota_m.toml` | 135 paths；44 成功/91 非法；成功路径 masked/unmasked 各 22；23 种 vtype |
| `VMVSX` | intime | 无需 | 41 paths；32 成功/9 非法；24 种 vtype；11 种汇编 |
| `VMVXS` | intime | 无需 | 9 paths；8 成功/1 非法；8 种 vtype；3 种汇编 |
| `VMTYPE` | intime | `vmtype.toml` | 74 paths；7 成功/64 内存异常/3 非法；2/2 助记符；6 种汇编；16 种 vtype；encdec 全部非空；PMP 禁用早退生效 |
| `VSETIVLI` | intime | 无需 | 12 paths；均正常退休；10 种 vtype；12 种汇编 |
| `VSETVL` | intime | 无需 | 36 paths；均正常退休；14 种 vtype；17 种汇编 |
| `VSETVLI` | intime | 无需 | 22 paths；均正常退休；14 种 vtype；22 种汇编 |
| `WVTYPE` | intime | 无需 | 541 paths；312 成功/229 非法；4/4 助记符各 78 条成功；23 种 vtype |
| `WVVTYPE` | intime | 无需 | 1891 paths；1470 成功/421 非法；7/7 助记符各 210 条成功；23 种 vtype |
| `WVXTYPE` | intime | 无需 | 1345 paths；1092 成功/253 非法；7/7 助记符各 156 条成功；23 种 vtype |
| `WXTYPE` | intime | 无需 | 373 paths；240 成功/133 非法；4/4 助记符各 60 条成功；23 种 vtype |
| `WMVVTYPE` | intime | 无需 | 1051 paths；630 成功/421 非法；3/3 助记符各 210 条成功；masked/unmasked 均覆盖；23 种 vtype |
| `WMVXTYPE` | intime | 无需 | 877 paths；624 成功/253 非法；4/4 助记符各 156 条成功；masked/unmasked 均覆盖；23 种 vtype |
| `VVTYPE` | intime | `vvtype.toml` | 864 paths；636 成功/228 非法；21/21 助记符；masked/unmasked 均覆盖；23 种 vtype；encdec 全部非空 |

## 当前进行中

- 无

## 本轮结论

- 58/58 条非浮点、非内存 clause 均已有当前正式产物：每条 JSON 可解析且 `.gen` 非空，
  每条在状态文件中恰有一条 `intime`，没有 `timeout` 或 `failed` 记录。
- 18 条未继续验收的浮点 clause 和 9 条内存 clause 均无 `intime`、`timeout` 或
  `failed` 残留；4 条提前完成的浮点 move/merge clause 只保留历史 `intime`。

## 按用户要求跳过

以下 clause 仍属于 `"v"` 扩展，但不计入本轮验收通过数范围，也不能因本轮要求标记为
`intime`。当前 `"v"` 扩展共 89 条：浮点 22 条、内存 9 条、非浮点且非内存 58 条，
即 `89 - 22 - 9 = 58`。本轮必要验收范围是最后这 58 条。

浮点 22 条中，下面列出的 18 条未继续验收；另有 `VFMERGE`、`VFMV`、`VFMVFS`、
`VFMVSF` 四条浮点 move/merge clause 在收到“跳过浮点”要求前已经正式通过。四条历史
结果仍保留在“已通过（含范围外历史结果）”表中，但不计入本轮 58 条必要范围。

### 浮点 clause（18 条）

```text
FVFMATYPE FVFMTYPE FVFTYPE FVVMATYPE FVVMTYPE FVVTYPE
FWFTYPE FWVFMATYPE FWVFTYPE FWVTYPE FWVVMATYPE FWVVTYPE
RFVVTYPE RFWVVTYPE
VFNUNARY0 VFUNARY0 VFUNARY1 VFWUNARY0
```

跳过原因：当前 IR 的合法浮点路径会调用未绑定的 `riscv_*` SoftFloat helper。
例如 `FVFTYPE` 已证实缺少 Add/Sub/Mul/Div/Lt_quiet，`VFNUNARY0` 缺少多种
浮点/整数转换，`VFUNARY1` 缺少 `riscv_f16Sqrt`/`riscv_f32Sqrt`。不得用零 flags、
自由符号返回值或固定非法状态绕过这些语义缺口，因此按用户要求停止。

### 内存 clause（9 条）

```text
VLRETYPE VLSEGFFTYPE VLSEGTYPE VLSSEGTYPE VLXSEGTYPE
VSRETYPE VSSEGTYPE VSSSEGTYPE VSXSEGTYPE
```

跳过原因：这些 clause 涉及内存符号化。`VLRETYPE` 已完成 PMP 早退验证并留下
ITRACE/日志证据，但按用户要求不再继续局部限制或正式验收；其余内存 clause 未继续运行。

## 已确认的共性限制模式

1. mask merge 类：只限制 execute 内 `vstart`/`vl` 驱动的逐 lane loop region。
2. narrowing/rounding 类：逐 lane loop region + `get_fixed_rounding_incr` region；若短时
   ITRACE 证明 `vxrm=0b11 -> bool_to_bit` 是长尾，再对 rounding-mode match 做方向抽样。
3. div/rem 类：保留循环外 funct6 分派；只在 arm 内对昂贵侧做稀疏抽样。`MVVTYPE` 的最终
   ITRACE 证明主要长尾实际来自 rounding helper，而不是 div/rem 本身。
