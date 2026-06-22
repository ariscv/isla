# output 执行错误函数定位报告（6.16）

- 生成方式：在仓库根目录扫描当前 `output/log/*.log`、`output/status.intime.log` 和 `output/status.timeout.log` 后整理写入本文件。
- 数据来源：`output/log/*.log`
- 运行来源：用户已执行 `make solve`，本报告只读取现有 `output/`，未重新运行。
- 过滤口径：沿用 `reports/6.14_test_solve_all/error_report.md` 的浮点过滤思路；本轮日志未扫描到 `riscv_f*`、`*ToF*`、SoftFloat、`extensions/FD`、`extensions/bfloat16`、`vext_fp*` 等浮点相关执行错误。
- 日志文件数：258；包含执行错误的日志文件数：118
- `status.intime.log`：241 个 clause；`status.timeout.log`：17 个 clause
- 原始执行错误总数：528；已过滤浮点相关错误：0；纳入本报告的非浮点执行错误：528
- 纳入本报告的日志文件数：118

## 结论

1. 当前最高频问题仍是符号 bitvector 长度，其中 `zeros` 273 次、`vector_init` 100 次。
2. 当前 `output/log` 中没有扫描到类型错误或缺失函数错误；6.14 中出现的 `%i64->%i Bits(...)`、`subrange_internal Poison`、`sys_enable_experimental_extensions` 均未出现。
3. 剩余问题主要分为三类：符号 bitvector 长度、循环上限、少量断言失败。
4. 超时项共有 17 个，主要集中在访存、除法、向量访存和部分 AES 指令。

## 按错误类型统计

| 错误类型 | 次数 |
|---|---:|
| 符号 bitvector 长度 | 382 |
| 循环上限 | 138 |
| 断言失败 | 8 |

## Top 问题函数/primop（非浮点）

| 次数 | 错误类型 | 问题函数/primop | 影响日志数 | 示例日志 | 示例消息 |
|---:|---|---|---:|---|---|
| 273 | 符号 bitvector 长度 | `zeros` | 68 | `MASKTYPEI.log:43` | Symbolic (bit)vector length in zeros(SymbolicLength("zeros", ...))[vector.sail 396:32 - 396:45] |
| 100 | 符号 bitvector 长度 | `vector_init` | 21 | `MOVETYPEV.log:35` | Symbolic (bit)vector length in vector_init(SymbolicLength("vector_init", ...))[extensions/V/vext_control.sail 84:40 - 84:71] |
| 66 | 循环上限 | `zpmpCheck` | 8 | `AMO.log:30` | Executed loop in 3670 at 41 more than specified limit(LoopLimitReached(Name("zpmpCheck"), 41)) |
| 30 | 循环上限 | `zinit_masked_result_cmp` | 5 | `VCPOP_M.log:27` | Executed loop in 4797 at 62 more than specified limit(LoopLimitReached(Name("zinit_masked_result_cmp"), 62)) |
| 10 | 循环上限 | `zcarryless_mul` | 2 | `CLMUL.log:17` | Executed loop in 2853 at 27 more than specified limit(LoopLimitReached(Name("zcarryless_mul"), 27)) |
| 8 | 循环上限 | `zcount_ones` | 2 | `CPOP.log:15` | Executed loop in 2864 at 23 more than specified limit(LoopLimitReached(Name("zcount_ones"), 23)) |
| 8 | 循环上限 | `zflush_TLB` | 2 | `SFENCE_VMA.log:31` | Executed loop in 4419 at 25 more than specified limit(LoopLimitReached(Name("zflush_TLB"), 25)) |
| 8 | 断言失败 | `sail_assert` | 5 | `UNZIP.log:9` | Assertion failure: extensions/K/zbkb_insts.sail:97.19-97.20 |
| 5 | 循环上限 | `zcarryless_mulr` | 1 | `CLMULR.log:17` | Executed loop in 2855 at 23 more than specified limit(LoopLimitReached(Name("zcarryless_mulr"), 23)) |
| 5 | 循环上限 | `zinit_masked_result_carry` | 1 | `MMTYPE.log:23` | Executed loop in 4796 at 60 more than specified limit(LoopLimitReached(Name("zinit_masked_result_carry"), 60)) |
| 5 | 符号 bitvector 长度 | `subrange_internal` | 3 | `VSRETYPE.log:29` | Symbolic (bit)vector length in subrange_internal(SymbolicLength("subrange_internal", ...)) |
| 4 | 符号 bitvector 长度 | `extension` | 2 | `MOVETYPEI.log:23` | Symbolic (bit)vector length in extension(SymbolicLength("extension", ...))[prelude/prelude.sail 89:29 - 89:51] |
| 3 | 循环上限 | `zread_vreg` | 2 | `VMTYPE.log:21` | Executed loop in 4009 at 96 more than specified limit(LoopLimitReached(Name("zread_vreg"), 96)) |
| 2 | 循环上限 | `zreverse_bits` | 1 | `BREV8.log:11` | Executed loop in 2751 at 23 more than specified limit(LoopLimitReached(Name("zreverse_bits"), 23)) |
| 1 | 循环上限 | `zexecute` | 1 | `XPERM4.log:16` | Executed loop in 4471 at 38330 more than specified limit(LoopLimitReached(Name("zexecute"), 38330)) |

## Top 调用位置/所在 Sail 函数（非浮点）

| 次数 | 源位置 | 所在 Sail 函数 | 问题函数/primop | 错误类型 | 影响日志示例 |
|---:|---|---|---|---|---|
| 265 | `/home/baiyifan/.opam/default/bin/../share/sail/lib/vector.sail:396` | `sail_ones` | `zeros` | 符号 bitvector 长度 | MASKTYPEI.log, MASKTYPEV.log, MASKTYPEX.log, MVVCOMPRESS.log, MVVMATYPE.log, MVVTYPE.log, MVXMATYPE.log, MVXTYPE.log |
| 100 | `extensions/V/vext_control.sail:84` | `read_vreg` 相关初始化路径 | `vector_init` | 符号 bitvector 长度 | MOVETYPEV.log, VAESDF.log, VAESDM.log, VAESEF.log, VAESEM.log, VAESKF1_VI.log, VAESKF2_VI.log, VAESZ_VS.log |
| 66 | `-` | `-` | `zpmpCheck` | 循环上限 | AMO.log, LOAD.log, LOADRES.log, STORE.log, STORECON.log, ZICBOM.log, ZICBOP.log, ZICBOZ.log |
| 30 | `-` | `-` | `zinit_masked_result_cmp` | 循环上限 | VCPOP_M.log, VFIRST_M.log, VMSBF_M.log, VMSIF_M.log, VMSOF_M.log |
| 10 | `-` | `-` | `zcarryless_mul` | 循环上限 | CLMUL.log, CLMULH.log |
| 8 | `prelude/prelude.sail:93` | `zeros` | `zeros` | 符号 bitvector 长度 | VIMTYPE.log, VVMTYPE.log, VXMTYPE.log, XPERM8.log |
| 8 | `-` | `-` | `zcount_ones` | 循环上限 | CPOP.log, CPOPW.log |
| 8 | `-` | `-` | `zflush_TLB` | 循环上限 | SFENCE_VMA.log, SINVAL_VMA.log |
| 6 | `extensions/V/vext_mem_insts.sail:177/238/365` | 向量访存断言 | `sail_assert` | 断言失败 | VLSEGFFTYPE.log, VSSEGTYPE.log, VSSSEGTYPE.log |
| 5 | `-` | `-` | `zcarryless_mulr` | 循环上限 | CLMULR.log |
| 5 | `-` | `-` | `zinit_masked_result_carry` | 循环上限 | MMTYPE.log |
| 4 | `prelude/prelude.sail:89` | `sign_extend` | `extension` | 符号 bitvector 长度 | MOVETYPEI.log, VIMCTYPE.log |
| 3 | `-` | `-` | `zread_vreg` | 循环上限 | VMTYPE.log, VSRETYPE.log |
| 2 | `extensions/K/zbkx_insts.sail:54` | `execute` | `subrange_internal` | 符号 bitvector 长度 | XPERM4.log |
| 2 | `extensions/K/zbkx_insts.sail:29` | `execute` | `subrange_internal` | 符号 bitvector 长度 | XPERM8.log |
| 2 | `extensions/K/zbkb_insts.sail:74/97` | `execute` | `sail_assert` | 断言失败 | ZIP.log, UNZIP.log |
| 1 | `extensions/V/vext_control.sail:71` | `read_single_element` | `subrange_internal` | 符号 bitvector 长度 | VSRETYPE.log |
| 1 | `-` | `-` | `zexecute` | 循环上限 | XPERM4.log |

## 超时 clause

本次 `status.timeout.log` 中共有 17 个超时项：

`AMO`, `AES64ESM`, `AES64DSM`, `DIV`, `DIVW`, `LOAD`, `LOADRES`, `MOVETYPEX`, `NVSTYPE`, `NVTYPE`, `STORE`, `STORECON`, `VLRETYPE`, `VLSEGTYPE`, `VLSSEGTYPE`, `VLXSEGTYPE`, `VSXSEGTYPE`

## 简单修改建议

1. 优先看 `zeros` / `vector_init` 的符号长度问题。建议在 sail-riscv 高频调用点尽量使用具体宽度或按合法 SEW/LMUL 分支，避免继续传递符号化长度。
2. `zpmpCheck` 影响访存类指令。短期可考虑提高 loop limit 或简化测试配置；长期建议给常见的“无 PMP 限制”路径做快速处理。
3. `zinit_masked_result_cmp` / `zinit_masked_result_carry` 属于向量掩码初始化循环。建议先按合法元素数量分支，必要时再在 isla 侧做简单 fast-path。
4. `zcarryless_mul*`、`zcount_ones`、`zreverse_bits` 是典型位运算循环。建议后续用专用 primop 或直接 SMT 表达式处理，不建议单纯扩大全局 loop limit。
5. `sail_assert` 的 8 次失败先检查输入约束是否过宽，再判断是否需要调整 sail-riscv 断言或测试配置。

## 复现统计口径

```sh
rg -n '执行错误' output/log -g '*.log'
wc -l output/status.intime.log output/status.timeout.log
```
