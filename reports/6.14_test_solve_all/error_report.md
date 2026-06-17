# output 执行错误函数定位报告

- 生成方式：在仓库根目录通过 `python3` 命令行脚本扫描 `output/log/*.log` 并覆盖写入本文件。
- 数据来源：`output/log/*.log`
- 过滤口径：已按用户要求忽略浮点相关错误；过滤条件包括 `riscv_f*`/`*ToF*`/SoftFloat、`extensions/FD`、`extensions/bfloat16`、`vext_fp*`，以及明显的浮点指令日志名。
- 日志文件数：347；包含执行错误的日志文件数：187
- 原始执行错误总数：2093；已过滤浮点相关错误：1591；纳入本报告的非浮点执行错误：502
- 纳入本报告的日志文件数：121

## 结论

1. 非浮点错误最高频的是 `zeros`（301 次，类型：符号 bitvector 长度）。
2. 主要问题集中在符号 bitvector 长度处理、向量控制/掩码相关 `subrange_internal` 类型错误，以及若干 Sail 函数循环超过 isla loop limit。
3. 明确缺失函数/primop：`sys_enable_experimental_extensions`；如果当前代码已补实现，`output/log` 仍代表旧运行快照。
4. 循环上限问题集中在 `zpmpCheck`、`zflush_TLB`、`zcarryless_mul*`、`zcount_ones`、`zreverse_bits` 等函数。

## 按错误类型统计

| 错误类型 | 次数 |
|---|---:|
| 符号 bitvector 长度 | 325 |
| 类型错误 | 90 |
| 循环上限 | 73 |
| 缺失函数/primop | 12 |
| 断言失败 | 2 |

## Top 问题函数/primop（非浮点）

| 次数 | 错误类型 | 问题函数/primop | 影响日志数 | 示例日志 | 示例消息 |
|---:|---|---|---:|---|---|
| 301 | 符号 bitvector 长度 | `zeros` | 89 | `LOAD.log:15` | Symbolic (bit)vector length in zeros(SymbolicLength("zeros", SourceLoc { file: 14, line1: 93, char1: 21, line2: 93, char2: 34 }))[prelude/prelude.sail 93:21 - 93:34] |
| 62 | 类型错误 | `subrange_internal` | 6 | `MMTYPE.log:32` | Type error: subrange_internal Poison I128(255) I128(0)(Type("subrange_internal Poison I128(255) I128(0)", SourceLoc { file: 51, line1: 151, char1: 54, line2: 151, char2: 80 }))[ex… |
| 39 | 循环上限 | `zpmpCheck` | 3 | `ZICBOM.log:38` | Executed loop in 3670 at 41 more than specified limit(LoopLimitReached(Name("zpmpCheck"), 41))[0:0 - 0:0] |
| 18 | 符号 bitvector 长度 | `subrange_internal` | 7 | `MOVETYPEX.log:27` | Symbolic (bit)vector length in subrange_internal(SymbolicLength("subrange_internal", SourceLoc { file: 83, line1: 227, char1: 4, line2: 227, char2: 24 }))[extensions/V/vext_utils_… |
| 12 | 缺失函数/primop | `sys_enable_experimental_extensions` | 2 | `BITYPE.log:24` | NoFunction("sys_enable_experimental_extensions", SourceLoc { file: 28, line1: 75, char1: 41, line2: 75, char2: 77 }) |
| 11 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 0, len: 64 })` | 7 | `LOADRES.log:19` | Type("%i64->%i Bits(B129 { tag: false, bits: 0, len: 64 })", SourceLoc { file: -1, line1: 1642, char1: 0, line2: 0, char2: 0 }) |
| 10 | 循环上限 | `zcarryless_mul` | 2 | `CLMUL.log:19` | Executed loop in 2853 at 27 more than specified limit(LoopLimitReached(Name("zcarryless_mul"), 27))[0:0 - 0:0] |
| 8 | 循环上限 | `zcount_ones` | 2 | `CPOP.log:17` | Executed loop in 2864 at 23 more than specified limit(LoopLimitReached(Name("zcount_ones"), 23))[0:0 - 0:0] |
| 8 | 循环上限 | `zflush_TLB` | 2 | `SFENCE_VMA.log:33` | Executed loop in 4418 at 25 more than specified limit(LoopLimitReached(Name("zflush_TLB"), 25))[0:0 - 0:0] |
| 5 | 循环上限 | `zcarryless_mulr` | 1 | `CLMULR.log:19` | Executed loop in 2855 at 23 more than specified limit(LoopLimitReached(Name("zcarryless_mulr"), 23))[0:0 - 0:0] |
| 4 | 符号 bitvector 长度 | `extension` | 2 | `MOVETYPEI.log:25` | Symbolic (bit)vector length in extension(SymbolicLength("extension", SourceLoc { file: 14, line1: 89, char1: 29, line2: 89, char2: 51 }))[prelude/prelude.sail 89:29 - 89:51] |
| 2 | 符号 bitvector 长度 | `slice_internal` | 1 | `AMO.log:24` | Symbolic (bit)vector length in slice_internal(SymbolicLength("slice_internal", SourceLoc { file: 14, line1: 101, char1: 23, line2: 101, char2: 37 }))[prelude/prelude.sail 101:23 -… |
| 2 | 循环上限 | `zreverse_bits` | 1 | `BREV8.log:13` | Executed loop in 2751 at 23 more than specified limit(LoopLimitReached(Name("zreverse_bits"), 23))[0:0 - 0:0] |
| 2 | 断言失败 | `sail_assert` | 2 | `UNZIP.log:11` | Assertion failure: extensions/K/zbkb_insts.sail:97.19-97.20(AssertionFailure(Some("extensions/K/zbkb_insts.sail:97.19-97.20"), SourceLoc { file: 95, line1: 97, char1: 2, line2: 97… |
| 2 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 2, len: 64 })` | 2 | `VLSSEGTYPE.log:55` | Type("%i64->%i Bits(B129 { tag: false, bits: 2, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 2 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 4, len: 64 })` | 1 | `VMVRTYPE.log:47` | Type("%i64->%i Bits(B129 { tag: false, bits: 4, len: 64 })", SourceLoc { file: -1, line1: 14521, char1: 0, line2: 0, char2: 0 }) |
| 2 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 1229782938314412309, len: 64 })` | 2 | `VSSEGTYPE.log:53` | Type("%i64->%i Bits(B129 { tag: false, bits: 1229782938314412309, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 18446744072635809792, len: 64 })` | 1 | `VLRETYPE.log:26` | Type("%i64->%i Bits(B129 { tag: false, bits: 18446744072635809792, len: 64 })", SourceLoc { file: -1, line1: 8058, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 279075704882888661, len: 64 })` | 1 | `VLSEGFFTYPE.log:32` | Type("%i64->%i Bits(B129 { tag: false, bits: 279075704882888661, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 27197519624740864, len: 64 })` | 1 | `VLSEGFFTYPE.log:46` | Type("%i64->%i Bits(B129 { tag: false, bits: 27197519624740864, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 4611686018905539009, len: 64 })` | 1 | `VLSEGTYPE.log:32` | Type("%i64->%i Bits(B129 { tag: false, bits: 4611686018905539009, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 70412322734089, len: 64 })` | 1 | `VLSEGTYPE.log:46` | Type("%i64->%i Bits(B129 { tag: false, bits: 70412322734089, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 288230376151711744, len: 64 })` | 1 | `VLSSEGTYPE.log:32` | Type("%i64->%i Bits(B129 { tag: false, bits: 288230376151711744, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 1804261760425926689, len: 64 })` | 1 | `VLSSEGTYPE.log:46` | Type("%i64->%i Bits(B129 { tag: false, bits: 1804261760425926689, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 4611686018427387904, len: 64 })` | 1 | `VSRETYPE.log:15` | Type("%i64->%i Bits(B129 { tag: false, bits: 4611686018427387904, len: 64 })", SourceLoc { file: -1, line1: 8058, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 1, len: 64 })` | 1 | `VSRETYPE.log:22` | Type("%i64->%i Bits(B129 { tag: false, bits: 1, len: 64 })", SourceLoc { file: -1, line1: 8058, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 288, len: 64 })` | 1 | `VSSEGTYPE.log:30` | Type("%i64->%i Bits(B129 { tag: false, bits: 288, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 类型错误 | `%i64->%i Bits(B129 { tag: false, bits: 18, len: 64 })` | 1 | `VSSSEGTYPE.log:30` | Type("%i64->%i Bits(B129 { tag: false, bits: 18, len: 64 })", SourceLoc { file: -1, line1: 7814, char1: 0, line2: 0, char2: 0 }) |
| 1 | 循环上限 | `zexecute` | 1 | `XPERM4.log:18` | Executed loop in 4470 at 37704 more than specified limit(LoopLimitReached(Name("zexecute"), 37704))[0:0 - 0:0] |

## Top 调用位置/所在 Sail 函数（非浮点）

| 次数 | 源位置 | 所在 Sail 函数 | 问题函数/primop | 错误类型 | 影响日志示例 |
|---:|---|---|---|---|---|
| 230 | `/home/baiyifan/.opam/default/bin/../share/sail/lib/vector.sail:396` | `sail_ones` | `zeros` | 符号 bitvector 长度 | MASKTYPEI.log, MASKTYPEV.log, MASKTYPEX.log, MVVCOMPRESS.log, MVVMATYPE.log, MVVTYPE.log, MVXMATYPE.log, MVXTYPE.log |
| 71 | `prelude/prelude.sail:93` | `zeros` | `zeros` | 符号 bitvector 长度 | LOAD.log, MOVETYPEV.log, VAESDF.log, VAESDM.log, VAESEF.log, VAESEM.log, VAESKF1_VI.log, VAESKF2_VI.log |
| 45 | `extensions/V/vext_control.sail:151` | `read_vmask` | `subrange_internal` | 类型错误 | MMTYPE.log, VCPOP_M.log, VMSBF_M.log, VMSIF_M.log, VMSOF_M.log |
| 39 | `-` | `-` | `zpmpCheck` | 循环上限 | ZICBOM.log, ZICBOP.log, ZICBOZ.log |
| 17 | `extensions/V/vext_control.sail:61` | `read_single_element` | `subrange_internal` | 类型错误 | VMTYPE.log |
| 12 | `-` | `-` | `sys_enable_experimental_extensions` | 缺失函数/primop | BITYPE.log, VABS_V.log |
| 11 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 0, len: 64 })` | 类型错误 | LOADRES.log, VLSEGFFTYPE.log, VLSEGTYPE.log, VLSSEGTYPE.log, VMVRTYPE.log, VSSEGTYPE.log, VSSSEGTYPE.log |
| 10 | `-` | `-` | `zcarryless_mul` | 循环上限 | CLMUL.log, CLMULH.log |
| 10 | `extensions/V/vext_utils_insts.sail:227` | `get_scalar` | `subrange_internal` | 符号 bitvector 长度 | MOVETYPEX.log, VMVSX.log, VXMCTYPE.log |
| 8 | `-` | `-` | `zcount_ones` | 循环上限 | CPOP.log, CPOPW.log |
| 8 | `-` | `-` | `zflush_TLB` | 循环上限 | SFENCE_VMA.log, SINVAL_VMA.log |
| 5 | `-` | `-` | `zcarryless_mulr` | 循环上限 | CLMULR.log |
| 4 | `prelude/prelude.sail:89` | `sign_extend` | `extension` | 符号 bitvector 长度 | MOVETYPEI.log, VIMCTYPE.log |
| 2 | `prelude/prelude.sail:101` | `trunc` | `slice_internal` | 符号 bitvector 长度 | AMO.log |
| 2 | `-` | `-` | `zreverse_bits` | 循环上限 | BREV8.log |
| 2 | `extensions/I/base_insts.sail:322` | `execute` | `subrange_internal` | 符号 bitvector 长度 | STORE.log |
| 2 | `extensions/A/zalrsc_insts.sail:70` | `execute` | `subrange_internal` | 符号 bitvector 长度 | STORECON.log |
| 2 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 2, len: 64 })` | 类型错误 | VLSSEGTYPE.log, VMVRTYPE.log |
| 2 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 4, len: 64 })` | 类型错误 | VMVRTYPE.log |
| 2 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 1229782938314412309, len: 64 })` | 类型错误 | VSSEGTYPE.log, VSSSEGTYPE.log |
| 2 | `extensions/K/zbkx_insts.sail:54` | `execute` | `subrange_internal` | 符号 bitvector 长度 | XPERM4.log |
| 2 | `extensions/K/zbkx_insts.sail:29` | `execute` | `subrange_internal` | 符号 bitvector 长度 | XPERM8.log |
| 1 | `extensions/K/zbkb_insts.sail:97` | `execute` | `sail_assert` | 断言失败 | UNZIP.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 18446744072635809792, len: 64 })` | 类型错误 | VLRETYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 279075704882888661, len: 64 })` | 类型错误 | VLSEGFFTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 27197519624740864, len: 64 })` | 类型错误 | VLSEGFFTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 4611686018905539009, len: 64 })` | 类型错误 | VLSEGTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 70412322734089, len: 64 })` | 类型错误 | VLSEGTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 288230376151711744, len: 64 })` | 类型错误 | VLSSEGTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 1804261760425926689, len: 64 })` | 类型错误 | VLSSEGTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 4611686018427387904, len: 64 })` | 类型错误 | VSRETYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 1, len: 64 })` | 类型错误 | VSRETYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 288, len: 64 })` | 类型错误 | VSSEGTYPE.log |
| 1 | `-` | `-` | `%i64->%i Bits(B129 { tag: false, bits: 18, len: 64 })` | 类型错误 | VSSSEGTYPE.log |
| 1 | `-` | `-` | `zexecute` | 循环上限 | XPERM4.log |
| 1 | `extensions/K/zbkb_insts.sail:74` | `execute` | `sail_assert` | 断言失败 | ZIP.log |

## 建议优先级

1. 优先看 `zeros`/`extension`/`slice_internal`/`subrange_internal` 这类 primop 对符号化长度或 Poison 参数的处理，因为它们影响日志数最多。
2. 再看 `zpmpCheck`、`zflush_TLB`、`zcarryless_mul*` 等循环上限，判断是需要提高 loop limit、改 Sail 实现，还是在 isla 中增加专用 primop/化简。
3. `sys_enable_experimental_extensions` 属于明确缺失接口；若代码已修，需重新生成 `output/log` 后再复扫确认。

## 复现命令

```sh
rg -n '执行错误' output/log -g '*.log'
python3 - <<'PY'
# 读取 output/log/*.log；过滤浮点相关项；按错误类型、问题函数/primop、源码位置聚合；写入 report.md。
# 本报告已由上述口径的命令行 Python 脚本生成。
PY
```
