# Isla Bug 报错与分析报告（6.16）

本文档仿照 `reports/6.14_test_solve_all`，基于用户已运行的 `make solve` 输出整理。2026-06-17 已按本报告中的高频问题完成一轮代码修正，修改范围为当前仓库和 `../sail-riscv`。2026-06-18 追加修正：`../sail-riscv` 中所有 Isla 专用 fast-path 均改为 `$ifdef SYMBOLIC` 条件编译，并由 `__isla_use_extra_ops` 运行时开关控制；随后按语义边界二次调整，将 B/K 位操作 fast-path 从指令 execute 下沉到 `count_ones`、`carryless_mul`、`carryless_mulr`、`brev8`、`xperm4`、`xperm8` 等 helper 内部，指令 execute 恢复为原本的直接语义调用。

> **同步说明（2026-06-17）**
>
> - 原始统计仍来自本报告生成时的 `output/`，不重写为后续 targeted run 的统计。
> - 本次同步追加已落地修复、验证命令、复验结果和剩余风险。
> - `rv64d.ir` 已由 `../sail-riscv/build/model/rv64d.ir` 重新生成并同步到当前仓库。
> - 2026-06-18 追加同步：RISC-V 位操作 primop 已统一改名为通用 `isla_*`，sail-riscv 侧通过 `$ifdef SYMBOLIC` 和 `__isla_use_extra_ops` 保护，避免影响非 Isla 后端或未启用 extra ops 的平台。
> - 2026-06-18 二次同步：`CPOP` / `CLMUL` / `BREV8` / `XPERM` 等指令层不再包 `execute_*_default` fast-path；Isla 替换点改在共享 helper 内部，默认 helper 仍保留原 Sail 循环实现。
> - 2026-06-18 全量复跑同步：再次执行 `make solve -j32`，已清除 `LPAD` panic、`ZIP`/`UNZIP` assertion、`zrev8`/`zvrev8`、`zwrite_velem_oct_vec` 等本轮目标问题；剩余错误重新统计见第 13 节。

> **运行概况**
>
> - 数据来源：`output/log/*.log`
> - 日志文件数：258
> - intime：241
> - timeout：17
> - 含执行错误的日志文件数：118
> - 执行错误总数：528

> **相比 6.14 的变化**
>
> - 已消失：`sys_enable_experimental_extensions` 缺失函数、`%i64->%i Bits(...)` 类型转换、`subrange_internal Poison` 类型错误、`slice_internal` 符号长度。
> - 仍高频：`zeros` / `ones` 的符号长度问题。
> - 新浮现：`vector_init` 符号长度，以及 `zinit_masked_result_cmp` / `zinit_masked_result_carry` 循环上限。
> - 错误类型更集中：当前只剩符号 bitvector 长度、循环上限、断言失败三类。

---

## 0. 本轮落地修正概览（2026-06-17）

### Isla 侧

- `isla-lib/src/primop.rs`
  - 为 `zeros` / `ones` / `get_slice_int` / `extension` / `subrange_internal` 增加“符号长度可由 SMT 证明为具体常量时继续执行”的处理。
  - 补齐 `slice_internal` / `subrange_internal` 对 `Poison` 的传播。
  - 新增向量辅助 primop：`isla_read_vreg`、`isla_init_mask`、`isla_vector_select`、`isla_masktypei_result`、`isla_masktypev_result`、`isla_pack_vreg`。
  - 新增通用 Isla 位操作 primop：`isla_count_ones`、`isla_carryless_mul`、`isla_carryless_mulr`、`isla_xperm4`、`isla_xperm8`、`isla_clmul`、`isla_clmulh`、`isla_clmulr`、`isla_cpop`、`isla_cpopw`、`isla_brev8`。其中 helper 层使用 `isla_count_ones` / `isla_carryless_mul*` / `isla_brev8` / `isla_xperm*`，旧的 `isla_cpop*` / `isla_clmul*` 保留为兼容 wrapper。
  - 修正 `smt_carryless_mul` 中 zero-extend 和移位常量宽度，避免生成错误宽度的 SMT 表达式；补测 `isla_carryless_mul` 纯符号与 concrete/symbolic 混合路径均返回 2 倍操作数宽度。

### sail-riscv 侧

- `model/core/arithmetic.sail`
  - 在 `$ifdef SYMBOLIC` 中声明 `__isla_use_extra_ops : bool = false`，保证 `arithmetic.sail` 内部 helper 可在加载顺序上引用该开关；默认不启用 Isla 专用 fast-path。
  - `count_ones`、`carryless_mul`、`carryless_mulr`、`brev8` 拆出 `*_default` 原实现；原 helper 名称仅在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用 Isla primop，否则调用默认 Sail 循环。
- `model/extensions/V/vext_control.sail`
  - `isla_read_vreg` / `isla_pack_vreg` 的声明只在 `$ifdef SYMBOLIC` 下可见。
  - `read_vreg` / `write_vreg` 仅在 `__isla_use_extra_ops` 为 true 时走 Isla helper；否则保留原逐元素读写语义。
  - `read_vmask` / `read_vmask_carry` 仅在 `__isla_use_extra_ops` 为 true 时走常见 `num_elem` 分派；否则保留原始 helper。
- `model/extensions/V/vext_utils_insts.sail`
  - `isla_init_mask`、`isla_vector_select`、`isla_masktypei_result`、`isla_masktypev_result` 的声明只在 `$ifdef SYMBOLIC` 下可见。
  - `init_masked_result`、`init_masked_result_carry`、`init_masked_result_cmp` 仅在 `__isla_use_extra_ops` 为 true 时返回原 `vd_val` 加 `isla_init_mask(...)`；否则保留原逐元素 mask 初始化循环。
  - 新增 `sign_extend_simm_to_sew`，避免部分立即数路径继续产生符号目标宽度。
- `model/extensions/V/vext_arith_insts.sail`
  - `MOVETYPEV`、`MOVETYPEX`、`MASKTYPEI`、`MASKTYPEV`、`MASKTYPEX` 的 Isla helper 路径均受 `__isla_use_extra_ops` 保护，默认分支保留原 Sail 循环。
  - 相关立即数路径改用 `sign_extend_simm_to_sew`。
- `model/extensions/B/zbc_insts.sail`
  - `CLMUL` / `CLMULH` / `CLMULR` execute 恢复为直接调用 `carryless_mul` / `carryless_mulr`；fast-path 由这些 helper 内部决定。
- `model/extensions/B/zbb_insts.sail`
  - `CPOP` / `CPOPW` execute 恢复为直接调用 `count_ones`；fast-path 由 `count_ones` 内部决定。
- `model/extensions/K/zbkb_insts.sail`
  - `BREV8` execute 恢复为直接调用 `brev8`；fast-path 由 `brev8` 内部决定。
  - `ZIP` / `UNZIP` 恢复默认 `assert(xlen == 32)` 语义，不再额外改写为 Isla 专用非法指令分支。
- `model/extensions/K/zbkx_insts.sail`
  - 新增 `xperm4` / `xperm8` helper；execute 仅调用 helper 并写回寄存器。helper 在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用 `isla_xperm*`，否则保留原逐元素置换实现。
- 当前仓库 `configs/riscv32.toml`、`configs/riscv64.toml`、`configs/riscv64_difftest.toml`、`configs/riscv64_ubuntu.toml`
  - 在 `[registers.defaults]` 中设置 `"__isla_use_extra_ops" = true`，使 Isla RISC-V 配置显式启用上述 fast-path；未设置该寄存器的平台仍走默认 Sail 语义。

### 验证结果

已通过：

```sh
cargo fmt --check
cargo test -p isla-lib primop::tests -- --nocapture
cargo check -p isla-lib
PATH=/home/baiyifan/workplace-local/isla-runner/isla/isla-sail:$PATH cmake --build build --target generated_isla_rv64d
cmp -s rv64d.ir ../sail-riscv/build/model/rv64d.ir
make solve-CLMUL
```

已 targeted 复验且日志中无执行错误：

```text
CLMUL, CLMULH, CLMULR, CPOP, CPOPW, BREV8, ZIP, UNZIP,
MOVETYPEV, MASKTYPEI, MASKTYPEV, VSRETYPE,
MASKTYPEX, MVVTYPE, MVVMATYPE, MVXMATYPE
```

`VIMTYPE` 原先的 `zinit_masked_result_carry` 已消失，但 targeted run 仍剩整体 `zexecute` 循环上限：

```text
LoopLimitReached(Name("zexecute"), 32914)
```

这属于更大粒度的向量算术主执行循环，不是本轮已替换的 helper 初始化循环。

---

## 1. `zeros` / `ones` — 符号化长度参数

### Bug 报错

```text
Symbolic (bit)vector length in zeros(SymbolicLength("zeros", ...))[vector.sail 396:32 - 396:45]
```

出现次数：273；影响日志数：68。

### 触发指令（Clause Name）

主要包括：

MASKTYPEI、MASKTYPEV、MASKTYPEX、MVVCOMPRESS、MVVMATYPE、MVVTYPE、MVXMATYPE、MVXTYPE、NISTYPE、NITYPE、NVSTYPE、NVTYPE、NXSTYPE、NXTYPE、RIVVTYPE、RMVVTYPE、VABS_V、VANDN_VV、VANDN_VX、VBREV8_V、VBREV_V、VCLMULH_VV、VCLMULH_VX、VCLMUL_VV、VCLMUL_VX、VCLZ_V、VCPOP_V、VCTZ_V、VEXTTYPE、VICMPTYPE、VID_V、VIMSTYPE、VIMTYPE、VIOTA_M、VISG、VITYPE、VLSEGFFTYPE、VLSEGTYPE、VLSSEGTYPE、VREV8_V、VROL_VV、VROL_VX、VROR_VI、VROR_VV、VROR_VX、VSSEGTYPE、VSSSEGTYPE、VVCMPTYPE、VVMSTYPE、VVMTYPE、VWSLL_VI、VWSLL_VV、VWSLL_VX、VXCMPTYPE、VXMSTYPE、VXMTYPE、VXSG、VXTYPE、WMVVTYPE、WMVXTYPE、WVTYPE、WVVTYPE、WVXTYPE、WXTYPE、XPERM8、ZVABDTYPE、ZVWABDATYPE 等。

主要触发路径：

- `sail_ones` 内部调用 `zeros`（`vector.sail:396`）→ 265 次
- `zeros` 直接调用（`prelude/prelude.sail:93`）→ 8 次

### 对应 sail-riscv 函数

```sail
val zeros : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function zeros (n) = sail_zeros(n)

val ones : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function ones (n) = sail_ones(n)
```

`zeros(n)` / `ones(n)` 返回长度为 `n` 的全 0 / 全 1 位向量。`n` 是类型级别隐式参数，在 sail-riscv 实际执行中通常是 8、16、32、64、256 等具体宽度，但在 isla 符号执行中可能变成符号长度。

### 本轮处理

- isla 侧为 `zeros` / `ones` 增加可证明符号长度具体化：当 SMT 能证明长度等于常见固定值时，按具体长度继续执行。
- sail-riscv 侧高频向量路径改用 `isla_init_mask` / `isla_vector_select` / `isla_masktype*` 等 helper，减少隐式长度继续流入 `zeros()` / `ones()`。
- 复验日志中，`MOVETYPEV`、`MASKTYPEI`、`MASKTYPEV`、`MASKTYPEX`、`MVVTYPE`、`MVVMATYPE`、`MVXMATYPE` 已不再出现 `zeros` / `ones` 符号长度执行错误。

### 剩余风险

这不是全量 `make solve` 后的重新统计，仍需后续全量跑完后更新 273 次原始计数是否归零。

---

## 2. `vector_init` — 符号化长度

### Bug 报错

```text
Symbolic (bit)vector length in vector_init(SymbolicLength("vector_init", ...))[extensions/V/vext_control.sail 84:40 - 84:71]
```

出现次数：100；影响日志数：21。

### 触发指令（Clause Name）

MOVETYPEV、VAESDF、VAESDM、VAESEF、VAESEM、VAESKF1_VI、VAESKF2_VI、VAESZ_VS、VGHSH_VV、VGMUL_VV、VMVRTYPE、VMVSX、VMVXS、VSHA2MS_VV、VSM3C_VI、VSM3ME_VV、VSM4K_VI、VVMCTYPE、VXMCTYPE、ZVKSHA2TYPE、ZVKSM4RTYPE。

### 对应 sail-riscv 函数

`vector_init` 位于 `extensions/V/vext_control.sail:84`，用于向量寄存器或向量中间结果初始化。当前报错说明该调用点仍然依赖隐式长度，isla 无法构造符号长度的 bitvector。

### 本轮处理

- `read_vreg` 在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时按 SEW/num_elem 分派，并调用 `isla_read_vreg` 直接从最多 8 个向量寄存器切分元素；默认分支保留原逐元素读取。
- `write_vreg` 在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用 `isla_pack_vreg` 打包寄存器组；默认分支保留原逐元素写回。
- `MASKTYPEX` 原先在 `vext_arith_insts.sail:832` 的 `vector_init(zeros())` 路径只在 `__isla_use_extra_ops` 开启时改用 `isla_masktypei_result(...)`；默认分支保留原循环。

### 复验结果

`MOVETYPEV`、`MASKTYPEX` 的 targeted 日志不再出现 `vector_init` 符号长度执行错误。

---

## 3. `zpmpCheck` — PMP 检查循环上限

### Bug 报错

```text
Executed loop in 3670 at 41 more than specified limit(LoopLimitReached(Name("zpmpCheck"), 41))[0:0 - 0:0]
```

出现次数：66；影响日志数：8。

### 触发指令（Clause Name）

AMO、LOAD、LOADRES、STORE、STORECON、ZICBOM、ZICBOP、ZICBOZ。

### 对应 sail-riscv 函数

`zpmpCheck` 是 PMP（Physical Memory Protection）检查逻辑，会遍历 PMP 配置项。访存类指令都会经过该路径，因此影响面比较广。

### 本轮状态

本轮未修改 `zpmpCheck`。该问题仍保留为后续访存路径优化项：短期可以考虑提高 loop limit 或在配置中减少 PMP 复杂度；长期更合适的是在 isla 侧为“未配置 PMP / 默认放行”这类常见情况加 fast-path，避免每次访存都完整展开 PMP 循环。

---

## 4. `zinit_masked_result_cmp` / `zinit_masked_result_carry` — 掩码结果初始化循环上限

### Bug 报错

```text
Executed loop in 4797 at 62 more than specified limit(LoopLimitReached(Name("zinit_masked_result_cmp"), 62))[0:0 - 0:0]
Executed loop in 4796 at 60 more than specified limit(LoopLimitReached(Name("zinit_masked_result_carry"), 60))[0:0 - 0:0]
```

出现次数：30（cmp）+ 5（carry）；影响日志数：5 + 1。

### 触发指令（Clause Name）

- `zinit_masked_result_cmp`：VCPOP_M、VFIRST_M、VMSBF_M、VMSIF_M、VMSOF_M
- `zinit_masked_result_carry`：MMTYPE

### 对应 sail-riscv 函数

这两个函数是 V 扩展中初始化 masked-result 的辅助逻辑，内部按元素个数循环。6.14 中 `read_vmask` 的 Poison 类型错误消失后，执行能继续走到这里，因此循环上限问题暴露出来。

### 本轮处理

- `init_masked_result`、`init_masked_result_carry`、`init_masked_result_cmp` 已改为返回 `(vd_val, isla_init_mask(...))`。
- `isla_init_mask` 在 Isla 侧直接构造 active mask，避免 Sail foreach 逐元素展开。

### 复验结果

- `VIMTYPE` 中原先的 `zinit_masked_result_carry` 不再出现。
- `VIMTYPE` targeted run 仍剩 `zexecute` loop limit，这是主执行循环，不是该 helper 循环。

---

## 5. `extension`（sign_extend / zero_extend）— 符号化长度

### Bug 报错

```text
Symbolic (bit)vector length in extension(SymbolicLength("extension", ...))[prelude/prelude.sail 89:29 - 89:51]
```

出现次数：4；影响日志数：2。

### 触发指令（Clause Name）

MOVETYPEI、VIMCTYPE。

### 对应 sail-riscv 函数

```sail
val sign_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function sign_extend(m, v) = sail_sign_extend(v, m)

val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function zero_extend(m, v) = sail_zero_extend(v, m)
```

目标长度 `m` 是隐式参数。实际运行中宽度通常是固定合法值，但 isla 符号执行看到的是符号长度。

### 本轮处理

- sail-riscv 侧新增 `sign_extend_simm_to_sew`，`MASKTYPEI` / `VITYPE` / `MOVETYPEI` 等立即数路径改为按 SEW 分派。
- isla 侧 `extension` 增加可证明符号目标长度具体化。

### 复验结果

`MVVTYPE` targeted 日志不再出现 `extension` 符号长度执行错误。

---

## 6. `subrange_internal` — 符号化子范围

### Bug 报错

```text
Symbolic (bit)vector length in subrange_internal(SymbolicLength("subrange_internal", ...))
```

出现次数：5；影响日志数：3。

### 触发指令（Clause Name）

VSRETYPE、XPERM4、XPERM8。

主要位置：

- `extensions/V/vext_control.sail:71`
- `extensions/K/zbkx_insts.sail:29`
- `extensions/K/zbkx_insts.sail:54`

### 对应 sail-riscv 函数

`subrange_internal` 是 Sail 编译器为 `v[high .. low]` 生成的内部函数。它本身不能直接修改，只能修改 sail-riscv 中触发该 slice 的调用点。

### 本轮处理

- `XPERM4` / `XPERM8` 在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用 `isla_xperm4` / `isla_xperm8` primop；默认分支保留原逐元素置换实现。
- isla 侧 `subrange_internal` 增加可证明符号 high/low 的具体化，并补齐 `Poison` 传播。

### 复验结果

`XPERM4`、`XPERM8`、`VSRETYPE` targeted 日志不再出现 `subrange_internal` 符号长度执行错误。

---

## 7. `zcarryless_mul` / `zcarryless_mulr` — 无进位乘法循环上限

### Bug 报错

```text
Executed loop in 2853 at 27 more than specified limit(LoopLimitReached(Name("zcarryless_mul"), 27))[0:0 - 0:0]
Executed loop in 2855 at 23 more than specified limit(LoopLimitReached(Name("zcarryless_mulr"), 23))[0:0 - 0:0]
```

出现次数：10（mul）+ 5（mulr）；影响日志数：2 + 1。

### 触发指令（Clause Name）

CLMUL、CLMULH、CLMULR。

### 对应 sail-riscv 函数

`carryless_mul` 是 GF(2) 上的无进位乘法，Sail 实现通过 foreach 逐位累积异或结果。语义正确，但对符号执行不友好。

### 本轮处理

- isla 侧新增通用 `isla_clmul` / `isla_clmulh` / `isla_clmulr` primop。
- sail-riscv 的 `CLMUL` / `CLMULH` / `CLMULR` 仅在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用这些 primop；默认保留 `carryless_mul` / `carryless_mulr` 原实现。
- 同时修正 Isla 侧 `smt_carryless_mul` 的 zero-extend 和移位常量宽度：
  - 主 symbolic 路径中，右操作数扩展到 `2 * len` 位，移位量宽度与被移位 bitvector 对齐。
  - concrete/symbolic 单比特快捷分支中，`ZeroExtend` 使用“增加 `len` 位”而不是误用目标宽度 `2 * len` 作为扩展量，避免结果变成 `3 * len` 位。
  - 新增单测确认 `isla_carryless_mul` 在 pure symbolic 和 mixed symbolic 路径都返回 2 倍宽度。

### 复验结果

`CLMUL`、`CLMULH`、`CLMULR` targeted 日志不再出现 `zcarryless_mul` / `zcarryless_mulr` loop limit。2026-06-18 单独重跑 `make solve-CLMUL`：命令返回 0，`output/log/CLMUL.log` 中未匹配到 `LoopLimitReached`、`zcarryless_mul` 或执行错误，`output/status.intime.log` 追加 `CLMUL intime`。

---

## 8. `zcount_ones` / `zreverse_bits` — 位操作循环上限

### Bug 报错

```text
Executed loop in 2864 at 23 more than specified limit(LoopLimitReached(Name("zcount_ones"), 23))[0:0 - 0:0]
Executed loop in 2751 at 23 more than specified limit(LoopLimitReached(Name("zreverse_bits"), 23))[0:0 - 0:0]
```

出现次数：8（count_ones）+ 2（reverse_bits）；影响日志数：2 + 1。

### 触发指令（Clause Name）

CPOP、CPOPW、BREV8。

### 本轮处理

- isla 侧新增通用 `isla_cpop` / `isla_cpopw` / `isla_brev8` primop。
- sail-riscv 的 `CPOP` / `CPOPW` / `BREV8` 仅在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用对应 primop；默认保留原 Sail 实现。

### 复验结果

`CPOP`、`CPOPW`、`BREV8` targeted 日志不再出现 `zcount_ones` / `zreverse_bits` loop limit。

---

## 9. `zflush_TLB` — TLB 刷新循环上限

### Bug 报错

```text
Executed loop in 4419 at 25 more than specified limit(LoopLimitReached(Name("zflush_TLB"), 25))[0:0 - 0:0]
```

出现次数：8；影响日志数：2。

### 触发指令（Clause Name）

SFENCE_VMA、SINVAL_VMA。

### 本轮状态

本轮未修改 `zflush_TLB`。该问题仍建议后续单独处理：TLB flush 在符号执行中可以考虑建模为整体失效，而不是逐项遍历；短期也可以通过减少默认 TLB 表项数或提高 loop limit 缓解。

---

## 10. `sail_assert` — 断言失败

### Bug 报错

```text
Assertion failure: extensions/K/zbkb_insts.sail:97.19-97.20(...)
Assertion failure: extensions/V/vext_mem_insts.sail:177.39-177.40(...)
```

出现次数：8；影响日志数：5。

### 触发指令（Clause Name）

UNZIP、ZIP、VLSEGFFTYPE、VSSEGTYPE、VSSSEGTYPE。

### 对应位置

- `extensions/K/zbkb_insts.sail:74`
- `extensions/K/zbkb_insts.sail:97`
- `extensions/V/vext_mem_insts.sail:177`
- `extensions/V/vext_mem_insts.sail:238`
- `extensions/V/vext_mem_insts.sail:365`

### 本轮处理

- `ZIP` / `UNZIP` 的 RV64 solve-state 路径只在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时，先对 `xlen != 32` 返回 `Illegal_Instruction()`；默认分支保留原 `assert(xlen == 32)` 语义，避免影响非 Isla 后端。
- `extensions/V/vext_mem_insts.sail` 中向量访存相关断言本轮未修改，仍需后续单独确认是输入约束过宽，还是可以在 sail-riscv 侧改成显式非法指令路径。

### 复验结果

`ZIP`、`UNZIP` targeted 日志不再出现 `sail_assert` 执行错误。`VLSEGFFTYPE`、`VSSEGTYPE`、`VSSSEGTYPE` 的向量访存断言不属于本轮已落地修复范围。

---

## 11. 其他零散循环上限

| 函数 | 次数 | 影响日志 | 本轮状态 |
|---|---:|---|---|
| `zread_vreg` | 3 | VMTYPE、VSRETYPE | `read_vreg` 已改为按 SEW/num_elem 分派并调用 `isla_read_vreg`；`VSRETYPE` targeted 复验不再报该循环 |
| `zexecute` | 1 | XPERM4 | `XPERM4` 的 `isla_xperm4` fast-path 已受 `$ifdef SYMBOLIC` 和 `__isla_use_extra_ops` 保护，targeted 复验不再报该循环；`VIMTYPE` 后续复验仍有新的 `zexecute` 主循环上限 |

### 剩余风险

`zread_vreg` 的原始统计仍需全量 `make solve` 重跑确认是否完全归零，尤其是 `VMTYPE`。`VIMTYPE` 剩余的 `zexecute` 不再是 `zinit_masked_result_carry` helper 循环，需要后续单独定位向量算术主执行循环来源。

---

## 12. 超时 clause

本次超时项共有 17 个：

`AMO`, `AES64ESM`, `AES64DSM`, `DIV`, `DIVW`, `LOAD`, `LOADRES`, `MOVETYPEX`, `NVSTYPE`, `NVTYPE`, `STORE`, `STORECON`, `VLRETYPE`, `VLSEGTYPE`, `VLSSEGTYPE`, `VLXSEGTYPE`, `VSXSEGTYPE`

### 本轮状态

本轮没有重写这 17 个原始 timeout 统计。已落地的 `zeros`、`vector_init`、向量 helper、位操作 primop 会降低一部分路径的符号展开成本，但访存检查、除法/AES 内部循环、向量访存路径仍可能继续造成 timeout。后续需要在全量 `make solve` 后重新统计 timeout 是否下降。

本轮 targeted run 中，部分目标仍可能因为主执行循环或路径规模超出限制而没有完全求解；本报告只把“日志中无执行错误”和“完全 intime/无 timeout”区分记录，避免把 targeted 结果覆盖原始全量统计。

---

## 13. 2026-06-18 全量 `make solve -j32` 复跑

### 本轮新增修复

- `src/isarch/exec.rs`
  - 修复 `LPAD` 触发的 panic：`FmtVal::from_val(...).unwrap()` 改为错误分支记录警告并跳过该路径，避免 `Poison` 格式化失败直接崩溃。
- `isla-lib/src/primop.rs`
  - 新增 `isla_rev8`，语义为按 byte 反转顺序，不同于 `isla_brev8` 的 byte 内 bit reverse。
  - 新增 `isla_vector_rev8`，用于向量 helper `vrev8` 的整体元素映射。
  - 增加 `isla_rev8_reverses_byte_order`、`isla_rev8_symbolic_path_preserves_width`、`isla_vector_rev8_maps_each_element` 单元测试。
- `../sail-riscv/model/core/arithmetic.sail`
  - `rev8` 拆出 `rev8_default`，仅在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为 true 时调用 `isla_rev8`。
- `../sail-riscv/model/extensions/V/vext_utils_insts.sail`
  - `vrev8` 拆出 `vrev8_default`，extra-op 开启时调用 `isla_vector_rev8`。
  - `write_velem_oct_vec` 拆出默认 loop，实现上仅在 extra-op 开启时展开 8 次 `write_single_element`，避免 helper loop limit；默认 Sail 语义保留。
- `../sail-riscv/model/extensions/K/zbkb_insts.sail`
  - `ZIP` / `UNZIP` 在 SYMBOLIC + extra-op 开启时，对 RV64 非法路径提前返回 `Illegal_Instruction()`；默认分支保留原 `assert(xlen == 32)`。

### 验证命令

已通过：

```sh
cargo fmt --check
cargo test -p isla-lib primop::tests -- --nocapture
cargo check -p isla-lib
PATH=/home/baiyifan/workplace-local/isla-runner/isla/isla-sail:$PATH cmake --build build --target generated_isla_rv64d
cmp -s rv64d.ir ../sail-riscv/build/model/rv64d.ir
make -j6 solve-VREV8_V solve-VSM3C_VI solve-VSM3ME_VV solve-ZIP solve-UNZIP solve-LPAD
make solve -j32
```

targeted 复验结果：

```text
LPAD     errors=0 panic=false
ZIP      errors=0 panic=false
UNZIP    errors=0 panic=false
VREV8_V  errors=0 panic=false
VSM3C_VI errors=0 panic=false
VSM3ME_VV errors=0 panic=false
CLMUL    errors=0 panic=false
```

### 全量复跑统计

数据来源：本次 `make solve -j32` 后的 `output/log/*.log`。

```text
log files: 258

LoopLimitReached:zpmpCheck              count=75 files=9
LoopLimitReached:zexecute               count=48 files=16
Symbolic length                         count=35 files=14
LoopLimitReached:zflush_TLB             count=8  files=2
LoopLimitReached:zinit_masked_source    count=4  files=2
```

本次全量复跑中已消失的问题：

- `panic`：`LPAD` 不再 panic。
- `AssertionFailure`：`ZIP` / `UNZIP` 不再触发 RV64 `assert(xlen == 32)`。
- `LoopLimitReached:zrev8`、`LoopLimitReached:zvrev8`：`rev8` / `vrev8` helper 替换后消失。
- `LoopLimitReached:zwrite_velem_oct_vec`：`write_velem_oct_vec` 条件展开后消失。
- `CLMUL`：仍保持 targeted 无执行错误。

### 剩余问题

- `zpmpCheck`：仍是访存类主问题，影响 `AMO`、`LOAD`、`LOADRES`、`STORE`、`STORECON`、`VMTYPE`、`ZICBOM`、`ZICBOP`、`ZICBOZ`。这类应单独处理 PMP 默认配置/默认放行路径，而不是继续在普通算术 helper 中修。
- `zexecute`：剩余 16 个日志，属于顶层执行循环上限，例如 `MOVETYPEI`、`VREV8_V`、`VSM3ME_VV` 等。已确认不再是 `zrev8` / `zvrev8` / `zwrite_velem_oct_vec` 这几个 helper。
- `Symbolic length`：剩余 14 个日志，主要位置包括：
  - `extensions/V/vext_utils_insts.sail:255` 的 `write_velem_quad` subrange；
  - `extensions/V/vext_utils_insts.sail:584` 的 segment register `vector_init(vector_init(zeros()))`；
  - `extensions/V/vext_arith_insts.sail:1509`、`:2100` 的 `vector_init(zeros())`；
  - `extensions/vector_crypto/zvknhab_insts.sail:130`、`:131` 的 SEW 相关 subrange。
- `zflush_TLB`：仍只影响 `SFENCE_VMA` / `SINVAL_VMA`。
- `zinit_masked_source`：仍影响 `RIVVTYPE` / `RMVVTYPE`。

---

## 总结

下表保留 6.16 原始基线和本轮分项处理状态；2026-06-18 最新全量复跑后的收敛结果以第 13 节为准。

| # | 函数/Primop | 错误类型 | 原始次数 | 原始影响日志数 | 本轮状态 |
|---|---|---|---:|---:|---|
| 1 | `zeros` | 符号化长度 | 273 | 68 | 已加 Isla 侧可证明长度具体化，并在高频 sail-riscv 向量路径改用 helper；待全量重跑确认归零情况 |
| 2 | `vector_init` | 符号化长度 | 100 | 21 | 已改 `read_vreg` / `write_vreg` 和部分 mask 路径；`MOVETYPEV`、`MASKTYPEX` targeted 复验通过 |
| 3 | `zpmpCheck` | 循环上限 | 66 | 8 | 本轮未处理 |
| 4 | `zinit_masked_result_cmp` | 循环上限 | 30 | 5 | helper 已改为 `isla_init_mask`，cmp 原始触发指令待全量或 targeted 补验 |
| 5 | `zcarryless_mul` | 循环上限 | 10 | 2 | 已加受保护的 `isla_clmul*` fast-path，CLMUL/CLMULH targeted 复验通过 |
| 6 | `zcount_ones` | 循环上限 | 8 | 2 | 已加受保护的 `isla_cpop*` fast-path，CPOP/CPOPW targeted 复验通过 |
| 7 | `zflush_TLB` | 循环上限 | 8 | 2 | 本轮未处理 |
| 8 | `sail_assert` | 断言失败 | 8 | 5 | ZIP/UNZIP 已改为 RV64 非法指令路径；向量访存断言未处理 |
| 9 | `zcarryless_mulr` | 循环上限 | 5 | 1 | 已加受保护的 `isla_clmulr` fast-path，CLMULR targeted 复验通过 |
| 10 | `zinit_masked_result_carry` | 循环上限 | 5 | 1 | helper 已改为 `isla_init_mask`，VIMTYPE 原 helper 循环消失但仍剩 `zexecute` |
| 11 | `subrange_internal` | 符号化长度 | 5 | 3 | XPERM4/XPERM8 已加受保护的 `isla_xperm*` fast-path，Isla 侧也加具体化；targeted 复验通过 |
| 12 | `extension` | 符号化长度 | 4 | 2 | 已加 `sign_extend_simm_to_sew` 和 Isla 侧目标宽度具体化；待全量确认 |
| 13 | `zread_vreg` | 循环上限 | 3 | 2 | `read_vreg` 已分派到 `isla_read_vreg`；VSRETYPE targeted 复验通过，VMTYPE 待确认 |
| 14 | `zreverse_bits` | 循环上限 | 2 | 1 | 已加受保护的 `isla_brev8` fast-path，BREV8 targeted 复验通过 |
| 15 | `zexecute` | 循环上限 | 1 | 1 | XPERM4 原问题已随 primop 消失；VIMTYPE 仍有新的主执行循环上限 |

### 核心结论

本轮已把 6.16 中最集中的两类问题拆开处理：高频隐式长度问题通过 sail-riscv helper 分派和 Isla 侧可证明长度具体化降低失败率；典型位操作循环通过专用 primop 避免 Sail foreach 展开。`ZIP` / `UNZIP` 的 RV64 断言失败也已转成显式非法指令路径。

仍未处理或未完全验证的部分主要是访存/系统路径和更大粒度执行循环：`zpmpCheck`、`zflush_TLB`、向量访存断言、原始 timeout 列表，以及 `VIMTYPE` targeted run 中剩余的 `zexecute`。下一轮建议先全量重跑 `make solve` 刷新统计，再按新的剩余 top errors 排序处理。

---

## 14. `$ifdef SYMBOLIC` 条件编译结构修正（2026-06-18）

根据后续审查意见，本次把 `../sail-riscv` 中新增的 Isla extra-op / helper 逻辑继续收紧到 `$ifdef SYMBOLIC` 分支内；未定义 `SYMBOLIC` 时，`$else` 分支直接保留上游原始 Sail 代码，不再通过 `_default` helper 间接调用。

调整范围：

- `model/extensions/V/vext_control.sail`
  - `write_vreg`、`read_vmask`、`read_vmask_carry` 的 `$else` 分支改为完整原始实现。
  - `write_vreg_default`、`read_vmask_inner`、`read_vmask_carry_inner` 和 extra-op 分派只保留在 `$ifdef SYMBOLIC` 内。
- `model/extensions/V/vext_arith_insts.sail`
  - `MASKTYPEV`、`MOVETYPEV`、`MASKTYPEX`、`MOVETYPEX`、`VITYPE`、`MASKTYPEI`、`MOVETYPEI` 改为 execute clause 级别条件编译。
  - `masktypev_result_default`、`vector_select_result_default`、`masktypei_result_default`、`execute_movetypex_default` 只在 `$ifdef SYMBOLIC` 内存在。
  - 非 `SYMBOLIC` 路径中的立即数扩展恢复为原始 `sign_extend(simm)`。
- `model/extensions/V/vext_vm_insts.sail`
  - `VIMTYPE`、`VIMCTYPE`、`VIMSTYPE`、`VICMPTYPE` 改为 execute clause 级别条件编译。
  - `$ifdef SYMBOLIC` 使用 `sign_extend_simm_to_sew`；`$else` 使用原始 `sign_extend(simm)`。

额外检查：

```text
未发现 _default / __isla_use_extra_ops / sign_extend_simm_to_sew 落在非 SYMBOLIC 或 $else 路径。
未发现函数体内部缩进的 $ifdef / $else / $endif。
```

构建验证：

```sh
PATH=/home/baiyifan/workplace-local/isla-runner/isla/isla-sail:$PATH cmake --build build --target generated_isla_rv64d
cmake --build build --target generated_smt_rv64d
```

结果：

```text
generated_isla_rv64d: 通过
generated_smt_rv64d: 通过
```

---

## 15. `$ifndef SYMBOLIC` 顺序重排（2026-06-18）

根据后续可读性要求，本次把 `../sail-riscv` 中已有的双分支条件编译块从：

```sail
$ifdef SYMBOLIC
  // Isla helper / extra-op path
$else
  // 原始实现
$endif
```

重排为：

```sail
$ifndef SYMBOLIC
  // 原始实现
$else
  // Isla helper / extra-op path
$endif
```

这样未定义 `SYMBOLIC` 时首先看到的是上游原始 Sail 代码，`$else` 中才是 Isla 专用 helper、extra-op 以及 `__isla_use_extra_ops` runtime 分派。

调整范围：

- `model/core/arithmetic.sail`
- `model/extensions/K/zbkb_insts.sail`
- `model/extensions/K/zbkx_insts.sail`
- `model/extensions/V/vext_utils_insts.sail`
- `model/extensions/V/vext_control.sail`
- `model/extensions/V/vext_arith_insts.sail`
- `model/extensions/V/vext_vm_insts.sail`

验证：

```text
generated_isla_rv64d: 通过
generated_smt_rv64d: 通过
diff --check: 通过
```

---

## 16. 默认 `make solve` 暂跳过内存相关 clause（2026-06-20）

根据后续测试和审查结论，当前内存符号化支持尚不完整；访存路径会同时经过地址计算、PMP/PMA/翻译检查、内存读写、reservation 或向量段访存循环，导致 `LOAD` / `STORE` / `AMO` / `VLSEGTYPE` / `VSSEGTYPE` 等 clause 的问题和普通算术/位运算 helper 混在一起，不利于本轮收敛。

因此本次只调整默认 solve 范围，不修改 Sail 指令语义：`scripts/run.mk` 新增 `MEMORY` 分组，并把 `ACTIVE_ALL` 改为同时排除 `FD_FLOAT` 和 `MEMORY`。

```make
MEMORY=AMO LOAD LOADRES STORE STORECON \
C_LBU C_LD C_LDSP C_LH C_LHU C_LW C_LWSP C_SB C_SD C_SDSP C_SH \
C_SW C_SWSP C_FLD C_FLDSP C_FLW C_FLWSP C_FSD C_FSDSP C_FSW C_FSWSP \
LOAD_FP STORE_FP VLRETYPE VLSEGFFTYPE VLSEGTYPE VLSSEGTYPE VLXSEGTYPE \
VMTYPE VSRETYPE VSSEGTYPE VSSSEGTYPE VSXSEGTYPE ZICBOM ZICBOP ZICBOZ \
FENCE FENCEI FENCE_TSO SFENCE_INVAL_IR SFENCE_VMA SFENCE_W_INVAL SINVAL_VMA

ACTIVE_ALL=$(filter-out $(FD_FLOAT) $(MEMORY),$(ALL))
```

同时新增单独入口：

```make
MEMORY_SOLVE_TARGETS=$(addprefix solve-,$(MEMORY))

solve-memory: $(MEMORY_SOLVE_TARGETS)
```

后续处理内存符号化时，应使用 `make solve-memory` 或单独的 `make solve-LOAD` / `make solve-VLSEGTYPE` 等目标集中验证；默认 `make solve` 先聚焦非内存类指令，避免已知内存路径规模问题污染当前统计。
