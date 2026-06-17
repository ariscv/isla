# Isla Bug 报错与修复报告

基于暂存区中 `isla-lib/src/primop.rs` 的改动，以及 `error_report.md` 中的错误统计，本文档梳理每个 bug 的报错信息、涉及的 clause name、isla 侧的修复方式、对应的 sail-riscv 函数语义、以及是否应在 sail-riscv 侧修复的分析。

> **核心发现：sail-riscv 的过度泛型设计**
>
> 大多数 bug 的根因是 **sail-riscv 中的函数使用了过于泛型的隐式参数（`implicit('n)`），超出了实际需要的范畴**。在 sail-riscv 运行时，这些隐式参数永远是具体常量（如 8, 16, 32, 64），但泛型签名导致 isla 符号执行时需要探索更大的参数空间，产生 `SymbolicLength` 等错误。
>
> 典型案例：[riscv/sail-riscv: pr#1559](https://github.com/riscv/sail-riscv/pull/1559) 将 sail-riscv 中使用 `int('n)` 隐式参数的 `shiftl`/`shiftr` 替换为 Sail 标准库的 `sail_shiftleft`/`sail_shiftright`，正是为了解决同样的问题。该 PR 的描述明确指出：
>
> > Helps with Isla symbolic execution, which doesn't support bitvectors of a symbolic size.
>
> 因此，**改进方向应在 sail-riscv 侧**：将使用隐式参数的函数调用点改为使用 Sail 标准库中接受具体整数的版本，或提供不使用隐式参数的特化版本。isla 侧的 solver 具体化只是 fallback 策略，不能替代 sail-riscv 侧的改进。

---

## 1. `zeros` / `ones` — 符号化长度参数

### Bug 报错
```
Symbolic (bit)vector length in zeros(SymbolicLength("zeros", ...))[prelude/prelude.sail 93:21 - 93:34]
```
影响日志数：89；出现次数：301（zeros）+ 隐含 ones。

### 触发指令（Clause Name）
运行以下指令时触发：**LOAD, MOVETYPEV, VAESDF, VAESDM, VAESEF, VAESEM, VAESKF1_VI, VAESKF2_VI, MASKTYPEI, MASKTYPEV, MASKTYPEX, MVVCOMPRESS, MVVMATYPE, MVVTYPE, MVXMATYPE, MVXTYPE** 等（共 89 个日志文件）。

主要触发路径：
- `sail_ones` 内部调用 `zeros`（vector.sail:396）→ 230 次
- `zeros` 直接调用（prelude.sail:93）→ 71 次

### Isla 侧处理
本轮不在 isla 中加入 solver 枚举具体化。`len` 为 `Val::Symbolic` 时仍保持原有 `SymbolicLength` 报错路径，避免把 sail-riscv 中过度泛型的隐式长度问题固化为 isla 后端的兜底逻辑。

### 对应 sail-riscv 函数
```sail
// prelude/prelude.sail:92-96
val zeros : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function zeros (n) = sail_zeros(n)

val ones : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function ones (n) = sail_ones(n)
```
**函数整体语义：** `zeros(n)` 和 `ones(n)` 是 Sail 预lude 中的基础位向量构造函数。`zeros` 返回长度为 `n` 的全 0 位向量，`ones` 返回长度为 `n` 的全 1 位向量。`n` 是类型级别的隐式参数（`implicit('n)`），由调用处的类型上下文推导确定，而非运行时传入。底层委托给 Sail 标准库的 `sail_zeros` / `sail_ones` 实现。

在 sail-riscv 中，这两个函数被广泛用于：
- 向量寄存器初始化（`read_vreg` 中 `vector_init(zeros())`）
- 掩码构造（`read_vmask` 中 `ones()` / `ones('n - num_elem)`）
- 运算结果初始化（`carryless_mul` 中 `var result = zeros()`）

### 是否改动 sail-riscv 更合理？
**是的。** 当前 `zeros`/`ones` 使用 `implicit('n)` 隐式参数，在 Sail 类型系统层面虽然保证了类型安全，但 `n` 在 sail-riscv 实际使用中永远是具体的常量值（8, 16, 32, 64 等）。这种过于泛型的写法导致 isla 符号执行时需要处理"符号化长度"的情况，探索更大的参数空间。

参考 [PR #1559](https://github.com/riscv/sail-riscv/pull/1559) 的思路：该 PR 将 sail-riscv 中自定义的 `shiftl`/`shiftr`（使用 `int('n)` 隐式参数）替换为 Sail 标准库的 `sail_shiftleft`/`sail_shiftright`（接受具体整数），从而避免 isla 符号执行时的符号化长度问题。

类似的改进方向：可以考虑在 sail-riscv 中将 `zeros`/`ones` 的调用点改为直接使用具体宽度的版本，或者在 sail-riscv 的 prelude 中提供不使用隐式参数的特化版本，减少 isla 需要探索的符号空间。

---

## 2. `extension`（sign_extend / zero_extend）— 符号化长度

### Bug 报错
```
Symbolic (bit)vector length in extension(SymbolicLength("extension", ...))[prelude/prelude.sail 89:29 - 89:51]
```
影响日志数：2；出现次数：4。

### 触发指令（Clause Name）
运行以下指令时触发：**MOVETYPEI, VIMCTYPE**（共 2 个日志文件）。

触发路径：`sign_extend`（prelude.sail:89）被向量指令中的立即数符号扩展调用。

### Isla 侧处理
本轮不在 isla 中加入针对 `Val::Symbolic` 目标长度的 solver 具体化。`sign_extend` / `zero_extend` 的符号化目标长度仍按原逻辑报 `SymbolicLength`，对应的泛型签名和调用点应优先在 sail-riscv 侧收窄。

### 对应 sail-riscv 函数
```sail
// prelude/prelude.sail:86-90
val sign_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function sign_extend(m, v) = sail_sign_extend(v, m)

val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function zero_extend(m, v) = sail_zero_extend(v, m)
```
**函数整体语义：** `sign_extend` 和 `zero_extend` 是 Sail 预lude 中的位向量宽度扩展函数。`sign_extend(m, v)` 将 `bits('n)` 符号扩展到 `bits('m)`（高位填充原最高位的副本），`zero_extend(m, v)` 将 `bits('n)` 零扩展到 `bits('m)`（高位填充 0）。目标长度 `m` 同样是隐式参数。类型约束 `'m >= 'n` 在编译期保证目标宽度不小于源宽度。底层分别委托给 `sail_sign_extend` / `sail_zero_extend`。

在 sail-riscv 中主要用于：
- 立即数符号扩展（`MOVETYPEI` 等指令中的立即数处理）
- 标量寄存器值的宽度适配（`get_scalar` 中 `sign_extend(SEW, X(rs1))`）
- 地址计算中的符号扩展

### 是否改动 sail-riscv 更合理？
**是的。** 与 `zeros`/`ones` 同理，`sign_extend`/`zero_extend` 的目标长度 `m` 是隐式参数，在 sail-riscv 实际使用中永远是具体常量（如从 8 扩展到 32，从 32 扩展到 64 等）。过于泛型的签名导致 isla 符号执行时需要探索符号化的目标长度空间。

改进方向：可以参考 PR #1559 的思路，在 sail-riscv 中将 `sign_extend`/`zero_extend` 的调用点改为使用 Sail 标准库中接受具体整数的版本，或者提供不使用隐式参数的特化版本。

---

## 3. `slice_internal` — 符号化长度

### Bug 报错
```
Symbolic (bit)vector length in slice_internal(SymbolicLength("slice_internal", ...))[prelude/prelude.sail 101:23 - 101:37]
```
影响日志数：1；出现次数：2。

### 触发指令（Clause Name）
运行 **AMO** 指令时触发（1 个日志文件）。

触发路径：`trunc`（prelude.sail:101）在原子操作中被调用。

### Isla 侧处理
本轮不在 `slice_internal` 中加入符号化长度具体化或 Poison 特判。`trunc` 的隐式目标长度属于 sail-riscv 泛型调用边界问题，应优先在 sail-riscv 中改为更具体的调用形式。

### 对应 sail-riscv 函数
```sail
// prelude/prelude.sail:100-101
val trunc : forall 'm 'n, 'm >= 0 & 'm <= 'n. (implicit('m), bits('n)) -> bits('m)
function trunc(m, v) = truncate(v, m)
```
**函数整体语义：** `trunc(m, v)` 是 Sail 预lude 中的位向量截断函数，将 `bits('n)` 截断为 `bits('m)`，保留最低 `m` 位、丢弃高位。隐式参数 `m` 为目标长度。类型约束 `'m <= 'n` 在编译期保证截断目标不大于源。底层委托给 `sail_truncate`。

在 sail-riscv 中用于：
- 原子操作中地址对齐截断（AMO 指令）
- 任何需要从宽位向量提取窄结果的场景

### 是否改动 sail-riscv 更合理？
**是的。** `trunc` 的隐式参数 `m`（目标长度）在 sail-riscv 实际使用中永远是具体常量。过于泛型的签名导致 isla 符号执行时需要探索符号化的目标长度空间。

改进方向：与 `zeros`/`ones`/`sign_extend` 类似，可以考虑在 sail-riscv 中使用 Sail 标准库的 `sail_truncate` 直接接受具体整数版本，或提供特化版本。

---

## 4. `subrange_internal` — 符号化索引 + Poison 传播

### Bug 报错
```
Symbolic (bit)vector length in subrange_internal(SymbolicLength("subrange_internal", ...))[extensions/V/vext_utils_insts.sail:227 ...]
```
影响日志数：7（符号化长度）+ 6（类型错误）；出现次数：80（含类型错误 62 次）。

### 触发指令（Clause Name）
运行以下指令时触发：
- **符号化长度**（18 次）：MOVETYPEX, VMVSX, VXMCTYPE, VMTYPE, STORE, STORECON, XPERM4, XPERM8
- **Poison 类型错误**（62 次）：MMTYPE, VCPOP_M, VMSBF_M, VMSIF_M, VMSOF_M

主要触发路径：
- `read_vmask`（vext_control.sail:151）→ MMTYPE 等掩码操作 → 45 次
- `read_single_element`（vext_control.sail:61）→ VMTYPE → 17 次
- `get_scalar`（vext_utils_insts.sail:227）→ MOVETYPEX, VMVSX, VXMCTYPE → 10 次
- `execute`（base_insts.sail:322）→ STORE → 2 次
- `execute`（zalrsc_insts.sail:70）→ STORECON → 2 次
- `execute`（zbkx_insts.sail:54/29）→ XPERM4, XPERM8 → 4 次

### Isla 侧处理
本轮不在 `subrange_internal` 中加入 high/low 的 solver 具体化，也不把 `Val::Poison` 作为通用子范围操作的成功返回值。符号化索引仍按原逻辑报 `SymbolicLength`，Poison 输入仍暴露为类型错误，以便将调用点问题继续定位到 sail-riscv 的向量掩码/泛型边界。

### 对应 sail-riscv 函数
`subrange_internal` 是 Sail 编译器为位向量子范围访问 `v[high .. low]` 生成的内部函数，无显式 Sail 定义。在 sail-riscv 中广泛使用，例如：
- `V(vrid)[num_elem - 1 .. 0]`（vext_control.sail:151）
- `X(rs1)[SEW - 1 .. 0]`（vext_utils_insts.sail:227）

**函数整体语义：** `subrange_internal` 是 Sail 编译器为位向量子范围访问语法 `v[high .. low]` 自动生成的内部函数，无显式 Sail 源码定义。其语义是从位向量 `v` 中提取第 `high` 位到第 `low` 位（含两端）的子范围，返回长度为 `high - low + 1` 的新位向量。

在 sail-riscv 中大量使用，典型场景包括：
- 向量寄存器元素访问：`V(vrid)[num_elem - 1 .. 0]`（读取向量掩码）
- 标量寄存器低位提取：`X(rs1)[SEW - 1 .. 0]`（获取标量操作数）
- 指令字段解码：`instr[31 .. 20]` 等
- 存储操作的数据截取：`base_insts.sail` 中的 store 指令

### 是否改动 sail-riscv 更合理？
**部分是。** `subrange_internal` 本身是 Sail 编译器为 `v[high .. low]` 语法生成的内置操作，无法直接修改。但 sail-riscv 中的某些调用点（如 `read_vmask` 中的 `V(vrid)[num_elem - 1 .. 0]`）的 `num_elem` 参数是隐式参数，在实际使用中永远是具体常量。如果 sail-riscv 将这些调用点改为使用具体常量（而非依赖隐式参数推导），isla 符号执行时就不需要探索符号化的索引空间。

不过，`subrange_internal` 的符号化索引问题更多源于 isla 符号执行将具体值抽象为符号，与 `zeros`/`ones` 的隐式参数问题略有不同。

---

## 5. `i64_to_i128` — Bits 类型转换缺失

### Bug 报错
```
Type("%i64->%i Bits(B129 { tag: false, bits: 0, len: 64 })", ...)
```
影响日志数：7；出现次数：11。

### 触发指令（Clause Name）
运行以下指令时触发：**LOADRES, VLSEGFFTYPE, VLSEGTYPE, VLSSEGTYPE, VMVRTYPE, VSSEGTYPE, VSSSEGTYPE, VSRETYPE, VLRETYPE**（共 7+ 个日志文件）。

主要涉及 V 扩展的段加载/存储指令（vlseg, vsseg 等）和保留加载（lr.w/lr.d）。

### Isla 侧修复
增加对 `Val::Bits(x)` 当 `x.len() == 64` 时的处理分支：将 64 位位向量有符号解释后转为 `Val::I128`。

```rust
Val::Bits(x) if x.len() == 64 => Ok(Val::I128(x.signed())),
```

### 对应 sail-riscv 函数
**函数整体语义：** `i64_to_i128` 是 isla 内部的类型转换原语，对应 Sail 语言中隐式的整数宽度提升。Sail 允许在表达式中混合使用不同宽度的整数（如 `i64` 和 `i128`），编译器会自动插入宽度转换。在 sail-riscv 中无显式定义，由 Sail 编译器在需要时自动生成调用。

在 sail-riscv 中触发场景包括：
- V 扩展段加载/存储指令（vlseg/vsseg 等）中的地址和长度计算
- 保留加载指令（lr.w/lr.d）中的地址宽度转换
- 涉及大整数中间计算的任何指令

### 是否改动 sail-riscv 更合理？
**不需要。** 这是 isla 对 Sail 类型转换的实现不完整导致的。Sail 的类型系统允许隐式整数提升，isla 应当处理所有合法的值表示形式。

---

## 6. `sys_enable_experimental_extensions` — 缺失函数

### Bug 报错
```
NoFunction("sys_enable_experimental_extensions", SourceLoc { file: 28, line1: 75, char1: 41, line2: 75, char2: 77 })
```
影响日志数：2；出现次数：12。

### 触发指令（Clause Name）
运行以下指令时触发：**BITYPE, VABS_V**（共 2 个日志文件，12 次错误）。

这些指令在 sail-riscv 中有 `sys_enable_experimental_extensions()` 守卫，用于检查是否启用实验性扩展。

### Isla 侧修复
在 primop 注册表中添加该函数，返回 `Val::Bool(false)`（表示不启用实验性扩展）：

```rust
fn experimental_extensions<B: BV>(_: Val<B>, _: &mut Solver<B>, _: SourceLoc) -> Result<Val<B>, ExecError> {
    Ok(Val::Bool(false))
}
// 注册：
primops.insert("sys_enable_experimental_extensions".to_string(), experimental_extensions as Unary<B>);
```

### 对应 sail-riscv 函数
```sail
// 在多个平台后端中定义，统一返回 false
// handwritten_support/riscv_extras.v:28
Definition sys_enable_experimental_extensions (_:unit) : bool := false.

// handwritten_support/riscv_extras.lem:39
def sys_enable_experimental_extensions () = false

// c_emulator/riscv_platform_if.cpp:134
bool PlatformInterface::sys_enable_experimental_extensions(unit) { return false; }
```
**函数整体语义：** `sys_enable_experimental_extensions` 是 sail-riscv 的平台接口函数，用于查询当前平台是否启用实验性 RISC-V 扩展。在 RISC-V 规范中，某些扩展（如 Bitmanip 的某些子扩展）在标准化之前处于"实验性"状态，需要通过此函数守卫。所有已实现的后端（Coq、LEM、Lean、C emulator）均硬编码返回 `false`，即不启用实验性扩展。

在 sail-riscv 中的使用模式：
```sail
if sys_enable_experimental_extensions() then {
  // 实验性扩展的指令实现
} else {
  // 抛出非法指令异常
}
```
被此守卫保护的指令包括 `BITYPE`（Bitmanip 某些变体）和 `VABS_V`（向量绝对值）等。

### 是否改动 sail-riscv 更合理？
**不需要。** 这是 isla 缺少对 sail-riscv 平台接口函数的实现。sail-riscv 侧的定义完全正确且一致（全返回 false），isla 作为新的执行后端需要补上对应的 primop。

---

## 7. `carryless_mul` — panic 导致的循环上限

### Bug 报错
```
Executed loop in 2853 at 27 more than specified limit(LoopLimitReached(Name("zcarryless_mul"), 27))[0:0 - 0:0]
```
影响日志数：2；出现次数：10（carryless_mul）+ 5（carryless_mulr）。

### 触发指令（Clause Name）
运行以下指令时触发：**CLMUL, CLMULH**（carryless_mul，10 次）, **CLMULR**（carryless_mulr，5 次）。

这些是 RISC-V Zbc（无进位乘法）扩展的指令。

### Isla 侧修复
**移除了 `carryless_mul` 函数开头的 `panic!("arrive carryless_mul!!")` 调试语句。** 此 panic 会导致执行直接崩溃（而非正常的循环上限错误），移除后让函数走入正常的符号执行路径。

注意：循环上限问题本身（`LoopLimitReached`）并未在此改动中解决，仅修复了 panic 导致的崩溃。

### 对应 sail-riscv 函数
```sail
// model/core/arithmetic.sail:20-27
val carryless_mul : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits(2 * 'n)
function carryless_mul(a, b) = {
  var result : bits(2 * 'n) = zeros();
  foreach (i from 0 to ('n - 1)) {
    if a[i] == 0b1 then result = result ^ (zero_extend(b) << i);
  };
  result
}
```
**函数整体语义：** `carryless_mul(a, b)` 实现 GF(2) 上的无进位乘法（即多项式乘法，不带进位的逐位与然后异或）。输入两个 `bits('n)`，输出 `bits(2*'n)`。实现方式是逐位检查 `a` 的每一位，若为 1 则将 `b` 左移对应位数后异或累加到结果中。循环次数等于操作数位宽 `'n`。

`carryless_mulr(a, b)` 是反向版本，输出仍为 `bits('n)`，取 carryless_mul 结果的低 `'n` 位（通过右移而非左移实现）。

这两个函数对应 RISC-V Zbc（无进位乘法）扩展的三条指令：
- **CLMUL**：调用 `carryless_mul`，取低 `'n` 位结果
- **CLMULH**：调用 `carryless_mul`，取高 `'n` 位结果
- **CLMULR**：调用 `carryless_mulr`

这些指令常用于密码学中的 CRC 计算和 GCM 等认证加密算法。

### 是否改动 sail-riscv 更合理？
**部分是。** `panic` 明显是 isla 侧遗留的调试代码，移除它是正确修复。但循环上限问题是 isla 的设计限制（loop limit），sail-riscv 的 foreach 循环实现本身语义正确。若要根本解决循环上限问题，可考虑在 isla 中为 carryless_mul 添加专用 primop（直接用 SMT 表达式实现），而非依赖符号执行遍历循环。

---

## 8. `read_vmask` 中的 `subrange_internal` 类型错误

### Bug 报错
```
Type error: subrange_internal Poison I128(255) I128(0)
```
影响日志数：6；出现次数：62（来自 MMTYPE.log 等向量掩码操作）。

### 触发指令（Clause Name）
运行以下向量指令时触发：**MMTYPE, VCPOP_M, VMSBF_M, VMSIF_M, VMSOF_M**（共 6 个日志文件，45 次来自 `read_vmask`）。

这些都是 V 扩展的掩码操作指令，执行时需要读取向量掩码寄存器。

### Isla 侧处理
本轮不通过 `subrange_internal` 的 Poison 传播掩盖该问题。`read_vmask` 的输入来源和隐式参数边界应在 sail-riscv 侧继续收窄或重写；isla 侧保留原错误有助于暴露未初始化/Poison 值的真实传播路径。

### 对应 sail-riscv 函数
```sail
// model/extensions/V/vext_control.sail:149-151
val read_vmask : forall 'n, 0 < 'n <= vlen . (int('n), bits(1), vregidx) -> bits('n)
function read_vmask(num_elem, vm, vrid) =
  if vm == 0b1 then ones() else ones('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]
```
**函数整体语义：** `read_vmask(num_elem, vm, vrid)` 是 RISC-V V 扩展中读取向量掩码的核心函数。参数含义：
- `num_elem`：当前向量操作的元素个数（受 VLMAX 和 vlen/SEW 约束）
- `vm`：掩码模式位（1 表示无掩码，0 表示使用掩码）
- `vrid`：掩码寄存器索引（通常为 v0）

逻辑：
- 当 `vm=0b1`（无掩码模式）时，返回全 1 位向量（所有元素启用）
- 当 `vm=0b0`（掩码模式）时，返回 `ones('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]`，即高位填充 1（超出 VL 的元素视为启用），低位取掩码寄存器 v0 的对应位

类似函数 `read_vmask_carry` 语义相反：`vm=1` 返回全 0（无进位），`vm=0` 返回零填充 + 寄存器值。

在 sail-riscv 中被所有带掩码的向量指令调用（MMTYPE, VCPOP_M, VMSBF_M, VMSIF_M, VMSOF_M 等）。

### 是否改动 sail-riscv 更合理？
**部分是。** `read_vmask` 的 `num_elem` 参数来自类型级别的隐式参数 `'n`，在 sail-riscv 实际使用中永远是具体常量（由 VLMAX 和 vlen/SEW 确定）。如果 sail-riscv 将 `read_vmask` 改为接受具体整数参数（而非依赖隐式类型参数），isla 符号执行时就不需要探索符号化的 `num_elem` 空间，从而避免 `subrange_internal` 的符号化索引问题。

不过，Poison 值本身是 isla 符号执行的特殊概念，与 sail-riscv 的泛型设计无关。

---

## 9. `get_scalar` 中的 `subrange_internal` 符号化长度

### Bug 报错
```
Symbolic (bit)vector length in subrange_internal(SymbolicLength("subrange_internal", ...))[extensions/V/vext_utils_insts.sail:227 ...]
```
影响日志数：3；出现次数：10。

### 触发指令（Clause Name）
运行以下指令时触发：**MOVETYPEX, VMVSX, VXMCTYPE**（共 3 个日志文件）。

这些指令在执行时调用 `get_scalar` 从标量寄存器读取值，其中的 `X(rs1)[SEW - 1 .. 0]` 子范围操作触发了符号化长度错误。

### Isla 侧处理
本轮不通过 `concretize_length_i128` 具体化 SEW。`get_scalar` 的 SEW 是运行时值，isla 不应把它混入通用长度 solver 枚举 fallback。

### sail-riscv 侧处理
在 sail-riscv 中将 `get_scalar` 的类型约束收窄为 `is_sew_bitsize('m)`，并按 `SEW` 的合法常量值分支到固定子范围。这样保留了运行时选择 SEW 的语义，但每个实际子范围操作都落在具体索引上，避免 `X(rs1)[SEW - 1 .. 0]` 直接产生符号化 high/low。

### 对应 sail-riscv 函数
```sail
// model/extensions/V/vext_utils_insts.sail:223-232
val get_scalar : forall 'm, is_sew_bitsize('m). (regidx, int('m)) -> bits('m)
function get_scalar(rs1, SEW) = {
  match SEW {
    8  => X(rs1)[7 .. 0],
    16 => X(rs1)[15 .. 0],
    32 => X(rs1)[31 .. 0],
    64 => {
      if 64 <= xlen then X(rs1)[63 .. 0] else sign_extend(64, X(rs1))
    },
  }
}
```
**函数整体语义：** `get_scalar(rs1, SEW)` 是 RISC-V V 扩展中从标量寄存器获取操作数的函数。参数含义：
- `rs1`：标量寄存器索引（x0-x31）
- `SEW`：Standard Element Width，标准元素宽度（8, 16, 32, 64 位）

逻辑：
- 当 `SEW` 为 8/16/32 时，分别取 `X(rs1)` 的低 8/16/32 位。
- 当 `SEW` 为 64 时，如果 `xlen >= 64` 则取低 64 位，否则将 `X(rs1)` 符号扩展到 64 位。

在 sail-riscv 中被标量-向量操作指令调用（MOVETYPEX, VMVSX, VXMCTYPE），用于将标量寄存器的值适配到向量元素宽度后作为向量运算的操作数。

### 是否改动 sail-riscv 更合理？
**部分是。** `get_scalar` 的 `SEW` 参数确实由 CSR（如 `vtype` 寄存器）动态确定，不等同于 `zeros`/`ones` 的隐式参数问题。但 RISC-V V 扩展的合法 SEW 取值集合固定为 8/16/32/64，因此在 sail-riscv 侧按合法常量分支，比在 isla 中增加通用 solver 枚举更贴近模型语义，也更容易定位后续真正的运行时符号值问题。

---

## 总结

| # | 函数/Primop | 错误类型 | 触发指令（Clause Name） | 本轮处理 | 改 sail-riscv？ |
|---|---|---|---|---|---|
| 1 | `zeros`/`ones` | 符号化长度 | LOAD, MOVETYPEV, VAESDF/DM/EF/EM, VAESKF1/2_VI, MASKTYPEI/V/X, MVVCOMPRESS, MVVMATYPE, MVVTYPE, MVXMATYPE, MVXTYPE | 不在 isla 中具体化，保留 `SymbolicLength` | **是** — 隐式参数过于泛型 |
| 2 | `extension` | 符号化长度 | MOVETYPEI, VIMCTYPE | 不在 isla 中具体化，保留 `SymbolicLength` | **是** — 隐式参数过于泛型 |
| 3 | `slice_internal` | 符号化长度 | AMO | 不在 isla 中具体化 | **是** — 隐式参数过于泛型 |
| 4 | `subrange_internal` | 符号化索引 + Poison | MMTYPE, VCPOP_M, VMSBF/IF/OF_M, MOVETYPEX, VMVSX, VXMCTYPE, VMTYPE, STORE, STORECON, XPERM4/8 | 不在 isla 中具体化/吞 Poison | **部分** — 调用点的隐式参数过于泛型 |
| 5 | `i64_to_i128` | 类型转换缺失 | LOADRES, VLSEGFFTYPE, VLSEGTYPE, VLSSEGTYPE, VMVRTYPE, VSSEGTYPE, VSSSEGTYPE, VSRETYPE, VLRETYPE | 增加 `Val::Bits` 分支 | 否 — isla 内部问题 |
| 6 | `sys_enable_experimental_extensions` | 缺失函数 | BITYPE, VABS_V | 添加 primop，返回 false | 否 — isla 缺少实现 |
| 7 | `carryless_mul` | panic 崩溃 | CLMUL, CLMULH, CLMULR | 移除调试 panic | **部分** — 循环上限需专用 primop |
| 8 | `read_vmask` | Poison 类型错误 | MMTYPE, VCPOP_M, VMSBF/IF/OF_M | 不在 isla 中吞 Poison；通过向量寄存器默认值和 `read_vreg` 具体零初始化暴露剩余 loop-limit 问题 | **部分** — 隐式参数过于泛型 |
| 9 | `get_scalar` | 符号化长度 | MOVETYPEX, VMVSX, VXMCTYPE | 不在 isla 中具体化；在 sail-riscv 中按合法 SEW 常量分支 | **部分** — SEW 是运行时值，但合法取值集合固定 |

### 本轮落地修正

**isla 侧：**
- 撤回 `zeros`/`ones`/`extension`/`slice_internal`/`subrange_internal` 中的通用 solver 长度枚举 fallback，保留原有 `SymbolicLength` 暴露路径。
- 保留真正属于 isla 的修复：`i64_to_i128` 支持 64 位 `Val::Bits`，`sys_enable_experimental_extensions` 返回 `false`，以及超出 `B::MAX_WIDTH` 的位向量字面量通过 `MixedBits` 表示并能转成 SMT。
- 在 RISC-V 配置中加入向量寄存器 relaxed/default，使 256 位向量寄存器默认值可以被解析和求值。

**sail-riscv 侧：**
- `vmem_read_addr` 将 `data` 明确为 `bits(8 * 'width)`，避免 `zeros(8 * n * bytes)` 的隐式长度进入符号执行。
- `LOAD`、`LOADRES`、`AMO` 按合法访问宽度分派到具体宽度调用点。
- `get_scalar` 收窄到 `is_sew_bitsize` 并按 8/16/32/64 常量 slice。
- `read_vreg` 用 `zero_sew_bits(SEW)` 初始化，避免 `vector_init(zeros())` 继续依赖符号化隐式长度。
- `MOVETYPEX` 按 `SEW` 和有效 `LMUL_pow` 分派到具体 `num_elem`，避免 `read_vreg` 的向量长度继续符号化。

**验证结果：**
- `sail model/riscv.sail_project --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.1 --memo-z3-path /tmp/sail-riscv-smt-cache --all-modules --just-check` 通过，仅有既有 warning。
- 已重新生成 `../sail-riscv/build/model/rv64d.ir` 并同步到当前目录 `rv64d.ir`。
- `cargo fmt` 和 `cargo check -p isla-lib` 通过，仅有既有 warning。
- `solve-MOVETYPEX` 不再出现 `Symbolic (bit)vector length`/Poison/执行错误；`solve-MMTYPE` 剩余 `zinit_masked_result_carry` 的 loop limit。
- `solve-LOAD`/`solve-LOADRES`/`solve-AMO` 未再出现本轮关注的符号长度或类型错误；残留主要是 `zpmpCheck` loop limit，以及部分 Ctor 返回 Poison 的既有警告。

### 核心结论

**双重根因：** 大多数 bug 的产生有两个层面的原因：

1. **sail-riscv 的过度泛型设计（主因）：** sail-riscv 中的函数（如 `zeros`/`ones`/`sign_extend`/`zero_extend`/`trunc`/`read_vmask`）大量使用 `implicit('n)` 隐式参数，将函数写得过于通用，超出了 sail-riscv 实际需要的范畴。在 sail-riscv 运行时，这些隐式参数永远是具体常量（如 8, 16, 32, 64），但泛型签名导致 isla 符号执行时需要探索更大的参数空间，产生 `SymbolicLength` 错误。

   参考 [PR #1559](https://github.com/riscv/sail-riscv/pull/1559)：该 PR 将 sail-riscv 中使用 `int('n)` 隐式参数的 `shiftl`/`shiftr` 替换为 Sail 标准库的 `sail_shiftleft`/`sail_shiftright`，正是为了解决同样的问题。

   **改进方向：** 在 sail-riscv 中将使用隐式参数的函数调用点改为使用 Sail 标准库中接受具体整数的版本，或提供不使用隐式参数的特化版本。

2. **isla 符号执行引擎的不完善（次因）：** 即使 sail-riscv 的设计更具体，isla 仍然需要处理符号执行过程中产生的符号值（如将具体运行时值抽象为符号）。这类 fallback 应在独立设计后再加入；本轮不引入通用 solver 枚举具体化，避免掩盖应由 sail-riscv 修正的泛型边界。

**其他问题：**
- `sys_enable_experimental_extensions` 是 isla 缺少对 sail-riscv 平台接口的实现，纯属 isla 侧遗漏
- `i64_to_i128` 是 isla 对 Sail 类型转换的实现不完整
- `carryless_mul` 的循环上限问题是 sail 的 foreach 循环在符号执行下的固有效率问题，长期方案应考虑在 isla 中添加专用 primop
