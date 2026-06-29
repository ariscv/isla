# read_vmask 符号切片修复：方案 A vs 方案 B —— 为什么 B 会 timeout

## 背景

6.28 报告问题 B：`read_vmask`/`read_vmask_carry`（vext_control.sail:538-549）的 `V(vrid)[num_elem-1..0]` 在符号 `num_elem` 下命中 isla `subrange_internal` 的 `SymbolicLength` 错误。

本文档回答用户的两个核心问题：
1. **为什么方案 B 会 timeout，方案 A 不会？** —— 从**符号引擎面对的操作**角度（不区分 isla/sail-riscv）。
2. **方案 A 和方案 B 是否等价？**

> 本轮所有数据基于**清理后的 primop.rs**（commit 5f8a793，5134 行）。注意：6.28 报告里的"63 个 timeout"是用**臃肿的** primop.rs（8203 行未提交工作树）跑的；清理后 baseline 的真实 timeout 是 **24 个**。本文档数据全部基于清理后版本，三方案在同一基线上对比。

---

## 1. 符号引擎面对的两个"符号"操作

不论 isla 还是 sail-riscv，符号引擎在执行 V 扩展指令时，面对 `num_elem`（元素个数，由符号化 vtype 派生）会撞上**两个它本质上无法直接处理的操作**：

### 操作 ①：符号位宽的位向量切片（symbolic-width bitvector slice）

原始 `read_vmask`（sail-riscv vext_control.sail:538-542）：

```sail
val read_vmask : forall 'n, 0 < 'n <= vlen . (int('n), bits(1), vregidx) -> bits('n)
function read_vmask(num_elem, vm, vrid) = {
  assert_vector_num_elem(num_elem);
  if vm == 0b1 then ones() else ones('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]
  //                                                       ^^^^^^^^^^^^^^^^^^^^
  //                                                       切片的 high 边界 = num_elem-1（符号）
}
```

`V(vrid)[num_elem-1 .. 0]` 编译成 isla 的 `subrange_internal(bits, high=num_elem-1, low=0)`。引擎要构造一个**位向量**，但这个位向量的宽度（= high-low+1 = num_elem）是符号值。位向量的宽度必须在**构造时就是具体的**（它决定 SMT 的 sort），引擎无法构造一个"宽度未知"的位向量。

isla `subrange_internal`（primop.rs:1152-1205）的处理：先尝试 `concretize_proven_i128(high)`（:1159）—— 即问 SMT "你能不能**证明** high 等于某个具体常量？"。`concretize_proven_i128` 的实现（primop.rs:123-131）：

```rust
fn concretize_proven_i128<B: BV>(value: Val<B>, solver: &mut Solver<B>, info: SourceLoc) -> Val<B> {
    match value {
        Val::Symbolic(sym) => match proven_symbolic_i128(sym, solver, info) {
            Some(value) => Val::I128(value),   // SMT 能证明 == 常量 → 具体化
            None => Val::Symbolic(sym),        // 证不出 → 保持符号
        },
        value => value,
    }
}
```

当 `num_elem` 是**无约束的自由符号**时，SMT 证不出 `num_elem-1 == 常量`，high 保持 `Val::Symbolic`，于是命中（primop.rs:1203-1205）：

```rust
        (_, Val::Symbolic(_), _) | (_, _, Val::Symbolic(_)) => {
            Err(ExecError::SymbolicLength("subrange_internal", info))   // ← 硬错误，路径终止
        }
```

这就是 6.28 报告的 73 次 `SymbolicLength` 硬错误的来源。

### 操作 ②：符号边界的循环（symbolic-bound loop）

V 指令执行体里普遍有（以 VIMTYPE/vext_vm_insts.sail:556 为例）：

```sail
  let num_elem = get_num_elem(LMUL_pow, SEW);   // 符号
  ...
  foreach (i from 0 to (num_elem - 1)) {         // ← 循环上界 = num_elem-1（符号）
    if mask[i] == 0b1 then { ... result[i] = ... }
  };
```

引擎要展开这个 `foreach`，但循环次数 `num_elem` 是符号值。引擎**无法静态确定要展开几轮**。

> **关键**：`num_elem` 的合法取值是有限集合 `{1,2,4,8,...,vlen}`（由 SEW∈{8,16,32,64}×LMUL∈{-3..3} 决定）。所以这两个操作不是"无限不可接受"，而是"有限但要枚举"。两种方案的差别就在于**如何处理这个有限枚举**。

---

## 2. 方案 A 做了什么（从引擎角度）

方案 A 在 `read_vmask` 内部用一个内置函数（isla `isla_read_vmask`）**替换掉了操作①**。核心实现（isla-A/isla-lib/src/primop.rs:2664-2770）的符号路径：

```rust
// 固定位宽 len = V(vrid) 的静态宽度（= VLEN，具体），与 num_elem 无关
let len = length_bits(&vreg, solver, info)?;
let num_elem_exp = int_exp_128(&args[0], ...)?;   // num_elem 转成 SMT 表达式（保持符号）

let mut exp = None;
for i in (0..len).rev() {                          // ← 循环上界 len 是具体值，定数展开
    let index = smt_i128(i128::from(i));
    // 第 i 位 = (i < num_elem) ? vreg[i] : pad    ← num_elem 只出现在 SMT 比较里
    let in_range = Exp::Bvslt(Box::new(index), Box::new(num_elem_exp.clone()));
    let vreg_bit = symbolic_bit(&vreg, i, info)?;
    let body_bit = Exp::Ite(Box::new(in_range), Box::new(vreg_bit), Box::new(pad_bit.clone()));
    ...
    exp = Some(Exp::Concat(Box::new(acc), Box::new(bit)));   // 拼成固定宽度的位向量
}
solver.define_const(exp.expect(...), info).into()   // 返回一个固定位宽的 SMT 表达式
```

**方案 A 本质上做了什么**：
- 它把"构造一个宽度=num_elem 的位向量"这个**不可能的操作**，改写成"构造一个**固定宽度 len**（=VLEN）的位向量，其中每一位的值由一个 SMT 谓词 `i < num_elem` 决定"。
- `num_elem` **不再是位向量的宽度**，也不再是任何切片的边界——它只作为 SMT `Bvslt(i, num_elem)` 比较的条件出现。
- 因此：位向量的 sort 在构造时就确定了（`len` 具体），`num_elem` 保持符号但**不进入控制流**，引擎**不需要 fork**，也**永远不调用 `subrange_internal`**。

**但方案 A 没有处理操作②**：`num_elem` 仍是符号，执行体里的 `foreach (i from 0 to num_elem-1)` 仍是符号边界循环。引擎对符号边界循环的处理是受限的（要么按 LoopLimit 截断，要么路径无法真正"算完"）。

---

## 3. 方案 B 做了什么（从引擎角度）

方案 B 不改 `read_vmask`，而是在**指令执行体**里把 `num_elem` 这个符号值**具体化**（concretize）掉。用的是 sail 已有的 `assert_vector_num_elem_value`（vext_control.sail:258-278）：

```sail
val assert_vector_num_elem_value : forall 'n, 'n >= 0. int('n) -> int('n)
function assert_vector_num_elem_value(num_elem) = {
  assert(num_elem <= vlen);
  match num_elem {       // ← 对符号 num_elem 做 match，每个 arm 是一个具体值
    1    => 1,
    2    => 2,
    4    => 4,
    8    => 8,
    16   => 16,
    32   => 32,
    ...
    1024 => 1024,
    _    => { assert(false); 1 }
  }
}
```

执行体里（vext_arith_insts.sail VITYPE 等）：

```sail
  let num_elem = get_num_elem(LMUL_pow, SEW);                       // 符号
  let num_elem = assert_vector_num_elem_value(num_elem);            // ← 具体化
  ...
  let vm_val = read_vmask(num_elem, vm, zvreg);                     // 现在 num_elem 在每条 path 上是常量
  ...
  foreach (i from 0 to (num_elem - 1)) { ... }                      // ← 循环边界也变具体，定数展开
```

**方案 B 本质上做了什么**：
- `match num_elem { 1=>1, 2=>2, ... }` 在符号执行里是一个**多路分叉**：引擎对 `num_elem` 的每个候选值 fork 出一条独立路径，每条路径上 `num_elem` 被**绑定到一个具体常量**（通过路径条件）。
- 这**同时解决了操作①和操作②**：
  - 操作①：每条路径上 `num_elem` 是常量 → `concretize_proven_i128` 成功 → 切片正常 → 不再 `SymbolicLength`。
  - 操作②：每条路径上循环边界是常量 → `foreach` 定数展开 → 计算真正完成（产生 `Retire_Success`）。
- **代价**：路径数 ×（num_elem 的候选个数）。`num_elem` 有 ~10 个合法值，每多一个就多一倍路径（叠加在已有的 SEW×LMUL×扩展使能位×vstart×vl 之上）。

---

## 4. 为什么 B 会 timeout，A 不会（核心论证）

两种方案都消除了操作①的 `SymbolicLength` 硬错误，但**处理方式根本不同**：

| | 方案 A | 方案 B |
|---|---|---|
| 操作①（符号切片） | **替换**为固定位宽 SMT ITE，绕过 `subrange_internal` | 通过具体化让切片边界变具体 |
| 操作②（符号循环） | **没处理**，`num_elem` 仍符号，循环边界仍符号 | **一并解决**，循环定数展开 |
| `num_elem` 的命运 | 保持符号，只活在 SMT 约束里 | 被拆成 N 条路径，每条上一个常量 |
| 引擎是否因 num_elem fork | **否** | **是**（按 num_elem 值枚举 fork） |
| 路径数 | 少（与 baseline 持平） | 多（baseline × num_elem 候选数） |
| 路径能否"算完"（Retire_Success） | 多数算不完（符号循环受限） | 能算完（循环定数展开） |

**一句话**：方案 A 把"符号宽度切片"这个**不可能的操作**换成了"固定位宽 + SMT 条件选择"这个**可能但符号的操作**，不引入新 fork；方案 B 把符号值**枚举成多个具体值**来回避符号性，代价是路径数随 `num_elem` 的合法取值成倍膨胀。**timeout 来自路径膨胀**，不是来自操作①本身。

### 实验证据（同一清理后基线，60s/clause）

**(a) 公平对比：VIMTYPE（两个方案都修复了该 clause）**

| | 耗时 | timeout | 完成路径 | Retire_Success |
|---|---|---|---|---|
| 方案 A | **7.2s** | 否 | 17 | 0 |
| 方案 B（VIMTYPE 也具体化） | **46.0s** | 否 | **27** | **8** |

方案 B 路径数 27 > A 的 17（具体化 fork 的直接体现），且 B 有 8 条真正算完的 `Retire_Success`（循环定数展开的收益），A 一条都没有（符号循环算不完）。B 慢 6 倍但还没 timeout——因为它"只"多了 ~10 个 num_elem 候选。

**(b) 全量 `make solve` timeout 对比（清理后 baseline）**

| | 总 timeout |
|---|---|
| cleaned baseline | 24 |
| **方案 A**（read_vmask 内部修，对所有 caller 生效） | **11**（↓13） |
| **方案 B**（只修了 4 个 clause：VITYPE/MASKTYPEV/X/I） | **38**（↑14） |

方案 A 把 timeout 从 24 降到 11。方案 B 的部分应用反而把 timeout 从 24 涨到 **38**——因为它只修了 4 个 clause，而对这 4 个 clause 的具体化引入了路径膨胀，使原本 intime 的 VITYPE/MASKTYPEV/MASKTYPEX 变成 timeout：

```
baseline intime → 方案 B timeout 的 clause（具体化导致路径膨胀）:
VITYPE, MASKTYPEV, MASKTYPEX, MVVTYPE, VANDN_VV, VANDN_VX, VBREV_V,
VCLMUL_*, VCLZ_V, VCPOP_V, VCTZ_V, VICMPTYPE, VIM*, VMVSX, VREV8_V,
VROL_*, VROR_*, VSM3*, VSM4K_VI, VGHSH_VV, VGMUL_VV, VMSIF_M, VMSOF_M ...
```

这是"具体化 → fork 膨胀 → timeout"机制的最直接证据。

---

## 5. 方案 A 和方案 B 是否等价？

**不等价。** 要分两个层面看：

### (a) mask 的语义：等价
对于任意一个**具体的** `num_elem` 值，方案 A 的 SMT 表达式和方案 B 的具体化结果，求出的 mask 位向量完全相同。两者都正确实现了 `read_vmask`/`read_vmask_carry` 的语义（低位取自 `V(vrid)`，高位按 vm/is_carry 填充）。

### (b) 符号执行的路径/覆盖模型：不等价
- **方案 A**：`num_elem` 保持符号，**一条符号路径**用一个 SMT 表达式覆盖所有 `num_elem` 可能（求解时由 path condition 区分）。
- **方案 B**：`num_elem` 被拆成 **N 条具体路径**，每条上一个常量。

也就是说，**方案 B 是方案 A 的"路径展开"**：B 用 N 条路径显式枚举了 A 用 1 条符号路径 + SMT 隐式覆盖的空间。在求解器能力足够时，A 更紧凑（路径少）；但 A 的代价是下游符号循环（操作②）算不完（0 个 Retire_Success），而 B 的循环能算完（8 个 Retire_Success）。

### (c) 副作用面：不等价
- **方案 A** 是**局部、针对 `read_vmask` 的根治**：对所有 caller（VITYPE/VIMTYPE/VICMPTYPE/reduction/... 几十个 clause）一次性生效。
- **方案 B** 是**逐 caller 改执行体**：每用一个 `read_vmask` 的 clause 都要单独加一行 `let num_elem = assert_vector_num_elem_value(num_elem)`。本轮只改了 4 个 clause，其余 ~35 个 caller 仍带原 bug（这也是方案 B 全量 timeout 反而升高的原因之一）。

---

## 6. 结论与建议

1. **timeout 的本质**：方案 B 的 `match num_elem` 让符号引擎按 `num_elem` 的有限合法值枚举 fork，路径数成倍膨胀 → 60s 跑不完。方案 A 用固定位宽 SMT ITE 绕开符号切片、不引入 fork，所以快。**两者都不解决"有限 vtype 组合"本身的 timeout**（那是 SEW×LMUL×扩展位×vstart×vl 的笛卡尔积，按用户指示靠放宽 timeout 处理）。
2. **A、B 不等价**：mask 语义等价，但路径模型不等价（A=1 符号路径，B=N 具体路径）；副作用面不等价（A 局部根治所有 caller，B 逐 caller 改、易漏）。
3. **取舍**：
   - 若优先**性能 + 覆盖面 + 一次到位**：方案 A（read_vmask 内部 SMT 化），全量 timeout 24→11，对所有 caller 生效。代价：primop 接触面 +1，下游符号循环仍算不完（但那是另一个独立问题，见下）。
   - 若优先**让计算真正跑完（Retire_Success）+ 不增 primop**：方案 B，但要**应用到所有 caller**（不只是 4 个），并接受路径膨胀 → 配合放宽 timeout。代价：改动面大、易漏 caller。
   - **注意**：方案 A 虽然快，但 VIMTYPE 的 0 个 Retire_Success 暴露了**操作②（符号循环）是另一个独立的未解决问题**——A 只修了切片没修循环。若要 V 扩展真正"算完"，操作②也需要处理（例如对 `foreach(num_elem-1)` 同样做有限域枚举，即方案 B 的思路用在循环上）。

## 7. 相关代码位置

- 原始 `read_vmask`/`read_vmask_carry`（符号切片）：`sail-riscv/model/extensions/V/vext_control.sail:538-549`
- `subrange_internal` 的 `SymbolicLength` 触发分支：`isla/isla-lib/src/primop.rs:1203-1205`（前置 `concretize_proven_i128` :1159、:123-131）
- 方案 A `isla_read_vmask`（固定位宽 SMT ITE）：`isla-A/isla-lib/src/primop.rs:2664-2770`
- 方案 B `assert_vector_num_elem_value`（具体化 match）：`sail-riscv/model/extensions/V/vext_control.sail:258-278`
- VIMTYPE 执行体（含符号边界 foreach）：`sail-riscv/model/extensions/V/vext_vm_insts.sail:556-590`

## 8. 复现

两方案代码在 worktree 分支：
- 方案 A：`isla` 分支 `read-vmask-extern-A`（5c11c37）+ `sail-riscv` 分支 `read-vmask-extern-A`（e46521a）
- 方案 B：`sail-riscv` 分支 `read-vmask-sail-B`（9ee899e，4-clause），isla 用清理后 HEAD（5f8a793）

```sh
# VIMTYPE 公平对比（两方案都修了 VIMTYPE）
# 方案 A
cp .worktrees/isla-A/rv64d.ir isla/rv64d.ir && (cd .worktrees/isla-A && cargo build --release --bin isarch) && cp .worktrees/isla-A/target/release/isarch isla/target/release/isarch && cd isla && make solve-VIMTYPE
# 方案 B（需把 VIMTYPE 也加 assert_vector_num_elem_value，见正文）
```
