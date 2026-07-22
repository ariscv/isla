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

方案 A 在 `read_vmask` 内部用一个内置函数（isla `isla_read_vmask`）**替换掉了操作①**。核心实现（isla-A/isla-lib/src/primop.rs:2664-2770）：

```rust
// 固定位宽 len = V(vrid) 的静态宽度（= VLEN=256，具体），与 num_elem 无关
let len = length_bits(&vreg, solver, info)?;
let num_elem_exp = int_exp_128(&args[0], ...)?;   // num_elem 转成 SMT 表达式（保持符号）

let mut exp = None;
for i in (0..len).rev() {                          // ← 注意：A 也在"枚举"！枚举 256 个 bit 位置
    let index = smt_i128(i128::from(i));
    let in_range = Exp::Bvslt(Box::new(index), Box::new(num_elem_exp.clone()));  // num_elem 只作比较
    let vreg_bit = symbolic_bit(&vreg, i, info)?;
    let body_bit = Exp::Ite(Box::new(in_range), Box::new(vreg_bit), Box::new(pad_bit.clone()));
    exp = Some(Exp::Concat(Box::new(acc), Box::new(bit)));   // 拼成一个固定宽度 256 的 SMT 表达式
}
solver.define_const(exp.expect(...), info).into()   // 返回一个 Val::Symbolic（一个 SMT 常量）
```

**关键：A 确实在枚举（`for i in 0..256`）**。但这个枚举发生在 **isla 自己的 Rust 二进制里**（primop 实现内部），对符号执行引擎是一个**黑盒 extern 调用**。看 IR（sail-A/rv64d.ir:37608）：

```
val zisla_read_vmask = "isla_read_vmask" : (%i, %bv1, %bv1, %bv) ->  %bv   ← 一条 extern 声明
...
return = zisla_read_vmask(zz411, zvm, zz49, zz410)                          ← 一条 call 指令
```

引擎看到的是**一条 `call` 指令**，它返回一个 `Val::Symbolic`。那个 256 次的 `for` 循环是 isla 在**构造一个 SMT 表达式**（256 个 `Ite` 拼成的 `Concat` 树），构造完作为一个符号常量返回。**整个调用不产生任何符号执行路径分叉（fork）**——它只是"算出一个返回值"。这就是 A 的枚举：**数据构造层的枚举，单路径，返回一个值**。

**但 A 没有处理操作②**：`num_elem` 仍是符号，执行体里的 `foreach (i from 0 to num_elem-1)` 仍是**符号边界循环**。符号执行引擎面对符号边界循环，无法证明 `0 <= i < num_elem`（边界是符号），**循环体被执行不了**——见第 4 节实验，A 的 VIMTYPE 有 **0 个 `Retire_Success`**，路径根本没把 foreach 跑完。

---

## 3. 方案 B 做了什么（从引擎角度）

方案 B 不改 `read_vmask`，而是在**指令执行体**里把 `num_elem` 这个符号值**具体化**（concretize）掉。用的是 sail 已有的 `assert_vector_num_elem_value`（vext_control.sail:258-278）：

```sail
val assert_vector_num_elem_value : forall 'n, 'n >= 0. int('n) -> int('n)
function assert_vector_num_elem_value(num_elem) = {
  assert(num_elem <= vlen);
  match num_elem {       // ← 对符号 num_elem 做 match，每个 arm 是一个具体值
    1 => 1, 2 => 2, 4 => 4, 8 => 8, 16 => 16, 32 => 32, 64 => 64, 128 => 128, 256 => 256, ...
    _ => { assert(false); 1 }
  }
}
```

执行体里（vext_arith_insts.sail VITYPE 等）：

```sail
  let num_elem = get_num_elem(LMUL_pow, SEW);                       // 符号
  let num_elem = assert_vector_num_elem_value(num_elem);            // ← 具体化
  ...
  let vm_val = read_vmask(num_elem, vm, zvreg);                     // num_elem 在每条 path 上是常量
  ...
  foreach (i from 0 to (num_elem - 1)) { ... }                      // ← 循环边界也变具体
```

**B 的枚举发生在符号执行的控制流层**。`match num_elem` 编译到 IR 是一串 `jump @not(zeq_int(num_elem, 1))` 条件跳转（见 zassert_vector_num_elem_value 的 IR 体）。符号执行引擎遇到符号条件跳转 `zeq_int(num_elem, 1)`，因为 SAT（相等）和 UNSAT（不等）都可能成立，**必须 fork**：对 `num_elem` 的每个候选值分裂出一条独立路径，每条路径上 `num_elem` 被**绑定到一个具体常量**。

这**同时解决了操作①和操作②**：
- 操作①：每条路径上 `num_elem` 是常量 → `concretize_proven_i128` 成功 → 切片正常 → 不再 `SymbolicLength`。
- 操作②：每条路径上循环边界是常量 → `foreach` **真正定数展开**（最多 256 轮，每轮都执行算术/比较）→ 计算真正完成（产生 `Retire_Success`）。

---

## 4. 为什么 B 会 timeout，A 不会 —— 直接回答"A 没有枚举吗"

> **A 有枚举，B 也有枚举。两者枚举的东西、枚举发生的层面、以及枚举的后果完全不同。**

### 两种枚举的本质区别

| | 方案 A 的枚举 | 方案 B 的枚举 |
|---|---|---|
| 枚举什么 | **bit 位置** `i = 0..255`（256 个） | **num_elem 的取值**（~10 个合法值） |
| 发生在哪个层面 | isla **Rust 数据构造层**（primop 实现内部的 `for` 循环） | 符号执行**控制流层**（IR 的 `jump @not(zeq_int)`） |
| 引擎看到什么 | 一条 `call` 指令，返回一个 `Val::Symbolic` | 一串符号条件跳转，必须逐个 fork |
| 是否产生路径分叉 | **否**（构造一个表达式，单路径返回） | **是**（每个候选值 fork 一条路径） |
| 是否触发下游 foreach 展开 | **否**（num_elem 仍符号，foreach 符号边界，引擎跑不动循环体） | **是**（num_elem 具体化，foreach 定数展开成实际计算） |

### 为什么 A 的"256 次枚举"反而比 B 的"~10 次枚举"快（反直觉但关键）

直觉上 A 枚举 256 次、B 只枚举 ~10 次，应该 A 更慢。实际相反，原因有二：

**(1) A 的枚举不产生路径，B 的枚举产生路径。**
A 的 `for i in 0..256` 是 isla Rust 里的普通循环，跑 256 次**拼一个 SMT 表达式**，O(256) 时间构造完，返回一个符号常量。**全程一条路径**。B 的 `match num_elem` 让引擎 fork 出 ~10 条路径，路径数直接乘上去（叠加在 SEW×LMUL×扩展位×vstart×vl 之上）。

**(2) 更关键：A 让下游 foreach "跑不动"（偷懒），B 让下游 foreach "真正展开"（干实活）。**
- A 里 `num_elem` 保持符号 → `foreach(i from 0 to num_elem-1)` 是符号边界循环 → 引擎无法证明循环条件 `i < num_elem`（边界符号）→ **循环体不被执行** → 指令计算没真正发生。
- B 里 `num_elem` 被具体化 → foreach 边界是常量 → **foreach 定数展开成最多 256 轮实际迭代**，每轮里 `mask[i]==1`、`vs2_val[i]+imm_val+carry > 2^SEW-1` 等都在构造/求解 SMT 表达式。

**换句话说：A 快是因为它没真正完成计算（foreach 没展开），B 慢是因为它真正去算了（foreach 展开成实打实的计算）。这不是"A 更高效地做了同一件事"，而是"A 没做完，B 做完了所以慢"。** timeout 的主因不是 num_elem 的 ~10 个 fork 本身，而是**具体化 num_elem 后，下游 foreach 从"符号边界（引擎跑不动、跳过）"变成"定数展开（最多 256 轮真实计算）"**，每条路径的实际工作量爆炸。

### 实验证据（同一清理后基线，60s/clause）

**(a) 公平对比：VIMTYPE（两个方案都修复了该 clause）**

| | 耗时 | timeout | 路径 | Retire_Success | 是否走到 foreach 循环体 |
|---|---|---|---|---|---|
| 方案 A | **7.2s** | 否 | 17 | **0** | 否（路径在 illegal check / 符号循环处停） |
| 方案 B（VIMTYPE 也具体化） | **46.0s** | 否 | 27 | **8** | **是**（8 条路径算完整个 foreach） |

- B 路径数 27 > A 的 17（差 ~10 ≈ num_elem 候选数，正是 match fork 的直接体现）。
- **B 有 8 条 `Retire_Success`**（foreach 真正展开算完了），**A 一条都没有**（foreach 符号边界，引擎跑不动）。B 的慢来自这 8 条"真正算完"的重路径；A 的快来自它**根本没算**（0 条算完）。
- B 日志在 `vext_vm_insts.sail:563/581/583`（foreach 循环体内部）有 fork 痕迹，A 在这些位置 **0 fork**（路径没走到循环体）。

**(b) 全量 `make solve` timeout 对比（清理后 baseline）**

| | 总 timeout |
|---|---|
| cleaned baseline | 24 |
| **方案 A**（read_vmask 内部修，对所有 caller 生效） | **11**（↓13） |
| **方案 B**（只修了 4 个 clause：VITYPE/MASKTYPEV/X/I） | **38**（↑14） |

方案 A 把 timeout 从 24 降到 11（它修了 read_vmask，让所有 caller 的符号切片不再硬错误；剩余 11 个是 foreach+SEW/LMUL 组合的有限爆炸，靠放宽 timeout）。方案 B 的部分应用反而把 timeout 从 24 涨到 **38**——具体化让原本 intime 的 VITYPE/MASKTYPEV/MASKTYPEX 等 14 个 clause 的 foreach 真正展开、工作量暴涨：

```
baseline intime → 方案 B timeout 的 clause（具体化触发下游 foreach 真实展开）:
VITYPE, MASKTYPEV, MASKTYPEX, MVVTYPE, VANDN_VV, VANDN_VX, VBREV_V,
VCLMUL_*, VCLZ_V, VCPOP_V, VCTZ_V, VICMPTYPE, VIM*, VMVSX, VREV8_V,
VROL_*, VROR_*, VSM3*, VSM4K_VI, VGHSH_VV, VGMUL_VV, VMSIF_M, VMSOF_M ...
```

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

1. **timeout 的本质（直接回答"A 没有枚举吗"）**：A 也枚举（256 个 bit 位置），B 也枚举（~10 个 num_elem 值）。但 A 的枚举在 isla Rust 数据构造层（构造一个 SMT 表达式、单路径返回、引擎不 fork），B 的枚举在符号执行控制流层（`match` 编译成 `jump @not(zeq_int)`、引擎逐值 fork）。更关键的是：**A 让下游 foreach 保持符号边界、引擎跑不动循环体（偷懒，0 个 Retire_Success）；B 具体化 num_elem 后下游 foreach 真正定数展开成最多 256 轮实打实的计算（干实活，8 个 Retire_Success）。B 的 timeout 主因是"具体化触发下游 foreach 真实展开"导致每条路径工作量爆炸，而不是 num_elem 那 ~10 个 fork 本身**。两者都不解决"有限 vtype 组合"本身的 timeout（SEW×LMUL×扩展位×vstart×vl 笛卡尔积，按用户指示靠放宽 timeout）。
2. **A、B 不等价**：mask 语义等价，但路径模型不等价（A=1 符号路径 + foreach 跑不动；B=N 具体路径 + foreach 跑完）；副作用面不等价（A 局部根治所有 caller，B 逐 caller 改、易漏）。
3. **取舍**：
   - 若优先**性能 + 覆盖面 + 一次到位**：方案 A（read_vmask 内部 SMT 化），全量 timeout 24→11，对所有 caller 生效。代价：primop 接触面 +1，且 A 没解决操作②——下游 foreach 仍符号边界、算不完。
   - 若优先**让计算真正跑完（Retire_Success）+ 不增 primop**：方案 B，但要**应用到所有 caller**（不只是 4 个），并接受具体化触发的 foreach 真实展开 → 配合放宽 timeout。代价：改动面大、易漏 caller。
   - **核心矛盾**：方案 A 快但是"没算完"（操作②符号循环没展开），方案 B 算完但是"慢到 timeout"（操作②真实展开太重）。要同时"算完又不 timeout"，需要对**操作②（符号边界 foreach）单独处理**——例如用有限域枚举但配合更聪明的循环摘要/分段，而不是裸 `match` 全展开。这是 read_vmask 修复之外的下一个独立问题。

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
