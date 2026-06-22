# Z3 枚举类型 model 解析修复说明

## 背景：isla 如何用 Z3 做符号执行

isla 对一条指令做符号执行的大致流程：

1. **创建符号参数**：`symbolic_args_from_types` 为指令的每个参数创建 Z3 符号常量。如果参数是枚举类型（`Ty::Enum`），先调用 `solver.get_enum(name, size)` 注册枚举（触发 `Def::DefineEnum` 事件），然后调用 `solver.declare_const(Ty::Enum(enum_id))` 声明一个该枚举类型的符号变量。

2. **打 checkpoint**：符号参数创建完后，调用 `checkpoint(&mut solver)` 保存当前 trace（记录了所有 `DefineEnum`、`DeclareConst`、`Assert` 等事件）。

3. **执行指令**：executor 从 checkpoint 创建新的 solver，回放 trace 重建状态，然后符号执行指令体。执行过程中可能产生多条路径（fork）。

4. **读取 model**：每条路径执行完后，如果 `check_sat` 返回 `Sat`，调用 `Model::new(&solver)` 获取一个具体的满足解，用于生成汇编字符串。`model.get_val(var)` 会递归地对 `Val::Struct` 的每个字段调用 `get_var` → `get_ast` 来提取具体值。

## 改之前的心智模型

### 枚举的注册（写）

`DefineEnum(name, size)` 事件处理时：

```rust
let z3_name = self.fresh();           // 全局递增的 Sym id
let members = (0..*size)
    .map(|_| self.fresh())            // 每个成员也是全局递增的 Sym id
    .collect();
self.enums.add_enum(*name, z3_name, &members)
```

`add_enum` 内部调用 `Z3_mk_enumeration_sort`，把 `z3_name` 和 `members` 作为 Z3 symbol 传进去，Z3 返回 `sort`（sort 对象）、`consts`（每个成员的构造函数 `Z3_func_decl`）、`testers`（每个成员的识别谓词 `Z3_func_decl`）。这三者都存在 `Enums` 表里。

### 枚举的读取（读）

`get_ast` 收到一个 `SortKind::Datatype` 的 Z3 AST 时，旧代码的做法是：

```rust
let func_decl = Z3_get_app_decl(z3_ctx, Z3_to_app(z3_ctx, z3_ast));
for (enum_id, enumeration) in self.solver.enums.enums.iter() {
    for (i, member) in enumeration.consts.iter().enumerate() {
        if Z3_is_eq_func_decl(z3_ctx, func_decl, *member) {
            // 匹配成功
        }
    }
}
// 匹配失败 => Err(ExecError::NoModel)
```

即：**用指针相等（`Z3_is_eq_func_decl`）来判断 model 返回的构造函数和注册时的构造函数是不是同一个 Z3 对象**。

### 为什么会失败

关键在 `from_checkpoint`：

```rust
pub fn from_checkpoint(ctx, checkpoint) -> Self {
    let mut solver = Solver::new(ctx);   // 全新的 Solver，enums 是空的
    solver.replay(num, trace);           // 回放 trace 中的所有事件
    solver
}
```

`replay` 会重新执行 `DefineEnum` 事件，再次调用 `Z3_mk_enumeration_sort`。但 **Z3 每次调用 `Z3_mk_enumeration_sort` 都会创建一个全新的 sort 对象**，即使参数完全相同。所以：

- **原始 solver** 的 `enums` 里有 sort_A、consts_A
- **from_checkpoint 的 solver** 的 `enums` 里有 sort_B、consts_B（replay 重建的）

而 Z3 solver 内部的 assert/model 记录的是 **原始 solver 创建的 sort_A**（因为 checkpoint 之前 solver 就已经把约束加到 Z3 solver 里了）。`from_checkpoint` 创建的新 solver 共享同一个 Z3 context，但 `Z3_mk_enumeration_sort` 返回的 sort_B 和 sort_A 是不同的 Z3 对象。

当 `Model::new` 调用 `Z3_model_eval` 拿到一个枚举值时，这个值的 func_decl 属于 sort_A。但 `get_ast` 用 `Z3_is_eq_func_decl` 比较的是 consts_B——指针不同，匹配失败，返回笼统的 `NoModel`。

### `fresh()` 加剧了问题

即使不考虑 sort 指针差异，`fresh()` 本身也有问题。`fresh()` 返回 `self.next_var` 并递增。原始 solver 调用 `fresh()` 时 `next_var` 可能从 100 开始（因为前面已经声明了很多符号变量）。但 `from_checkpoint` 的 solver 是全新的，`next_var` 从 0 开始（然后被设为 checkpoint 保存的值）。replay 时 `DefineEnum` 再次调用 `fresh()`，得到的 Sym id 和原始 solver 不同。

这意味着即使我们后来加了基于 `Z3_get_symbol_string` 的字符串比较，也不会匹配——因为原始 solver 用的是 `fresh()` 生成的随机 id（如 `"101"`），而 replay 后生成的是不同的 id（如 `"1"`）。

## 改之后的心智模型

### 改动 1：枚举注册用确定性 symbol 名

```rust
Def::DefineEnum(name, size) => {
    let z3_name = Sym::from_u32(name.as_u32());
    let members: Vec<Sym> = (0..*size).map(|_| self.fresh()).collect();
    self.enums.add_enum(*name, z3_name, &members)
}
```

只保留 enum **sort 名** 的确定性：`Name::as_u32()` 直接作为 Z3 sort symbol。member constructor 名继续用 `fresh()`，因为 `get_ast` 现在用 model 值自身 sort 的 recognizer 匹配 constructor，不再依赖 member symbol 稳定性。

这样 replay 后同一个 enum 的 sort 名一致，足够把 recognizer 匹配出的 constructor index 映射回 `EnumId`。

### 改动 2：get_ast 用 model 值自身 sort 的 recognizer 匹配 constructor

**关键洞察**：之前所有方案失败的根因是——tester/recognizer 来自我们注册的 enum（replay 后的 sort），而 model 值来自原始 sort，两者是不同的 Z3 sort 对象。

`Z3_get_datatype_sort_recognizer(z3_ctx, sort, idx)` 可以从 **model 值自己的 sort** 上直接获取 recognizer。这样 recognizer 和 model 值天然属于同一个 sort 对象，`Z3_model_eval` 一定能正确评估。

```rust
} else if sort_kind == SortKind::Datatype {
    // 1. 从 model 值的 sort 获取 constructor 数量
    let n_ctors = Z3_get_datatype_sort_num_constructors(z3_ctx, sort);

    // 2. 遍历每个 constructor，用 sort 自身的 recognizer 评估
    let mut ctor_idx = None;
    for i in 0..n_ctors {
        let recognizer = Z3_get_datatype_sort_recognizer(z3_ctx, sort, i);
        let tester_app = Z3_mk_app(z3_ctx, recognizer, 1, &z3_ast);
        let mut eval_result = ...;
        Z3_model_eval(z3_ctx, model, tester_app, true, &mut eval_result);
        if Z3_get_bool_value(eval_result) == Z3_L_TRUE {
            ctor_idx = Some(i);  // 第 i 个 constructor 匹配
            break;
        }
    }

    // 3. 通过 sort id 还原 Name，再查正向表
    let sort_id = Z3_get_symbol_int(z3_ctx, Z3_get_sort_name(z3_ctx, sort));
    let enum_name = Name::from_u32(sort_id as u32);
    self.solver.enums.enums.get(&enum_name)
        .map(|enum_info| Exp::Enum(EnumMember { enum_id: enum_name, member: ctor_idx }))
}
```

**为什么这个方案完全遵守 functional 设计**：
- 不共享任何状态——recognizer 从 model 值的 sort 上查询，不是从注册的 enum 表上拿
- 不依赖 Z3 对象指针相等——recognizer 和 model 值属于同一个 sort，由 Z3 保证类型一致
- 不需要反向缓存表——sort id 就是 `Name::as_u32()`，可直接 `Name::from_u32(sort_id as u32)` 还原
- 对单成员和多成员枚举**一视同仁**——都用 recognizer 评估，无需特殊路径

**为什么确定性命名（改动 1）仍然保留**：recognizer 方案不依赖确定性命名做 constructor 匹配，但 constructor index 映射回 `EnumId` 时需要 sort id 在 replay 后一致。`Name::as_u32()` 作为 sort symbol 保证这一点。

## 改动文件

- `isla-lib/src/ir.rs`
  - `Name::as_u32()`：提供稳定的 Name id 访问器，避免通过 `Display`/parse 取 id
- `isla-lib/src/smt.rs`
  - `add_internal` 的 `Def::DefineEnum` 分支：用 `Name::as_u32()` 作为确定性 sort symbol
  - `get_ast` 的 `SortKind::Datatype` 分支：用 model 值自身 sort 的 recognizer 匹配 constructor，再用 sort id 还原 `Name` 并查正向表

## 验证

修改前：VIMSTYPE 三条路径全部报 `model.get_val失败 NoModel`，无法生成汇编。

修改后（三种场景全部成功）：
- VIMSTYPE（单成员枚举 + replay）：成功生成汇编 `vadc.vim v0, v0, 0x0, v0`
- F_MADD_TYPE_S（多成员枚举 + replay）：成功生成汇编 `fmadd.s f0, f31, f31, f31, dyn`
- RTYPE（无枚举参数）：30 条路径全部生成汇编
- 8 个 SMT 单元测试全部通过；新增覆盖 checkpoint replay 后单成员 enum、多成员 enum、以及 `Val::Struct` 中混合 enum/bitvector 字段的 model 提取
