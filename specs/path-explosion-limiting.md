# 符号执行路径爆炸限制策略技术文档

## 1. 背景与问题

Isla 是一个基于 Sail ISA 规范的符号执行引擎。在符号执行过程中，每当遇到符号化的条件分支，引擎需要 **fork**（分叉）出两条执行路径，分别探索两个分支。这会导致路径数量呈指数级增长——即**路径爆炸**（path explosion）问题。

具体来说，路径爆炸在以下场景中尤为严重：

1. **循环**（Loop）：循环体的每次迭代都可能产生分支，N 次迭代可产生 O(2^N) 条路径
2. **串行条件链**（Serial if-else chain）：连续多个独立的符号分支，M 个分支产生 O(2^M) 条路径
3. **热点分支**（Hot branch）：某个分支点被反复执行（如循环内的条件判断），其 fork 数远超其他分支

为解决这一问题，Isla 实现了**两套独立的限制机制**：

- **`ExecutionLimits`**（本文重点）：通用的多层限制框架，控制 IR 级别的执行深度、分支 fork 和循环回边
- **`pc_limit`**：面向 litmus 测试场景的架构级 PC 限制，按指令地址控制重复执行次数

---

## 2. 整体架构

```
┌──────────────────────────────────────────────────────────────────┐
│                        ExecutionLimits                            │
│  (配置层：定义各项阈值和行为策略，Builder 模式可组合)                  │
├──────────────────────────────────────────────────────────────────┤
│  max_path_depth            │ 路径深度上限                          │
│  max_backjumps_per_loop    │ 循环回边次数上限                      │
│  max_total_forks           │ 全局 fork 总数上限                    │
│  max_forks_per_branch      │ 单分支点 fork 上限                    │
│  max_fork_pct_per_branch   │ 自适应百分比限制                      │
│  max_fork_pct_check_delay  │ 百分比检查热身期延迟                   │
│  on_limit_reached          │ 触发行为策略 (Truncate / Concretize)  │
├──────────────────────────────────────────────────────────────────┤
│                    ExecutionLimitsState                            │
│  (运行时状态：跨任务共享的计数器，线程安全)                           │
├──────────────────────────────────────────────────────────────────┤
│  branch_fork_counts  │ 每个分支点的累计 fork 数                     │
│  total_forks         │ 全局 fork 总计数                            │
├──────────────────────────────────────────────────────────────────┤
│                     Frame / LocalFrame                             │
│  (每条路径的局部状态，fork 时继承)                                   │
├──────────────────────────────────────────────────────────────────┤
│  step_count         │ 当前路径已执行的 IR 指令数                    │
│  forks              │ 当前路径产生的 fork 数                       │
│  loop_counts        │ 每个 PC 位置的循环回跳次数                   │
│  branch_conditions  │ 路径上积累的分支条件列表                     │
│  pc_counts          │ 每个架构 PC 的出现次数（用于 pc_limit）       │
└──────────────────────────────────────────────────────────────────┘
```

**源码位置**：
- `ExecutionLimits` / `ExecutionLimitsState`：`isla-lib/src/executor/task.rs:76-170`
- `Frame` / `LocalFrame`：`isla-lib/src/executor/frame.rs:104-167`
- 限制检查逻辑：`isla-lib/src/executor.rs:1088-1321`
- Concretize 逻辑：`isla-lib/src/executor.rs:1008-1028`
- 错误类型：`isla-lib/src/error.rs:87-143`

---

## 3. 两层限制检查

Isla 的限制策略由两层组成，它们在 `run_loop` 的指令分发阶段被检查。这两层的**决策时机不同**：

1. **预评估层**（在评估分支条件之前）：路径深度限制和循环回边限制
2. **Fork 层**（在确认符号分支两路都可满足之后）：全局 fork、单分支 fork、百分比限制

任一检查触发即执行 `on_limit_reached` 行为（OR 语义）。

### 3.1 路径深度限制（`max_path_depth`）

**目的**：防止单条执行路径过长（例如无限递归、超长指令序列）。

**检查位置**：`Instr::Jump`（`executor.rs:1093-1100`）、`Instr::Goto`（`executor.rs:1307-1310`）、`Instr::Call`（`executor.rs:1366-1370`）。

**机制**：每次执行 Jump/Goto/Call 指令时递增 `frame.step_count`，检查是否超过阈值。

```rust
// executor.rs:1089
frame.step_count += 1;
if let Some(max_depth) = limits.max_path_depth {
    if frame.step_count as u64 > max_depth {
        match limits.on_limit_reached {
            LimitBehavior::Truncate => return Err(ExecError::DepthLimitReached),
            LimitBehavior::Concretize => limit_reached = true,
        }
    }
}
```

**`path depth` 的含义**：`step_count` 计的不是 AST 深度，也不是函数调用栈深度，而是 **IR 指令执行步数**——每遇到 Jump、Goto、Call 就加一。它约束的是"当前路径已经执行了多少条 IR 指令"，适合挡住长路径和非终止路径。

**特点**：
- 计数器 `step_count` 是**每条路径独立**的（存储在 Frame 中）
- **Frame 继承语义**：fork 时子帧继承父帧的 `step_count`，因此阈值是相对于**整条执行路径**（从根任务到当前节点）计算的，而非从 fork 点开始
- 对于 Goto 和 Call（无条件控制流），即使配置了 Concretize 也只能 Truncate，因为没有符号条件可供具体化
- 触发错误：`ExecError::DepthLimitReached`

### 3.2 循环回边限制（`max_backjumps_per_loop`）

**目的**：检测并限制无限循环和过深的循环迭代。

**检查位置**：`Instr::Jump`（`executor.rs:1103-1117`）和 `Instr::Goto`（`executor.rs:1312-1319`）。

**机制**：当跳转目标 PC 小于等于当前 PC 时，判定为**回边**（back-edge）。使用 `frame.loop_counts` 这个 HashMap 记录每个目标 PC 的回跳次数。

```rust
// executor.rs:1103-1117
if let Some(max_backjumps) = limits.max_backjumps_per_loop {
    if *target <= frame.pc {                          // 回边检测：目标 <= 当前 PC
        let count = frame.loop_counts.entry(*target).or_insert(0);
        *count += 1;
        if *count > max_backjumps {
            match limits.on_limit_reached {
                LimitBehavior::Truncate => {
                    return Err(ExecError::LoopLimitReached(frame.function_name, *target))
                }
                LimitBehavior::Concretize => limit_reached = true,
            }
        }
    }
}
```

**回边判定逻辑**：
```
当前 PC = 5, 目标 PC = 3  →  target(3) <= pc(5)  →  回边 ✓（循环）
当前 PC = 5, 目标 PC = 8  →  target(8) >  pc(5)  →  前向跳转 ✗
```

这种判定不依赖源码中的 `loop` 关键字，而是看"是否回跳"，因此能覆盖两类情况：
- 典型 `while` / `for` 回边
- 由 `goto` 形成的非结构化回跳

**特点**：
- `loop_counts` 是**每条路径独立**的 HashMap，key 为目标 PC
- **Frame 继承语义**：与 `step_count` 相同，fork 时子帧继承父帧的 `loop_counts`
- 支持 Concretize 行为（在 Jump 指令中）：当触发时，将循环条件的符号变量具体化为一个布尔值，选择一条路径继续执行
- 对于 Goto 指令（无条件跳转），只能 Truncate
- 触发错误：`ExecError::LoopLimitReached(function_name, target_pc)`

### 3.3 全局 fork 总数限制（`max_total_forks`）

**目的**：限制当前路径上的 fork 总数，防止路径数量失控。特别能有效捕获**串行 if-else 链**的场景——即使每个分支点只 fork 一次，连续 M 个分支点也会产生 2^M 条路径。

**检查位置**：`Instr::Jump`（`executor.rs:1163-1185`），仅在符号分支**两路都可满足**时检查。

**机制**：检查当前帧的 `frame.forks` 计数器，每次成功 fork 后递增。

```rust
// executor.rs:1163-1185
if let Some(max_total) = limits.max_total_forks {
    if frame.forks >= max_total {
        match limits.on_limit_reached {
            LimitBehavior::Truncate => {
                return Err(ExecError::BranchLimitReached(frame.function_name, frame.pc))
            }
            LimitBehavior::Concretize => {
                let concrete_bool = concretize_branch_condition(v, solver, *info)?;
                // 选择一条路径继续执行...
            }
        }
    }
}
```

**特点**：
- `frame.forks` 是**每条路径独立**的计数器
- 在多线程执行中，fork 出的子任务继承父任务的 forks 值并各自递增
- 有效应对串行分支链：5 个连续的独立 if-else 在 `max_total_forks=2` 时，只有前 2 个分支点会真正 fork
- 触发错误：`ExecError::BranchLimitReached(function_name, pc)`

**`max_forks_per_branch` 无法替代它**：测试 `real_ir_per_branch_cannot_detect_serial_chain`（`executor.rs:3290-3298`）清楚地展示了——单独使用 `max_forks_per_branch=2` 时，5 个串行的独立分支点每个只 fork 一次，均不超限，最终全部通过。这是因为 `max_forks_per_branch` 按 `(function_name, pc)` 统计，不同分支点互不影响。只有 `max_total_forks` 能从全局视角捕获这种串行爆炸模式。

### 3.4 单分支点 fork 限制（`max_forks_per_branch`）

**目的**：限制同一个分支点的 fork 次数，防止循环内同一条件反复 fork 导致爆炸。

**检查位置**：`Instr::Jump`（`executor.rs:1187-1211`）。

**机制**：使用**跨任务共享**的 `ExecutionLimitsState.branch_fork_counts`，以 `(function_name, pc)` 为 key 追踪每个分支点的累计 fork 数。

统计粒度选择 `(function_name, pc)` 而非"语句文本"，是为了确保同一个 IR PC 在不同函数里的行为不会互相干扰。

```rust
// executor.rs:1187-1211
if let Some(max_forks) = limits.max_forks_per_branch {
    let fork_count = task_state.limits_state
        .increment_branch_fork(frame.function_name, frame.pc);
    if fork_count > max_forks {
        match limits.on_limit_reached {
            LimitBehavior::Truncate => {
                return Err(ExecError::BranchLimitReached(frame.function_name, frame.pc))
            }
            LimitBehavior::Concretize => {
                let concrete_bool = concretize_branch_condition(v, solver, *info)?;
                // 选择一条路径继续执行...
            }
        }
    }
}
```

**与 `max_total_forks` 的互补关系**：

| 维度 | `max_total_forks` | `max_forks_per_branch` |
|------|-------------------|----------------------|
| 作用域 | 单条路径上的 fork 总数 | 同一分支点的 fork 数（跨所有路径） |
| 计数器 | `frame.forks`（帧本地） | `limits_state.branch_fork_counts`（全局共享） |
| 擅长捕获 | 串行 if-else 链 | 循环内重复分支 |
| 漏报场景 | 无法单独限制循环内分支 | 无法检测串行链（每点 fork 一次均不超限） |

两者必须配合使用，才能同时覆盖串行链和循环内分支两种爆炸模式。

### 3.5 自适应百分比限制（`max_fork_pct_per_branch`）

**目的**：自适应地抑制占比过高的"热点"分支。灵感来自 KLEE 的 `MaxStaticForkPct` 策略。

**检查位置**：`Instr::Jump`（`executor.rs:1213-1243`）。

**机制**：当某个分支点的 fork 数占全局 fork 总数的比例超过阈值时触发。

```rust
// executor.rs:1213-1243
if let Some(max_pct) = limits.max_fork_pct_per_branch {
    let branch_count = /* 该分支点的 fork 数 */;
    let total = task_state.limits_state.total_forks();
    let delay = limits.max_fork_pct_check_delay.unwrap_or(0);
    // 热身期之后才检查百分比
    if total > delay && (branch_count as f64) > (total as f64) * max_pct {
        match limits.on_limit_reached {
            LimitBehavior::Truncate => {
                return Err(ExecError::BranchLimitReached(frame.function_name, frame.pc))
            }
            LimitBehavior::Concretize => { /* ... */ }
        }
    }
}
```

**热身机制**（`max_fork_pct_check_delay`）：

在全局 fork 总数未达到 `check_delay` 之前，跳过百分比检查。这避免了初始阶段 `total_forks` 过小导致任何分支点占比都接近 100% 而误杀。

例如，配置 `max_fork_pct_check_delay=100` 表示前 100 次 fork 无论占比如何都不做百分比限制。

### 3.6 未受 ExecutionLimits 约束的 Fork 来源

上述三道 Fork 防线（3.3-3.5）只覆盖了 `Instr::Jump` 中的符号分支 fork。仓库中还存在另一个 fork 来源——`Instr::Monomorphize`（`executor.rs:1533-1650`）。

Monomorphize 指令用于将符号化的 bitvector/bool 值通过 SMT 求解器枚举所有可能值并 case split（即 fork）。它产生的 fork **不经过 ExecutionLimits 的限制检查**，因为它走的是完全不同的代码路径。

这意味着如果 ISA 模型中大量使用 monomorphize 操作，当前的 ExecutionLimits 无法控制由此产生的路径爆炸。这是一个已知的覆盖盲区。

---

## 4. 触发行为策略

当任一防线触发时，系统根据 `on_limit_reached` 配置选择行为：

### 4.1 Truncate（截断）

直接终止当前路径的执行，返回对应的错误。

```rust
ExecError::DepthLimitReached           // 路径深度超限
ExecError::LoopLimitReached(name, pc)  // 循环回边超限
ExecError::BranchLimitReached(name, pc) // 分支 fork 超限
```

上层调用者负责处理这些错误，通常会丢弃该路径或记录为执行失败。

### 4.2 Concretize（具体化）

不终止执行，而是通过 SMT 求解器将符号化的分支条件**具体化为一个确定的布尔值**，选择其中一条路径继续执行。

```rust
// executor.rs:1008-1028
fn concretize_branch_condition<B: BV>(
    v: Sym,                    // 符号变量
    solver: &mut Solver<B>,    // SMT 求解器
    info: SourceLoc,
) -> Result<bool, ExecError> {
    // 1. 查询符号变量是否可以为 true
    let can_be_true = solver.check_sat_with(&Var(v), info).is_sat()?;

    // 2. 如果可以为 true，从模型中提取具体值
    let concrete_val = if can_be_true {
        let mut model = Model::new(solver);
        match model.get_var(v) {
            Ok(ModelVal::Exp(Bool(b))) => b,  // 使用模型中的值
            Ok(ModelVal::Arbitrary(_)) => true, // 任意值时默认 true
            _ => true,
        }
    } else {
        false
    };

    // 3. 将具体值作为约束添加到求解器（锁定选择）
    solver.add(Assert(Eq(Box::new(Bool(concrete_val)), Box::new(Var(v)))));

    Ok(concrete_val)
}
```

**Concretize 的关键性质**：
- **不是"猜一个值"**，而是先通过 SMT 证明当前分支至少有一侧可行（`check_sat`），再把该侧约束写回 solver（`solver.add(Assert(...))`）
- 保证**约束一致性**：具体化后的约束与已有约束不矛盾，执行路径始终处于可行状态
- 不保证**完备性**：具体化只选择了一条路径，可能遗漏其他可行路径
- 具体化后，该路径条件被记录在 `frame.branch_conditions` 中，保证执行轨迹可追溯
- 本质是把 fork 变成**单路径推进**，同时保持约束一致性

### 4.3 Truncate-only 的场景

对于 `Instr::Goto`（无条件跳转）和 `Instr::Call` 中的路径深度检查，即使配置了 Concretize 也只能 Truncate，因为：

- Goto 没有分支条件符号变量可供具体化
- Call 的深度检查发生在函数调用之前，没有分支条件

```rust
// executor.rs:1303 注释
// Goto 是无条件跳转，没有分支条件可供具体化，因此即使配置了 Concretize 也只能 Truncate
```

---

## 5. 限制检查的执行时序

在 `Instr::Jump` 处理中，两层检查的执行顺序如下：

```
Instr::Jump(exp, target, info)
│
│  ── 预评估层（分支条件评估之前）──
│
├── 1. step_count++ → 检查 max_path_depth
│       └── 触发 → Concretize 或 Truncate
│
├── 2. 检查 max_backjumps_per_loop（仅 target <= pc 时）
│       └── 触发 → Concretize 或 Truncate
│
│  ── Fork 层（确认符号分支两路都可满足之后）──
│
├── 3. 评估 exp → 得到值（Symbolic 或 Bool）
│       └── 如果是 Symbolic 且两路都可满足（can_be_true && can_be_false）：
│           │
│           ├── 3a. 检查 max_total_forks（frame.forks >= max_total?）
│           │       └── 触发 → Concretize 或 Truncate
│           │
│           ├── 3b. 检查 max_forks_per_branch（该分支点 fork 数 > max?）
│           │       └── 触发 → Concretize 或 Truncate
│           │
│           ├── 3c. 检查 max_fork_pct_per_branch（占比 > pct?）
│           │       └── 触发 → Concretize 或 Truncate
│           │
│           └── 全部通过 → 正常 Fork（创建子任务入队列）
│               ├── checkpoint(solver) 保存 SMT 状态
│               ├── freeze_frame(frame) 冻结当前帧
│               ├── 子任务：pc=pc+1, 断言 test_false, 入队
│               └── 当前路径：断言 test_true, pc=target
│
└── 如果是 Bool → 直接跳转，不触发任何限制
```

**短路语义**：前面的检查如果触发了限制，后续检查不再执行。优先级为：路径深度 > 循环回边 > 全局 fork > 单分支 fork > 百分比。

---

## 6. 状态追踪机制

### 6.1 帧本地状态（Frame-local）

以下计数器存储在 `Frame` / `LocalFrame` 中，每条执行路径独立维护：

| 字段 | 类型 | 含义 |
|------|------|------|
| `step_count` | `u32` | 当前路径已执行的 Jump/Goto/Call 指令数 |
| `forks` | `u32` | 当前路径上产生的 fork 总数 |
| `loop_counts` | `HashMap<usize, u32>` | 每个 PC 位置的循环回跳次数 |
| `branch_conditions` | `Vec<Exp<Sym>>` | 路径上积累的分支条件（含 concretize 选择） |
| `pc_counts` | `HashMap<B, usize>` | 每个架构 PC 的出现次数（用于 `pc_limit`） |

**Frame 继承语义**：`freeze_frame` / `unfreeze_frame` 会把 `step_count` 和 `loop_counts` 一起拷贝到子帧中。因此 fork 之后，子路径**不会丢失**父路径已经累计的限制信息。这意味着限制阈值是相对于**整条执行路径**（从根任务到当前节点）计算的，而非从 fork 点重新开始。

### 6.2 全局共享状态（Shared）

`ExecutionLimitsState` 通过 `Arc<Mutex<...>>` 和 `AtomicU32` 在所有执行任务间共享：

| 字段 | 类型 | 含义 |
|------|------|------|
| `branch_fork_counts` | `Arc<Mutex<HashMap<(Name, usize), u32>>>` | 每个 `(函数名, PC)` 位置的累计 fork 数 |
| `total_forks` | `AtomicU32` | 全局 fork 总计数 |

```rust
// task.rs:155-161
pub fn increment_branch_fork(&self, function_name: Name, pc: usize) -> u32 {
    let mut counts = self.branch_fork_counts.lock().unwrap();
    let count = counts.entry((function_name, pc)).or_insert(0);
    *count += 1;
    self.total_forks.fetch_add(1, Ordering::Relaxed);
    *count
}
```

**线程安全**：
- `branch_fork_counts` 使用 `Mutex` 保护，确保并发任务间的计数一致性
- `total_forks` 使用 `AtomicU32`，提供无锁的原子递增
- 在多线程执行模式（`start_multi`）下，这些共享状态确保跨任务的限制检查是准确的

### 6.3 路径份额（Fraction）

除了计数限制外，每个 Task 还携带一个 `Fraction`（`isla-lib/src/fraction.rs`），表示该任务占总体工作的比例份额：

- 每次 fork 时，当前路径的 Fraction 调用 `halve()`（分母幂次 +1）
- 多线程调度器（`start_multi`）使用 Fraction 来决定工作窃取（work stealing）的优先级
- Fraction 本身不参与限制检查，但它是路径数量增长的间接指标——当大量 fork 发生后，每个任务的 Fraction 变得很小

---

## 7. `pc_limit`：独立的架构级 PC 限制

除了 `ExecutionLimits`，Isla 还有一套独立的 `pc_limit` 机制，用于 litmus 测试场景。

### 7.1 机制

`pc_limit` 限制的是**架构级程序计数器**（即 ISA 的 PC 寄存器，如 RISC-V 的 `pc`），而非 IR 级别的 PC。它在 `INSTR_ANNOUNCE` 指令（`executor.rs:966-988`）处理中检查：

```rust
// executor.rs:969-988
if let Some((arch_pc, limit)) = task_state.pc_limit {
    if let Some(reg) = frame.local_state.regs.get(arch_pc, shared_state, solver, info)? {
        match reg {
            Val::Bits(bv) => {
                let count = frame.pc_counts.entry(*bv).or_insert(0);
                *count += 1;
                if *count > limit {
                    return Err(ExecError::PCLimitReached(bv.lower_u64()));
                }
            }
            _ => { /* 符号 PC 不支持 */ }
        }
    }
}
```

### 7.2 与 ExecutionLimits 的区别

| 维度 | `pc_limit` | `ExecutionLimits` |
|------|-----------|-------------------|
| 作用层级 | 架构级 ISA PC（指令地址） | IR 级别（指令内部的控制流） |
| 检查时机 | 指令 announce 时 | Jump/Goto/Call 指令执行时 |
| 用途 | 限制同一指令地址的重复执行 | 限制符号分支/循环/路径深度 |
| 超限行为 | `PCLimitMode::Error`（报错）或 `PCLimitMode::Discard`（丢弃 trace） | `Truncate` 或 `Concretize` |
| 配置方式 | `TaskState::with_pc_limit(pc, limit)` | `TaskState::with_execution_limits(limits)` |
| 使用场景 | `isla-axiomatic` litmus 测试 | `isarch` 指令分析 |

### 7.3 CLI 参数

在 `isla-axiomatic` 中通过命令行参数配置：

```
--pc-limit <n>           限制同一 PC 值出现的次数
--pc-limit-mode <mode>   超限处理方式：error（默认）或 discard
```

源码位置：`src/axiomatic.rs:320-329`，`isla-axiomatic/src/run_litmus.rs:138-141,293-294,366-368`

---

## 8. 使用示例

### 8.1 isarch 中的配置

`src/isarch/exec.rs:289-310` 展示了实际使用中的配置：

```rust
let limits = ExecutionLimits::default()
    .with_max_forks_per_branch(2)         // 单分支点最多 fork 2 次
    .with_max_total_forks(8)              // 全局最多 8 次 fork
    .with_max_backjumps_per_loop(10)      // 循环最多回跳 10 次
    .with_max_path_depth(10000)           // 路径深度上限 10000 步
    .with_max_fork_pct_per_branch(0.1)    // 单分支占比不超过 10%
    .with_max_fork_pct_check_delay(100)   // 前 100 次 fork 跳过百分比检查
    .with_limit_behavior(LimitBehavior::Concretize);  // 触发时具体化

let task_state = TaskState::new().with_execution_limits(limits);
```

**配置方式说明**：`ExecutionLimits` 当前是在代码中硬编码的，不像 `timeout`、`memory` 等参数那样通过 TOML 配置文件设置。限制策略不是写死在执行器内部，而是由上层按任务显式开启——同一个 executor 可以在不同场景下复用不同策略。

### 8.2 isla-axiomatic 中的 pc_limit 使用

`isla-axiomatic/src/run_litmus.rs:293-294`：

```rust
if let Some(limit) = opts.pc_limit {
    task_state.with_pc_limit(isa_config.pc, limit)
}
```

### 8.3 测试用例验证

`isla-lib/src/executor.rs:3183-3312` 包含完整的限制策略测试：

**循环限制测试**：
```rust
#[test]
fn loop_limit_reports_error_after_max_backjumps() {
    let limits = ExecutionLimits::default().with_max_backjumps_per_loop(2);
    let result = run_with_limits(vec![Instr::Goto(0)], limits);  // 无限循环
    match result {
        Err(ExecError::LoopLimitReached(function, pc)) => { /* 通过 */ }
        _ => panic!("期望循环限制错误"),
    }
}
```

**串行链检测测试**（验证 `max_total_forks` 能捕获串行 if-else 链，而 `max_forks_per_branch` 不能）：
```rust
#[test]
fn total_fork_limit_truncates_serial_if_else_chain() {
    let (instrs, shared_state) = repeated_call_fork_program(5);  // 5 个连续分支
    let limits = ExecutionLimits::default()
        .with_max_forks_per_branch(100)   // 单点限制宽松
        .with_max_total_forks(2);         // 全局限制严格
    let results = run_all_with_shared_state(instrs, limits, shared_state);
    // 验证触发了 BranchLimitReached
}

#[test]
fn real_ir_per_branch_cannot_detect_serial_chain() {
    // 反例：只用 max_forks_per_branch=2 无法检测串行链
    // 因为每个分支点只 fork 一次，均不超限
    let limits = ExecutionLimits::default().with_max_forks_per_branch(2);
    let results = run_all_with_bindings(instrs, limits, shared_state, regs, lets);
    assert!(results.iter().all(Result::is_ok));  // 全部通过，未触发限制
}
```

**Concretize 行为测试**（验证触发限制后具体化能正常完成）：
```rust
#[test]
fn branch_limit_concretize_finishes_without_error() {
    let limits = ExecutionLimits::default()
        .with_max_forks_per_branch(2)
        .with_limit_behavior(LimitBehavior::Concretize);
    let (instrs, shared_state) = repeated_call_fork_program(5);
    let results = run_all_with_shared_state(instrs, limits, shared_state);
    // 所有路径正常完成，无错误
    assert!(results.iter().all(Result::is_ok));
}
```

测试的重点不是"有没有报错"，而是确认限制命中后，执行路径会按照设计进入 Truncate 或 Concretize。

---

## 9. 与 KLEE 的对比

| 特性 | KLEE | Isla |
|------|------|------|
| 全局 fork 限制 | `max-forks` | `max_total_forks` |
| 单指令 fork 限制 | `max-static-fork` | `max_forks_per_branch` |
| 自适应百分比限制 | `max-static-fork-pct` | `max_fork_pct_per_branch` |
| 百分比检查延迟 | `max-static-fork-pct-check-delay` | `max_fork_pct_check_delay` |
| 循环限制 | 通过 `max-instruction-time` 间接实现 | `max_backjumps_per_loop`（显式回边检测） |
| 路径深度限制 | 无直接对应 | `max_path_depth` |
| 架构 PC 限制 | 无直接对应 | `pc_limit`（独立机制） |
| 超限行为 | 仅截断 | Truncate 或 Concretize |
| 符号条件具体化 | 无 | 通过 SMT 模型提取可行值 |

Isla 的 Concretize 行为是其独特之处：当限制触发时，它不直接终止路径，而是利用 SMT 求解器找到一个可行的具体值来替换符号条件，让执行沿着单条路径继续进行。这在 ISA 语义分析场景中特别有用，因为它保证了每个被分析的指令至少能产生一个有效的执行结果。

---

## 10. 设计取舍

1. **牺牲完备性换取可行性**：Concretize 保证约束一致性（不引入矛盾），但不保证完备性（可能遗漏路径）。这在 ISA 分析场景中是可接受的——获得一个有效结果远比获得所有可能结果更重要。

2. **多维度限制互补**：`max_total_forks` 擅长捕获串行 if-else 链但无法限制循环内分支，`max_forks_per_branch` 擅长限制循环内热点分支但无法检测串行链。两者必须配合使用。

3. **回边检测的局限**：`target <= pc` 的判定是一种静态近似，对于某些复杂的控制流模式（如 switch 跳表、间接跳转）可能无法准确识别循环。

4. **Goto/Call 的 Truncate-only**：无条件控制流变换缺少符号变量，无法执行 Concretize，这是架构层面的固有限制。

5. **百分比限制的热身期**：`max_fork_pct_check_delay` 避免了冷启动阶段的误杀，但也意味着在热身期内可能产生一些本可避免的 fork。

6. **Monomorphize 不受限**：`Instr::Monomorphize` 产生的 fork 不经过 ExecutionLimits 检查。如果 ISA 模型大量使用 monomorphize，可能导致不可控的路径爆炸。

7. **统计粒度选择**：`branch_fork_counts` 使用 `(function_name, pc)` 作为 key 而非语句文本，确保同一 IR PC 在不同函数里不会互相干扰，但也意味着同一函数内不同调用上下文的同一 PC 会被合并计数。
