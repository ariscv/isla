# Findings & Decisions - 将 run_loop_with_condition 合并到 run_loop

## Requirements
- 将 `run_loop_with_condition` 中的 `branch_conditions` 相关改动合并到 `run_loop` 函数
- 删除 `run_loop_with_condition` 函数

## Research Findings

### 函数位置
- `run_loop`: executor.rs 第 1023-1488 行
- `run_loop_with_condition`: executor.rs 第 1491-1969 行

### 代码差异分析

两个函数的唯一差异在于 `Instr::Jump` 指令的处理逻辑：

#### run_loop (第 1079-1104 行)
```rust
if can_be_true && can_be_false {
    ...
    let point = checkpoint(solver);
    let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(frame) };
    ...
    solver.add(Assert(test_true));
    frame.pc = *target
}
```

#### run_loop_with_condition (第 1547-1585 行)
```rust
if can_be_true && can_be_false {
    ...
    let point = checkpoint(solver);

    // 为 fork 路径创建条件列表
    let mut fork_conditions = frame.branch_conditions.clone();
    fork_conditions.push(test_false.clone());

    let frozen = Frame {
        pc: frame.pc + 1,
        branch_conditions: fork_conditions,
        ..freeze_frame(frame)
    };
    ...
    solver.add(Assert(test_true.clone()));  // 注意：使用 clone()

    // 当前路径的条件
    frame.branch_conditions.push(test_true);

    frame.pc = *target
}
```

### 需要合并的改动

| 位置 | run_loop | run_loop_with_condition |
|------|----------|-------------------------|
| 第 1086 行 | `let frozen = Frame { pc: frame.pc + 1, ..freeze_frame(frame) };` | 添加 `branch_conditions: fork_conditions` 字段 |
| 第 1103 行 | `solver.add(Assert(test_true));` | `solver.add(Assert(test_true.clone()));` |
| 第 1085-1086 行之间 | - | 添加 fork_conditions 克隆逻辑 |
| 第 1103 行之后 | - | 添加 `frame.branch_conditions.push(test_true);` |

### 检查是否有其他差异
通过逐行对比，除上述 Jump 指令处理的差异外，两个函数的其他部分完全相同。

## Technical Decisions
| Decision | Rationale |
|----------|-----------|
| 直接替换 run_loop 中的 Jump 逻辑 | 保持代码结构一致，最小化改动范围 |

## Issues Encountered
| Issue | Resolution |
|-------|------------|
| | |

## Resources
- 文件路径: `isla-lib/src/executor.rs`
- run_loop: 第 1023-1488 行
- run_loop_with_condition: 第 1491-1969 行

---
*Update this file after every 2 view/browser/search operations*
*This prevents visual information from being lost*
