# Task Plan: 将 run_loop_with_condition 的改动合并到 run_loop

## Goal
将 `run_loop_with_condition` 函数中的 `branch_conditions` 相关改动合并到 `run_loop` 函数中，然后删除 `run_loop_with_condition` 函数。

## Current Phase
Complete

## Phases

### Phase 1: 分析两个函数的差异
- [x] 读取 run_loop 函数完整代码
- [x] 读取 run_loop_with_condition 函数完整代码
- [x] 识别 branch_conditions 相关的改动
- [x] 列出所有需要合并的改动点
- **Status:** complete

### Phase 2: 合并改动到 run_loop
- [x] 修改 run_loop 函数的 Jump 指令处理
- [x] 添加 branch_conditions 的克隆逻辑
- [x] 添加 test_true 和 test_false 的 clone 调用
- [x] 添加当前路径的条件收集
- **Status:** complete

### Phase 3: 删除 run_loop_with_condition 函数
- [x] 删除 run_loop_with_condition 函数定义
- [x] 验证没有其他代码引用该函数
- **Status:** complete

### Phase 4: 编译验证
- [x] 编译项目验证语法正确
- [x] 运行相关测试
- **Status:** complete

## Key Questions
1. run_loop_with_condition 是否被其他代码调用？✅ 否，没有调用者
2. 除了 Jump 指令处理，两个函数是否还有其他差异？✅ 否，无其他差异

## Decisions Made
| Decision | Rationale |
|----------|-----------|
| 删除 run_loop_with_condition | 避免代码重复，简化维护 |

## Errors Encountered
| Error | Attempt | Resolution |
|-------|---------|------------|
| | | |

## Notes
- run_loop 函数位于 executor.rs 第 1023 行
- branch_conditions 已在之前添加到 LocalFrame 和 Frame 结构体中
- 编译通过，无错误
