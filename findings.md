# 研究发现

## 项目概述
Isla 是一个用 Rust 编写的 Sail RISC-V 符号执行引擎，用于对 Sail 定义的指令集架构进行形式化验证和分析。

## 关键发现

### 1. IR 文件结构
- **位置**: `rv32d.ir` / `rv64d.ir`（项目根目录）
- **格式**: Sail 编译器生成的中间表示
- **结构**: goto/条件分支语言
- **关键函数**:
  - `zexecute(zmergez3var)`: 指令执行分派函数（第 243762 行）
  - `zassembly_forwards()`: 指令汇编名称映射（第 289038 行）

### 2. 指令编码机制
- **文件**: `isla-lib/src/zencode.rs`
- **编码规则**:
  - Sail 名称 → C 标识符格式
  - `z` 前缀 + 编码内容
  - 字母 `z` → `zz`
  - 其他非标识符字符 → `zX` 格式
- **示例**: "MRET" → "zMRET"

### 3. 符号执行引擎
- **文件**: `isla-lib/src/executor.rs`
- **核心结构**:
  - `Frame`: 执行栈帧
  - `Task`: 执行任务
  - `SharedState`: 共享状态
- **功能**:
  - 多线程路径探索
  - 符号变量初始化
  - 约束条件收集
  - 路径分支处理

### 4. Z3 集成
- **文件**: `isla-lib/src/smt.rs`
- **关键类型**:
  - `Sym`: 符号变量
  - `Solver`: SMT 求解器接口
  - `Event`: 执行事件
- **功能**:
  - 符号变量创建
  - 约束构建
  - 模型查询
  - 检查点和恢复

### 5. 现有 CLI 工具
- `isla-execute-function`: 执行指定函数
- `zencode`: 编码/解码工具
- `isla-property`: 属性验证
- `isla-axiomatic`: 内存模型测试（包含图可视化功能）

### 6. MRET 指令在 IR 中的表示
- **Sail 内部名**: `MRET`（编码为 `zMRET`）
- **汇编名**: `mret`
- **执行入口**: `zexecute` 函数中的 `jump zmergez3var is zMRET goto 1358`
- **执行路径**:
  1. 检查 `cur_privilege != Machine` → `Illegal_Instruction()`
  2. 检查 `not(ext_check_xret_priv(Machine))` → `Ext_XRET_Priv_Failure()`
  3. 正常执行 → `exception_handler` + `set_next_pc` + `RETIRE_SUCCESS`

### 7. 可复用的基础设施
- 图可视化: `isla_axiomatic::graph::{draw_graph_ascii, draw_graph_gv}`
- IR 解析: `ir_parser` + `ir_lexer`
- 配置系统: `config.rs` + TOML 文件
- 约束求解: `smt.rs` + Z3

## 技术挑战

### 1. 路径跟踪
- 需要在符号执行过程中跟踪每条路径的条件
- 需要识别分支点和合并点
- 需要构建树状路径结构

### 2. 条件提取
- 需要从 IR 的条件跳转中提取条件表达式
- 需要将 IR 表达式转换为人类可读的形式
- 需要处理复杂的嵌套条件

### 3. ISA 状态表示
- 需要定义完整的 ISA 状态结构
- 需要处理符号变量和具体值
- 需要支持默认值和约束值

### 4. Z3 求解
- 需要构建正确的约束
- 需要处理不可满足的约束
- 需要格式化求解结果

## 下一步
1. 阅读关键源代码文件以深入理解实现细节
2. 设计指令识别和路径跟踪机制
3. 设计输出格式和求解接口
