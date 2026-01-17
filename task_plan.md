# 任务计划：RISC-V 指令符号执行与路径分析

## 目标
针对 RISC-V 指令（如 mret）实现符号执行，分析不同执行路径需要的 ISA 状态和指令操作数条件，使用 Z3 SMT 求解器求解具体的 ISA 状态值。

## 背景
- 项目：Isla - Sail RISC-V 符号执行引擎
- 输入：编译好的 Sail IR 文件（rv32d.ir / rv64d.ir）
- 目标：对指定指令进行符号执行，收集路径条件和 ISA 状态约束
- 输出：树状执行路径、人类可读的条件表达式、Z3 求解结果

## 技术栈
- Rust
- Sail IR（中间表示）
- Z3 SMT 求解器
- LALRPOP（IR 解析）

## 关键文件位置

### 源代码
- `isla-lib/src/ir.rs` - IR 类型定义
- `isla-lib/src/ir_parser.lalrpop` - IR 语法解析器
- `isla-lib/src/ir_lexer.rs` - IR 词法分析器
- `isla-lib/src/executor.rs` - 符号执行引擎核心
- `isla-lib/src/smt.rs` - Z3 求解器接口
- `isla-lib/src/zencode.rs` - 名称编码/解码
- `isla-lib/src/config.rs` - 配置处理

### 配置和输入
- `rv32d.ir` - RISC-V 32 位 IR 文件
- `rv64d.ir` - RISC-V 64 位 IR 文件
- `configs/riscv32.toml` - RISC-V 32 位配置

### 现有工具
- `src/execute-function.rs` - 函数执行器
- `src/zencode.rs` - 编码/解码 CLI

## 任务分解

### 阶段 1：理解现有代码
- [x] 探索项目结构
- [x] 理解 IR 解析机制
- [x] 理解符号执行引擎
- [x] 理解 Z3 集成
- [ ] 理解现有 CLI 工具的实现模式

### 阶段 2：设计实现方案
- [ ] 设计指令识别和提取机制
- [ ] 设计符号执行路径跟踪机制
- [ ] 设计条件收集和约束构建机制
- [ ] 设计树状输出格式
- [ ] 设计 Z3 求解和结果格式化

### 阶段 3：实现核心功能
- [ ] 实现指令字典构建
- [ ] 实现路径符号执行和条件收集
- [ ] 实现树状路径打印
- [ ] 实现 Z3 约束求解
- [ ] 实现 ISA 状态值格式化输出

### 阶段 4：测试和验证
- [ ] 测试 mret 指令
- [ ] 测试其他指令（add、sw、lw、sb、lb、ecall）
- [ ] 验证输出格式正确性
- [ ] 验证 Z3 求解结果正确性

## 关键技术点

### 1. 指令识别
- IR 中通过 `zexecute(zmergez3var)` 函数分派到不同指令
- 使用 `zencode::decode()` 解码指令名称（如 "zMRET" → "MRET"）
- 汇编名称通过 `zassembly_forwards()` 函数获取

### 2. 符号执行流程
```
IR 解析 → 创建符号变量 → 执行路径探索 → 收集约束条件 → Z3 求解
```

### 3. 路径分支处理
- 条件跳转（`jump <cond> goto <label>`）
- 分支条件跟踪
- 路径合并点识别

### 4. ISA 状态表示
- 特权级（PRV_M/PRV_S/PRV_U/PRV_HS/PRV_VS）
- 通用寄存器（x0-x31）
- 浮点寄存器
- 向量寄存器
- CSR 寄存器（mstatus、misa、mtvec 等）

## 预期输出格式

### 树状路径输出
```
    mret
     |
   /-----\
  con1       mstatus.MPP=PRV_S
 /    \         /
...  ...      ...
p0   p1        p2

isa状态、指令操作数需要满足的条件：
p0: (非法指令路径)
  cur_privilege != PRV_M

p1: (权限失败路径)
  cur_privilege == PRV_M
  not(ext_check_xret_priv(PRV_M))

p2: (正常返回路径)
  cur_privilege == PRV_M
  ext_check_xret_priv(PRV_M)
  ...
```

### Z3 求解结果输出
```
p2: (正常返回路径)
  priv=PRV_M
  x0=0x00000000
  x1=0x00000000
  ...
  x31=0x00000000
  mstatus=0x00001800 (MPP=PRV_S)
  misa=0x40000100
  mtvec=0x00000000
  ...
```

## 待澄清问题
（将在 Phase 1 后提出）

## 错误记录
| 错误 | 尝试 | 解决方案 |
|-------|------|----------|
| - | - | - |
