# isarch CLI 规范

## 概述

`isarch` 是 RISC-V 指令符号执行探索工具，通过子命令模式组织功能。

## 用法

```
isarch [全局选项] <子命令> [子命令参数]
```

## 全局选项

| 选项 | 说明 |
|------|------|
| `-A/--arch <file>` | 架构 IR 文件路径（必需） |
| `-C/--config <file>` | ISA 配置文件路径 |
| `-T/--threads <n>` | 工作线程数 |
| `-R/--register <name>=<value>` | 寄存器初始化 |
| `-I/--initial <name>=<value>` | 初始状态寄存器 |
| `-D/--debug <flags>` | 调试标志。`f`=FORK，`m`=MEMORY，`l`=LITMUS，`g`=GRAPH，`p`=PROBE，`c`=CACHE，`s`=SYM_EXEC，`r`=PATH_RESULT，`a`=ARCH_INFO |
| `--no-model-reg-init` | 跳过寄存器初始化 |
| `--verbose` | 详细输出 |
| `--init-isa-with-config` | 使用配置默认值初始化 ISA |
| `-g/--graphviz` | Graphviz 输出格式（tree 命令） |
| `--timeout <n>` | 超时时间（秒） |

## 子命令

### `list-instructions`

列出架构中所有可用指令。

```
isarch -A <ir> -C <config> list-instructions
```

输出格式：

```
共 N 个 clause，M 条指令：

  [CLAUSE_NAME] asm1, asm2, ...
  [CLAUSE_NAME] (无汇编名称)
```

- clause 名称使用 `zencode::decode` 解码后的原始名称（如 `ADDIW` 而非 `zADDIW`）
- 每个 clause 的助记符按字母序排列
- 无助记符的 clause 显示 `(无汇编名称)`

退出码：0 成功，1 失败。

### `tree <instruction>`

显示指定指令的执行路径树。

```
isarch -A <ir> -C <config> tree <instruction>
isarch -A <ir> -C <config> -g tree <instruction>  # Graphviz DOT 输出
```

- `<instruction>`：指令名称（必需）
- `-g`：生成 Graphviz DOT 格式输出到 `out/` 目录

退出码：0 成功，1 缺少参数或执行失败。

### `debug-instruction [<clause>]`

调试指令汇编名称列举功能。替代原 `--features debug_instruction` + `test_instruction_list_main`。

```
isarch -A <ir> -C <config> debug-instruction
isarch -A <ir> -C <config> debug-instruction zRTYPE
```

- `<clause>`：可选，clause 构造子名称（默认 `zRTYPE`）

输出：列举指定 clause 的所有汇编名称，通过日志输出。

退出码：0 成功。

### `debug-clause-args [<clause>]`

调试 clause 参数提取功能。替代原 `--features debug_clause_args` + `test_clause_args_main`。

```
isarch -A <ir> -C <config> debug-clause-args
isarch -A <ir> -C <config> debug-clause-args zSTORE
```

- `<clause>`：可选，clause 构造子名称（默认行为：先测试 zRTYPE 的符号化参数，再测试 zSTORE 的 InstructionMap）

输出：符号化参数和 InstructionMap 信息，通过日志输出。

退出码：0 成功。

### `debug-clause-args-yaml`

导出所有指令 clause 参数为 YAML 文件。替代原 `--features debug_clause_args_yaml` + `test_clause_args_yaml_main`。

```
isarch -A <ir> -C <config> debug-clause-args-yaml
```

输出：在 `profiles/riscv/` 目录下为每个 clause 生成 `args_<clause>.yaml` 文件。

退出码：0 成功。

## 退出码

| 码 | 含义 |
|----|------|
| 0  | 成功 |
| 1  | 错误（参数缺失、未知子命令、执行失败等） |

## 错误处理

- 无子命令：打印用法信息，退出码 1
- 未知子命令：打印错误信息和用法，退出码 1
- `tree` 缺少必需参数：打印错误信息，退出码 1

## 废弃的 Feature Flags

以下 feature flags 在重构后被子命令替代，不再需要：

- `debug_instruction` → `debug-instruction` 子命令
- `debug_clause_args` → `debug-clause-args` 子命令
- `debug_clause_args_yaml` → `debug-clause-args-yaml` 子命令

## 集成测试

### 目录结构

```
test/isarch/cli/
├── test_isarch_cli.sh                  # 测试入口脚本（编排所有子命令测试）
└── list-instructions/                  # list-instructions 子命令的测试资源
    ├── extract_sail_clauses.py         # 预期结果管理工具
    ├── update_expected.sh              # 从 sail-riscv 更新预期结果
    ├── _bootstrap_data.py              # 一次性引导工具（历史参考）
    ├── expected_data/                  # 预期数据源（按 sail-riscv 扩展组织的 Python 模块）
    │   ├── __init__.py                 #   聚合所有模块，提供 get_all_instructions()
    │   ├── i.py                        #   I 扩展（20 clauses）
    │   ├── m.py                        #   M 扩展
    │   └── ...                         #   其他扩展模块
    └── expected/                       # 生成的预期结果文件
        ├── clause_names.txt            #   clause 名称列表
        ├── assembly_names.txt          #   clause → 助记符映射
        └── summary.txt                #   汇总统计
```

### 预期数据管理

预期数据以 Python 模块形式硬编码在 `expected_data/` 中，按 sail-riscv 的扩展目录组织。每个模块定义 `INSTRUCTIONS` 字典：

```python
# expected_data/i.py
INSTRUCTIONS = {
    "RTYPE": ["add", "and", "or", "sll", "slt", "sltu", "sra", "srl", "sub", "xor"],
    "LOAD": ["lb", "lbu", "ld", "ldu", "lh", "lhu", "lw", "lwu"],
    ...
}
```

`__init__.py` 聚合所有模块并提供 `get_all_instructions()` 函数，返回合并后的 `{clause_name: [asm_names]}` 字典。

### extract_sail_clauses.py 子命令

#### `generate`

从 `expected_data/` 生成 `expected/*.txt` 文件：

```
python3 extract_sail_clauses.py generate
```

- 读取 `expected_data/` 包中的硬编码数据
- 生成 `clause_names.txt`、`assembly_names.txt`、`summary.txt`

#### `verify <actual_output_file>`

对 isarch `list-instructions` 实际输出做集合比较：

```
python3 extract_sail_clauses.py verify <actual_output_file>
```

验证语义为 **actual ⊆ expected**（实际输出不应超出预期范围），配合显式 allowlist 处理已知差异：

| 场景 | 判定 |
|------|------|
| 实际输出完全为空 | **失败** |
| 实际助记符超出预期范围 | **失败** |
| 实际 clause 不在预期数据中 | **失败** |
| 预期有助记符但实际完全为空（不在 `_ALLOWED_EMPTY_CLAUSES` 中） | **失败** |
| 缺失助记符且不在 allowlist 中 | **失败** |
| 预期 clause 在实际输出中不存在（不在 allowlist 中） | **失败** |
| 缺失部分助记符但在 `_ALLOWED_PARTIAL_MISSING_CLAUSES` 中 | **info**（允许部分缺失，但必须非空） |
| 预期有助记符但实际完全为空（在 `_ALLOWED_EMPTY_CLAUSES` 中） | **info**（IR 无法解析任何助记符） |
| 预期 clause 在实际输出中不存在（在 allowlist 中） | **info**（可能被配置过滤） |

##### Allowlist 说明

`expected_data` 来自 sail-riscv 笛卡尔积解析，是助记符的上界；CLI 实际输出经 IR 合法性过滤是子集。allowlist 记录两类已知差异：

**`_ALLOWED_PARTIAL_MISSING_CLAUSES`** — 允许部分助记符缺失，但必须至少命中一个：

```
AMO, LOAD, STORE, LOADRES, STORECON, LOAD_FP, STORE_FP,
DIV, DIVW, MUL, REM, REMW,
VLRETYPE, VLSEGFFTYPE, VLSEGTYPE, VLSSEGTYPE, VLXSEGTYPE,
VMVRTYPE, VSRETYPE, VSSEGTYPE, VSSSEGTYPE, VSXSEGTYPE,
ZBA_RTYPEUW, ZCMOP, ZIMOP_MOP_R, ZIMOP_MOP_RR
```

原因：sail 笛卡尔积生成的组合多于 IR 合法性过滤后的实际输出。例如 LOAD 在 sail 中生成 lb/lbu/ld/ldu/lh/lhu/lw/lwu，但 CLI 只输出 ld。

**`_ALLOWED_EMPTY_CLAUSES`** — 允许完全无输出（CLI 显示"无汇编名称"）：

```
ZBA_RTYPE,
C_ADD, C_ADDI, C_ADDI16SP, C_ADDI4SPN,
C_FLW, C_FLWSP, C_FSW, C_FSWSP,
C_JAL, C_JALR, C_JR, C_LDSP, C_LUI, C_LWSP, C_MV
```

原因：这些 clause 的助记符解析需要 IR 不支持的上下文信息，导致无法枚举任何助记符。

退出码：0 验证通过，1 验证失败。

#### `update-from-sail <sail_riscv_dir>`

从 sail-riscv 源码解析并重新生成 `expected_data/` Python 模块：

```
python3 extract_sail_clauses.py update-from-sail <sail_riscv_dir>
```

- 扫描 `<sail_riscv_dir>/model/` 下所有 `.sail` 文件
- 提取 `union clause instruction` 定义获取 clause 名称
- 解析 `mapping clause assembly` 获取助记符表达式
- 对表达式求值（支持 `mapping` 函数查找、`dec_bits_N` 计算、`^` 拼接的笛卡尔积）
- 排除非指令 clause（`STOP_FETCHING`、`THREAD_START`）
- 按扩展目录分组生成 Python 模块

如果有表达式无法解析，脚本以退出码 1 失败并报告所有未解析的表达式，避免静默覆盖既有数据。

### update_expected.sh

从 sail-riscv 目录更新预期结果的入口脚本：

```
./update_expected.sh [sail_riscv_dir]
```

执行两步：
1. `extract_sail_clauses.py update-from-sail` — 从 sail-riscv 源码重新生成 `expected_data/`
2. `extract_sail_clauses.py generate` — 从 `expected_data/` 生成 `expected/*.txt`

### 测试用例

`test_isarch_cli.sh` 中的 `list-instructions` 相关测试：

| 测试 | 说明 |
|------|------|
| `t_list_instructions` | 基本退出码检查 |
| `t_list_instructions_clause_count` | clause 数量不低于预期 |
| `t_list_instructions_key_clauses` | 关键 clause（RTYPE, ITYPE, BTYPE 等）必须存在 |
| `t_list_instructions_assembly_names` | 调用 `extract_sail_clauses.py verify` 做集合级比较 |

### 数据流

```
sail-riscv/model/*.sail
        │
        ▼  update-from-sail
expected_data/*.py (INSTRUCTIONS 字典)
        │
        ▼  generate
expected/*.txt (clause_names.txt, assembly_names.txt)
        │
        ▼  verify
isarch list-instructions 实际输出
```

### 设计决策

1. **硬编码而非运行时解析**：expected_data 硬编码在 Python 模块中，避免运行时解析 sail 文件的脆弱性（guard 约束、笛卡尔积过度膨胀等问题）
2. **actual ⊆ expected 语义**：expected_data 来自 sail-riscv 的笛卡尔积解析，是助记符的上界；CLI 实际输出经 IR 合法性过滤是子集，因此验证只检查实际输出不超出预期范围
3. **zencode 解码**：`list_instructions` 输出时对 clause 名做 `zencode::decode`，使输出与 sail-riscv 源码中的原始名称一致（如 `ADDIW` 而非 `zADDIW`）
4. **按扩展目录组织**：expected_data 按 sail-riscv 的扩展目录分模块，便于增量更新和 review

### `fuzz`

与 `solve-state` 共用全部探索参数、指令与前态设置。每个进程针对一个场景，先用当前模型完整认证 corpus，再用常驻快档判定 mutant。

```sh
isarch [原 J1 探索参数] \
  --fuzz-mode judge-only --fuzz-scenario <场景配置id> \
  --fuzz-corpus <samples.jsonl> --fuzz-inputs <mutants.jsonl> \
  --fuzz-output <绝对路径的新目录> fuzz --clause <指令>
```

回放 P1b 使用 `--fuzz-mode replay-log --fuzz-mutations <mutations.json>`；原始输入从同目录 `judge-batches.json` 定位，也可用 `--fuzz-inputs` 显式指定。`--fuzz-seed` 指定随机数初值（默认 0），`--fuzz-batch-size` 指定批量大小（默认 256）。默认使用模型执行器；`campaign --executor difftest` 连接 emu 和独立 NEMU。

路径引导使用 `--fuzz-mode campaign --fuzz-budget 2000`。形态 A 固定父类，在活动输入字段的 8 位切片中换满足约束的值；形态 B 在同一条完成路径的规范向量目录中选择距离近、命中少的类，仅放开差异守卫及关联约束涉及的位。默认 5% 对照从 `--fuzz-mutations` 与原始输入构成的 replay-log 记录池抽样，统一在 A/B 之后生成；不提供对照池时显式设 `--fuzz-control-percent 0`。普通 campaign 只对新增类的 corpus 候选做认证；验收使用 `--fuzz-certify-all` 对全部接纳输入做两档逐字段比较。

生成遵循 `-T`，每个目标类的排重历史按编号处理；批内先预约目标，输出与线程完成顺序无关。普通 `--executor model` 不连接硬件。`--executor difftest` 对要送硬件的输入先做完整认证，再提交有界 worker 池；默认 `--difftest-workers 8`，允许 1 到 12，单例 `--difftest-timeout 120` 秒，允许 1 到 600。Python worker 外层额外保留 30 秒用于构建与清理。支持 SIGINT/SIGTERM 取消、整进程组及独立子会话清理。

`--difftest-worker/profile/lock/files/observer` 分别指定 Python 入口、平台描述、平台锁、工具路径 JSON 和独立 NEMU 观察器。默认入口是当前仓库的 `tools/fuzz/paging_worker.py`；外部只读目录由 `DIFFTEST_XIANGSHAN_DIR` 选择，默认来源与 [第 4 步记录](../agents/path_merge_call_support/fuzz-step4.md) 一致。`PT_DECODE_DIR` 选择既有解码器。平台锁只记录 isarch 身份，样本有效性由当前模型认证决定。

闭环额外输出 `difftest-results.jsonl`、`findings.jsonl`、`findings-summary.json`，每个输入的 ELF、原始日志和结构化 `result.json` 位于 `difftest/input-编号/`。保留原始不一致数量，再统计窄规则 `R-XS-001` 命中数；未过滤分歧只记录，不自动认定为缺陷。分组依据为目标类、不同字段和阶段，反馈仍只观察。

所有 fuzz 模式都将路径 DAG 写到 `dag/`，重读检查结果写到 `dag-manifest.json`。格式见 [DAG 导出](../agents/path_merge_call_support/fuzz-dag-export.md)，本轮实验与限制见 [第 3 步记录](../agents/path_merge_call_support/fuzz-step3.md)。

输出 `judged.jsonl` 为 judged v1，`classified.jsonl` 为完整 samples v1；类目录、变异记录、认证、覆盖和统计另存。旧缺 `fcsr` 的 P1b 输入通过 replay-log 从父 corpus entry 补齐并审计。完整命令、文件说明与四场景验收见 [第 2 步记录](../agents/path_merge_call_support/fuzz-step2.md)，也可运行 `isarch fuzz --help`。
