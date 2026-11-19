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
| `--execution-limits-config <file>` | 显式加载只有 `[execution_limits]` 的独立 TOML，整体替换 `-C` 的同名表。缺省使用主 ISA 配置。 |
| `-T/--threads <n>` | 工作线程数 |
| `-R/--register <name>=<value>` | 寄存器初始化 |
| `-I/--initial <name>=<value>` | 初始状态寄存器 |
| `-D/--debug <flags>` | 调试标志。`f`=FORK，`m`=MEMORY，`l`=LITMUS，`g`=GRAPH，`p`=PROBE，`c`=CACHE，`s`=SYM_EXEC，`r`=PATH_RESULT，`a`=ARCH_INFO |
| `--no-model-reg-init` | 跳过寄存器初始化 |
| `--verbose` | 详细输出 |
| `--init-isa-with-config` | 使用配置默认值初始化 ISA |
| `-g/--graphviz` | Graphviz 输出格式（tree 命令） |
| `--timeout <n>` | 超时时间（秒） |

isarch 使用实际 IR 检查区域规则。旧 TOML 的 `ir_sha256` 仍可解析，IR 来源可查生成清单或求解摘要。

## 过滤模型异常终态

`solve-state` 与 `fuzz` 可按 Sail 异常构造子名在抛出时结束路径。默认集合为空，行为保持原样。TOML 可放在基础配置或 `--execution-limits-config` 指定的文件中：

```toml
[execution_limits]
filter_model_exceptions = ["Error_internal_error", "Error_reserved_behavior"]
```

对应 CLI 参数可重复：

```sh
isarch -A model.ir -C model.toml \
  --filter-model-exception Error_internal_error \
  --filter-model-exception Error_reserved_behavior \
  solve-state --clause LOAD
```

出现任意 `--filter-model-exception` 时，CLI 集合整体覆盖 TOML 集合。名称按解码后的完整构造子名精确匹配；不依据模型名、源码位置或消息关键词过滤。`Error_not_implemented` 只有显式列入集合才会被过滤。没有环境变量入口。

Sail IR 设置 `have_exception = true` 时执行过滤。普通执行立即结束该路径，区域推演沿用死臂事务，撤销该臂的效应并排除它的到达守卫。配置中的异常在任何捕获或返回之前结束路径。区域只有在静态确认终止调用会到达已过滤的 throw 时才放行该调用。

`[MODEL_EXCEPTION_THROW_FILTER]` 记录现场丢弃的普通路径与推演臂。开启 `--merge-diagnostics summary` 可在诊断快照读到这两个计数，`detail` 还会逐次记录构造子、载荷、throw 与直接调用者的 IR 和 Sail 位置。推演计数包含后来被外层回滚的尝试，普通执行再次到达时另计。

终态收集和旧缓存读回继续按同一个构造子规则处理已有的异常终态。`[MODEL_EXCEPTION_FILTER]` 与摘要的 `filtered-model-exception-paths`、`filtered-model-exception-sites` 保留这部分终态的次数和载荷消息。旧缓存只有原探索实际保存的路径，需重新探索才能应用抛出时策略或恢复已剪路径。

执行错误、超时、未知 Poison、panic 保留原有失败处理；`AssertionFailure` 仍由原有断言逻辑计数。fuzz 仍要求至少一个保留终态，外部 corpus 仍须完整通过认证；若旧 corpus 包含已排除的异常输入，应从保留路径重新生成。

## 过滤 Sail match 失败出口

`[execution_limits].filter_match_failures = true` 可在 Sail IR 的 `exit match` 处结束该路径。缺省关闭，命令行 `--filter-match-failures` 可直接开启。此开关独立于模型异常列表，普通 `exit` 和断言按各自的 IR 类型处理。

区域沿用死臂事务。stderr 的 `[MATCH_FAILURE_FILTER]` 记录现场丢弃的普通路径和推演臂。`--merge-diagnostics summary` 输出计数快照，`detail` 逐次记录 IR 指令位置、Sail 源码位置及直接调用者。

## 枚举符号前态

枚举寄存器可以在同一节配置允许成员：

```toml
[symbolic_registers]
cur_privilege = { allowed = ["User", "Supervisor"] }

[symbolic_registers.mstatus]
pin_mask = "0xfffffffffff3ffff"
pin_value = "0x0000000a00000000"
```

此例让当前特权级在 U/S 中求解，mstatus 仅 SUM[18]、MXR[19] 自由，其余位保持指定值。
`allowed` 也支持 `[symbolic_registers.cur_privilege]` 子表写法；成员名须与 IR 中的 Sail 名称完全一致。
集合为空、重复、成员拼错、成员属于另一枚举、目标不是枚举、与任何位约束混用都会报错。
与 `--prestate` 或 `[registers.defaults]` 同名仍报错，不能用具体默认值为这个寄存器补译码上下文。
使用 `--instruction-bits` 时，独立译码采用允许集合的首项作为具体上下文；需要选择能译出目标指令的首项。
这只服务固定机器字的译码，执行时仍对整个允许集合求解。各执行样本的编码和汇编沿用已有模型检查。
约束沿用 `setup_pre_state` 之后、checkpoint 之前的符号寄存器注入，执行值与输出前态共用同一个符号；没有改 IR。
未使用 `allowed` 的配置保持原有行为。

通用符号探索直接指定 clause，不传固定机器码：

```sh
isarch -A <ir> -C <config> solve-state --clause=LOAD
isarch -A <ir> -C <config> solve-state --clause=STORE
```

`symbolic_args_from_types` 为指令全部字段建立自由符号变量，包括 rs1、rd/rs2、立即数和访问宽度；
`setup_pre_state` 已为 x1–x31 建立独立初态符号，x0 遵循模型的常零语义。
无需额外声明某个通用寄存器，也不传固定通用寄存器的 `--prestate` 或附加地址掩码。
`--instruction-bits` 仍供用户明确要求固定机器码时使用，通用探索脚本不依赖它。
完整 DAG 入口 `solve-state` 缺省尝试自适应区域合并，并启用循环区域分析。`isla-execute-function` 同样采用该缺省。可用 `[execution_limits.path_merge] enabled = false` 或 `--no-path-merging` 关闭。CLI 显式选项覆盖 TOML，局部 `off` 和 `force` 在启用合并时继续生效。fuzz 等通用库入口沿用各自的配置。
通用探索省略分支、路径、回跳、比例及区域额度即不限。只有在有限预算的对照实验中才需要 `branch_limit` 或 `fork_limit`。加载 workaround 时，其中显式设置的额度仍可生效。有限额度触发时，省略 `on_limit_reached` 沿用截断，显式 `concretize` 会保留一个可行方向或当前模型。报告里应记录截断与具体化导致的覆盖收缩。
当符号下标引起算子重试拆分时，默认沿用求解模型的候选顺序。跨进程由完整语义判定对齐。

区域合并默认不设步数预算（-1）。配置正整数后，两臂、调用和普通嵌套区域共同扣步，可按轮折叠的循环独立逐轮续配。
步数用尽只拒绝本次合并尝试，不截断普通执行路径。设置 `-1` 时，以上区域一律不扣步、不会因步数耗尽拒绝；路径限时仍有效。

```toml
[execution_limits]

[execution_limits.path_merge]
enabled = true
step_budget = -1
```

也可使用 `--region-step-budget=-1`，它覆盖 TOML 的 `execution_limits.path_merge.step_budget`。合法值为正整数或 `-1`；`0`、其他负数、非整数均报错。
关闭预算时，`region_progress` 继续统计实际步数，预算耗尽位置 `exhausted` 为 `null`；循环日志中 `steps_since_budget_renewal` 为 `null`，`step_budget_unlimited=true`。

## 慢 SMT 查询导出

默认关闭；用显式 CLI 选项导出已返回的慢查询，不改变查询结果，也不依赖区域合并开关：

```sh
isarch -A <ir> -C <config> --slow-query-dump-dir queries \
  --slow-query-threshold 20s --slow-query-dump-limit 5 solve-state --clause <name>
```

`--slow-query-dump-dir` 开启导出；阈值默认 `20s`，支持正整数秒及 `s/m/h` 后缀；份数上限默认 `5`，必须为正整数。单独传阈值或上限、零值、非法值均报错。每次进程最多配置一次，目录中生成 `query-NNN.smt2` 和同名 JSON；请为不同进程使用各自的输出目录。

SMT2 包含已发布／事务缓冲断言、活动臂条件及临时查询条件，可以离线重放。JSON 记录源位置、结果、solver／Context／线程身份、是否主 solver、检查前后 statistics、断言来源与依赖、展开定义后的共享 DAG／树节点数及导出耗时。树节点数饱和会明确标记，不代表实际分配大小。只记录真正提交给 Z3 且正常返回的检查；缓存命中和中断错误不导出，中断错误仍走已有 timeout SMT 输出。

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

`--path-cache-read <目录> --path-cache-encoding bin` 直接恢复完成路径，跳过符号探索。省略 `--fuzz-corpus` 时，沿用现场枚举器，显式使用 `class_cap=1`、`sample_stride=1`，为每个成功遍历的守卫类生成一个代表。路径上限缺省不限。初始 corpus 写入 `initial-corpus.jsonl`，完整枚举元数据写入 `initial-corpus-enumeration.json`。生成的 corpus 经完整 judge 认证后才进入 loop。提供 `--fuzz-corpus` 时跳过生成，认证并复用指定的 corpus。缓存读取也支持普通 `solve-state` 的样本导出和 `--check-samples`。

路径缓存使用 schema 4，保存 64 位 fork ID、纯原语定义的符号区间 `pure_definitions` 和终态。JSON 和二进制均保存这些字段，可用 `--path-cache-crosscheck` 交叉核对。schema 3 的 JSON 可单独读取，须省略 `--path-cache-crosscheck`。schema 3 二进制及 schema 1/2 需要重新生成。初始 corpus 通过恢复路径的完整 judge 认证，检查其输入与后态，不重新执行当前 IR 的 clause。本轮保持 IR／配置不变；跨 IR／配置的语义兼容仍需独立复验。manifest 的来源哈希只作记录，不是准入门槛。partial 缓存只代表已完成路径，完整性和错误数量以 manifest 为准。

```sh
isarch [原探索参数] \
  --path-cache-read <缓存目录> --path-cache-encoding bin --path-cache-crosscheck \
  --fuzz-mode campaign --fuzz-scenario <场景配置id> \
  --fuzz-budget 50 --fuzz-control-percent 0 \
  --fuzz-output <绝对路径的新目录> fuzz --clause <指令>
```

```sh
isarch [原 J1 探索参数] \
  --fuzz-mode judge-only --fuzz-scenario <场景配置id> \
  --fuzz-corpus <samples.jsonl> --fuzz-inputs <mutants.jsonl> \
  --fuzz-output <绝对路径的新目录> fuzz --clause <指令>
```

回放 P1b 使用 `--fuzz-mode replay-log --fuzz-mutations <mutations.json>`；原始输入从同目录 `judge-batches.json` 定位，也可用 `--fuzz-inputs` 显式指定。`--fuzz-seed` 指定随机数初值（默认 0），`--fuzz-batch-size` 指定批量大小（默认 256）。默认使用模型执行器；`campaign --executor difftest` 连接 emu 和独立 NEMU。

路径引导使用 `--fuzz-mode campaign --fuzz-budget 2000`。形态 A 固定父类，在活动输入字段的 8 位切片中换满足约束的值；形态 B 在同一条完成路径的规范向量目录中选择距离近的类，仅放开差异守卫及关联约束涉及的位。默认 `--fuzz-feedback coverage` 用实际类的 PTE 字段桶及未知不一致签名接纳 corpus entry，并在批次边界更新父输入和目标类的评分；`--fuzz-feedback none` 保留既有轮转基线。字段桶复用已有 Python 分页覆盖接口，评分公式见 [第 5 步](../agents/path_merge_call_support/fuzz-step5.md)。默认 5% 对照从 `--fuzz-mutations` 与原始输入构成的 replay-log 记录池抽样，统一在 A/B 之后生成；不提供对照池时显式设 `--fuzz-control-percent 0`。新 corpus entry 必须先认证；验收使用 `--fuzz-certify-all` 对全部接纳输入做两档逐字段比较。

`--fuzz-avoid-known-ppn-overflow` 默认关闭。开启后，分页 A/B 优先令活动叶 PTE[53:46]=0；若目标类要求超宽，则撤下本次偏好，保留取值并在 `ppn-preference-summary.json` 计数。它不约束编码空间对照，不改变模型和窄规则；详见 [第 8 步](../agents/path_merge_call_support/fuzz-step8.md)。

生成遵循 `-T`，每个目标类的排重历史按编号处理；批内先预约目标，输出与线程完成顺序无关。普通 `--executor model` 不连接硬件。`--executor difftest` 对要送硬件的输入先做完整认证，再提交有界 worker 池；默认 `--difftest-workers 8`，允许 1 到 12，单例 `--difftest-timeout 120` 秒，允许 1 到 600。Python worker 外层额外保留 30 秒用于构建与清理。支持 SIGINT/SIGTERM 取消、整进程组及独立子会话清理。

`--difftest-worker/profile/lock/files/observer` 分别指定 Python 入口、平台描述、平台锁、工具路径 JSON 和独立 NEMU 观察器。默认入口是当前仓库的 `tools/fuzz/paging_worker.py`；外部只读目录由 `DIFFTEST_XIANGSHAN_DIR` 选择，默认来源与 [第 4 步记录](../agents/path_merge_call_support/fuzz-step4.md) 一致。`PT_DECODE_DIR` 选择既有解码器。平台锁只记录 isarch 身份，样本有效性由当前模型认证决定。

闭环额外输出 `difftest-results.jsonl`、`findings.jsonl`、`findings-summary.json`，每个输入的 ELF、原始日志和结构化 `result.json` 位于 `difftest/input-编号/`。保留原始不一致数量，再统计窄规则 `R-XS-001` 命中数；未过滤分歧只记录，不自动认定为缺陷。分组依据为目标类、不同字段和阶段。`feedback-observations.jsonl`、`feedback-summary.json`、`schedule-scores.jsonl` 记录反馈和批次评分，`corpus-added.jsonl` 保存完整类身份、输入标识、血缘和认证样本。`hardware-timing.jsonl` 单列每例 emu 耗时；根目录硬件结果保留确定性的语义字段，完整原始结果仍在逐例目录。

所有 fuzz 模式都将路径 DAG 写到 `dag/`，重读检查结果写到 `dag-manifest.json`。格式见 [DAG 导出](../agents/path_merge_call_support/fuzz-dag-export.md)，本轮实验与限制见 [第 3 步记录](../agents/path_merge_call_support/fuzz-step3.md)。

输出 `judged.jsonl` 为 judged v1，`classified.jsonl` 为完整 samples v1；类目录、变异记录、认证、覆盖和统计另存。旧缺 `fcsr` 的 P1b 输入通过 replay-log 从父 corpus entry 补齐并审计。完整命令、文件说明与四场景验收见 [第 2 步记录](../agents/path_merge_call_support/fuzz-step2.md)，也可运行 `isarch fuzz --help`。

## 合并拒绝诊断

`--merge-diagnostics off|summary|detail` 默认关闭。`summary` 每 15 秒及正常收尾时，按位置、槽和差异类别输出累计汇总；`detail` 另输出采样的单行 JSON。该选项独立于 `ISLA_STATS`，不改变合并准入或求解条件。

记录包含 `stage`、尝试编号、父尝试编号、函数／IR pc、槽名与声明类型、原始初始化状态、正常初始化后的值形态、失败字段／元素路径及原错误。执行臂内无法取得双臂槽的错误使用 `stage=execute_arm`，槽和值填 `null`；嵌套传播另记 `merge_value_propagated`。

细节每个汇总键最多 3 条，全进程最多 1000 条，每行最多 4096 字节，路径最多 8 层。汇总最多保留 4096 个键，每键最多 1024 字节，超出计入 `other`。`details_suppressed` 和 `oversized` 明确记录未输出的细节，采样行数不代表拒绝总数。

每组汇总带同一个 `snapshot`，末行 `merge_value_summary` 表示该组输出完整；`trigger` 区分 `periodic`、`final` 和 `signal`。计数不清空，比较时应选完整的一组，不能跨组累加。开启诊断后，收到 SIGINT／SIGTERM 会尽力补写汇总，再恢复原信号行为；SIGKILL 不会触发补写。关闭诊断时不注册这些信号处理器；诊断与 `ISLA_STATS` 均关闭时不创建统计线程。

同组还输出 `merge_timing_site` 和 `merge_timing_summary`。按区域入口（函数／IR pc）与结果汇总尝试数、墙钟秒、真实SMT求解秒／次数、模型取值秒／次数；每项都有 `sum`、`mean`、`max`。`inclusive` 包含子区域，不能跨层相加；`exclusive` 扣除子区域；`root` 只计最外层尝试，并按最外层结果归属其全部嵌套成本。成功子区域若随外层回滚，其成本因此计入该根拒绝。单次直接槽差异仍见既有 `merge_value_summary_key`，不另算一次区域拒绝。

`all_smt` 记录全进程已返回的受保护Z3调用，`outside_smt` 记录不在区域尝试内的调用；真实求解和模型取值分开，已有模型命中／恒值化简不增加真实查询数。时间是各执行线程的墙钟累计，包含等待和调度，不能当进程CPU时间或直接与进程墙钟相加。周期中尚在执行的区域不进入结束尝试聚合，已返回的内部SMT已进入 `all_smt`，由 `in_flight` 明示；全部尝试结束时，根SMT累计加区域外SMT等于全进程SMT，独占累计等于根累计。位置键另限4096个、每键1024字节，溢出计入 `other_sites`，结果总表不丢计数。关闭时不取时钟、不访问计时线程局部栈、不分配计时表或取计时锁，仅检查已有诊断开关。

区域行的均值以尝试数为分母；`all_smt`／`outside_smt` 的 `count` 是全部已返回受保护Z3调用数（含模型取值），相应均值以该数为分母。单次真实求解的均值应按 `smt_seconds.sum / queries.sum` 计算；模型取值同理。

## 分段合并候选与诊断配置

这些选项放在主配置或 `--execution-limits-config` 文件中：功能字段放 `[execution_limits.path_merge]`，只读诊断放 `[execution_limits.path_merge.diagnostics]`，`bool_proof_rlimit` 放 `[execution_limits.solver]`。CLI 在加载配置后覆盖对应字段；布尔参数必须显式传 `true` 或 `false`，因此可以关闭 TOML 已开启的选项。未指定的 CLI 参数保留 TOML 值。所有选项默认保持原执行行为，不再读取先前新增的 `ISLA_REGION_*` 等功能／诊断环境变量；本节表格给出完整范围，其他既有环境变量不受影响。

| TOML 字段 | CLI 参数 | 默认值 | 用途 |
| --- | --- | --- | --- |
| `path_merge.prune_constant_branches` | `--prune-constant-branches=true/false` | `false` | Jump 入口识别符号表达式的布尔恒值；不查询 SMT |
| `path_merge.defer_exit_check` | `--region-defer-exit-check=true/false` | `false` | 延迟区域出口检查 |
| `path_merge.lazy_z3_scope` | `--region-lazy-z3-scope=true/false` | `false` | 延迟 Z3 条件作用域，仅在 defer 推演内生效，可能增加内存占用 |
| `path_merge.witness_eval` | `--region-witness-eval=true/false` | `false` | 完整前提见证求值 |
| `path_merge.diagnostics.witness_shadow` | `--region-witness-shadow=true/false` | `false` | 见证影子诊断 |
| `path_merge.diagnostics.witness_local_shadow` | `--region-witness-local-shadow=true/false` | `false` | 局部见证补全影子诊断 |
| `path_merge.prefix_compact` | `--region-prefix-compact=true/false` | `false` | 迭代边界前缀固化 |
| `path_merge.diagnostics.bool_proof_profile` | `--region-bool-proof-profile=true/false` | `false` | 可选布尔证明资源统计 |
| `path_merge.diagnostics.progress` | `--region-progress=true/false` | `false` | 区域步数和查询进度诊断 |
| `path_merge.diagnostics.native_snapshot` | `--region-native-snapshot=true/false` | `false` | 原生查询快照 |
| `path_merge.diagnostics.call_census` | `--call-census=true/false` | `false` | 有界函数调用统计 |
| `path_merge.diagnostics.probe_round_cost` | `--probe-round-cost=true/false` | `false` | 逐轮成本分账 |
| `path_merge.diagnostics.probe_query_timings` | `--probe-query-timings=true/false` | `false` | 有界逐查询计时 |
| `solver.bool_proof_rlimit` | `--region-bool-proof-rlimit=<u32>` | `0` | 可选布尔证明资源上限；0 不限，路径可达性判定不受此上限影响 |
| `path_merge.diagnostics.query_dump_sites` | `--query-dump-sites=f@1,g@2` | `[]` | 按已有位置字符串选取有界查询导出点 |
| `path_merge.diagnostics.same_context_sites` | `--same-context-sites=f@1,g@2` | `[]` | 最多两个同 Context 配对位置 |
| `path_merge.diagnostics.query_dump_dir` | `--query-dump-dir=<path>` | 未配置 | 查询 SMT2 导出目录；配置 query_dump_sites 时必填 |
| `path_merge.diagnostics.obligation_dump_dir` | `--obligation-dump-dir=<path>` | 未配置 | 断言义务诊断目录 |

```toml
[execution_limits.path_merge]
defer_exit_check = true
witness_eval = true
[execution_limits.path_merge.diagnostics]
progress = false
```

```bash
isarch -A model.ir -C scenario.toml -T 32 --path-merging \
  --region-progress=true --region-witness-eval=false \
  solve-state --clause=CLAUSE
```

位置数组通过 CLI 以逗号分隔，传空串可清空，例如 `--query-dump-sites=`。非布尔开关值、负数／超范围 u32、空导出目录、未知 TOML 字段、超过两个配对位置或缺少必需导出目录均报错。位置名称沿用诊断原有格式，不增加模型或函数特判。

配置在架构初始化前确定，执行期间按进程冻结；同一进程再次初始化架构时只能传入相同选项。诊断仍遵循已有条数／轮次限制。延迟 Z3 作用域也默认关闭，不再读取 `ISLA_REGION_LAZY_Z3_SCOPE`。仅设置 `lazy_z3_scope=true` 而未开启 `defer_exit_check` 时静默无效；只有在 defer 推演内省去临时 push/pop，离开 defer 后的实际查询仍包含完整活动条件。

开启可能增加内存占用。历史 STORE 两分钟探针峰值约 10.4 GiB，关闭侧约 8.9 GiB；PMP=2 的有限两输入 judge 峰值约 68.8 GiB，62 GiB 上限不足，须为该类验证选择更高的内存上限。这些测量仅针对特定输入与探索窗口，不代表任意规模的内存保证，也不签全域等价或完整 DAG。


## 无 SMT 候选配置

四个开关统一放在 `[execution_limits.solver]`，默认均为 `false`：

| TOML 字段 | CLI（名称不变） | 行为 |
| --- | --- | --- |
| `skip_branch_checks` | `--skip-branch-checks` | 跳过分支可行性检查，保留两臂完整守卫 |
| `skip_bool_proofs` | `--skip-bool-proofs` | 跳过可选布尔恒值证明 |
| `no_smt` | `--no-smt` | 停止所有真实 check，仅构造未认证候选 |
| `no_smt_keep_bool_proofs` | `--no-smt-keep-bool-proofs` | 全局无 SMT 模式下恢复可选布尔恒值证明，包括 defer 内的查询 |

CLI 裸 flag 等于 `true`，显式 `=false` 可覆盖 TOML。`no_smt_keep_bool_proofs` 要求 `no_smt=true` 且 `skip_bool_proofs=false`。不读取这些选项的环境变量。

```toml
[execution_limits.solver]
bool_proof_rlimit = 0
no_smt = true
# 可选第三种：no_smt_keep_bool_proofs = true
[execution_limits.path_merge]
defer_exit_check = true
lazy_z3_scope = true
witness_eval = true
[execution_limits.path_merge.diagnostics]
progress = true
```

全局无 SMT 模式只支持 `solve-state --path-cache-only --path-cache-write <新目录>`，不能同时认证样本或读回缓存。产物标 `uncertified`，探索保持 partial；候选计数不能作为已认证覆盖。`--memory-stats` 输出 `no_smt_summary`；全关应为零真实 check，第三种仍会运行可选布尔恒值证明。旧 `[execution_limits.path_merge]`（包括其中的 `no_smt`）报错；四个开关也不能放在 `path_merge` 或其 `diagnostics` 表中。


使用线程中断功能构建时，`--smt-timeout` 设置单次 Z3 调用的软中断限时，缺省 60 秒。终态查询的专用限时独立生效。直接调用构建没有这两种单次限时。

### 臂内执行错误叶子

`[execution_limits.path_merge].arm_error_leaf` 默认关闭，`--arm-error-leaf=true|false` 可覆盖。
延迟区域检查下，位置和到达条件随错误保留。执行器按逻辑臂冻结访存前缀并撤销该臂的正常出口，兄弟臂继续参与汇合。启用 SMT 时，区域出口证明错误不可达后才提交。无 SMT 时，缓存写出未认证的 `ExecutionError` 终态，支持用 `--path-cache-read` 配合 `--check-samples` 或 `--judge-resident` 重新判定。不可达的错误终态不影响正常路径接纳，可达的执行错误会使签收失败。

## 投影枚举与样本输出

在 `[execution_limits.path_merge.enumeration]` 设置 `enabled=true` 后开始枚举。每个守卫类的 `class_cap` 与每条完成路径的 `path_cap` 缺省均不限，可显式设置正整数。达到上限且仍有可行解时记录截断。`sample_stride` 缺省为 1，显式大于 1 时按步长选择输出，计数仍包含已枚举的解。

`mode="samples"` 为每组可行的守卫赋值和被测位投影输出一份具体见证。关闭枚举时，样本后端为每条完成路径输出一个代表，旧 `gen` 为每个可编码分支输出一个代表。judge 依据原路径约束逐条检查输入。省略 `--check-samples-limit` 时读取到 EOF。

单 binary 后端且 `sample_stride=1` 时使用二进制 schema 2 流式写出，字节数缺省不限。显式 `max_output_bytes` 至少为 1024，并要求这种输出配置。每 60 秒刷新并记录写入进度。创建与输出同名、扩展名为 `.stop` 的文件会在轮询后停止接收新样本。字节到限与文件停止在汇总中分别记为 `output_budget`、`stop_file`，收尾时保存截断统计和正常结束标记。

`mode="count"` 只计数。`mode="predict"` 缺省精确计数并以十进制字符串输出。浮点表示超出范围时可省略浮点统计。显式设置 `predict_probes`（至少 200）启用近似预测，此时可用 `predict_domain_cap` 设置每个分量的精确验证额度，额度缺省为 256。超过额度后进行探测，保留精确前缀与下界。两种模式均不写见证。

终值重解可在 `[execution_limits.solver]` 显式设置正整数 `model_timeout_ms`。查询取此限时、`--smt-timeout` 和路径剩余时间中的最小值。

### 通用 SMT 等价改写

`[execution_limits.solver] bv_rewrite` 缺省为 `false`。`true` 启用全部规则；列表可选 `data-ite-eq`（数据 ITE 相等展开）、`mask-and`（位掩码恒等式）、`sign-bound`（符号扩展与常量比较）。空列表关闭。

CLI `--bv-rewrite` 等价于 `--bv-rewrite=true`。`--bv-rewrite=false` 关闭，`--bv-rewrite=data-ite-eq,sign-bound` 独立选择规则；CLI 整体覆盖 TOML。没有开启新的 SMT 查询，同一改写也用于 `--no-smt`。`--memory-stats` 输出 `bv_rewrite_hits`，统计本进程各规则累计改写次数。

## resident judge 分批恢复

普通 `--judge-resident INPUT --judge-resident-out OUTPUT` 默认每批恢复 `-T` 条完成路径，每批对全部输入执行原 judge，再释放该批求解器和 Context。所有保存路径仍参与判定，跨批重复接纳仍报错，守卫和后态唯一性证明保持原行为。保存路径及其事件记录仍占内存，因此批大小只约束恢复出的 native solver 数，不保证整个进程的固定内存上限。

`--judge-resident-batch-size N` 可覆盖 `[execution_limits].judge_resident_batch_size=N`，要求正整数。此选项只用于普通 resident judge，不能与 `--judge-resident-fast` 或 fuzz 同用。新选项不读取环境变量。逐批 `JUDGE_RESIDENT_BATCH_RESTORED` / `JUDGE_RESIDENT_BATCH_MEASUREMENTS` 记录恢复和判定；最终 `JUDGE_RESIDENT_MEASUREMENTS` 汇总批数、累计恢复/判定墙钟和峰值在驻 solver 数，`JUDGE_RESIDENT_REPORT` 保持原报告字段。多输入的接纳行按批完成顺序写出，使用方按 sample_id/path_signature 对齐。

实验选项 `[execution_limits.path_merge] defer_range_proofs` 与 `defer_ctor_checks` 均默认 false；CLI `--region-defer-range-proofs=true|false`、`--region-defer-ctor-checks=true|false` 分别覆盖。它们只延后可表达的范围／标签证明；出口须在完整原到达域下验证反例为空，否则原子回滚。
## 配置布局与迁移

`execution_limits` 只保留非合并的全局限制、输出过滤、配额和 judge 参数。路径合并全局参数放 `execution_limits.path_merge`，枚举配置放其 `enumeration` 子表，省略类、路径及字节上限即不限。局部规则统一放 `regions` 数组。`step_budget` 缺省关闭（-1），`-1`关闭；CLI名字和优先级不变。

步数、嵌套深度及片段数缺省不限，显式 `-1` 与省略等价。正整数 `max_merge_depth` 可由 `--region-max-merge-depth` 覆盖。保存点深度不限，诊断记录实际区域深度分布和最大值，调用深度另计。正整数 `max_fragments` 允许每次根区域尝试额外保留至多 `max_fragments - 1` 个局部汇合失败片段，超限计 `fragment_limit` 并保留普通分叉。

每条局部规则必须显式指定 `kind`，不得靠缺失字段猜类别：

| kind | 原规则含义 | 必需配置 |
| --- | --- | --- |
| `limit_filter` | 分支/循环执行限制只作用于指定源码范围；不限制路径级预算 | 源码坐标 |
| `branch_limit` | 指定范围内每个分支点的独立预算 | 源码坐标、`max_forks_per_branch` |
| `fork_limit` | 原区域 fork 预算及可选方向偏置 | 源码坐标、`max_forks_per_region`；偏置仍需同时指定 `sample_bias`、`sample_bias_direction` |
| `merge_policy` | 函数或源码范围的合并策略，优先级保持不变 | `mode` 与 `function` 或源码坐标二选一 |

源码坐标是 `file`、`start_line`、`start_column`、`end_line`、`end_column`。旧筛选范围会先清除预置的两类局部预算，然后应用同一配置里的局部覆盖；未知文件仍匹配不到位置。规则数组不能为空。

```toml
[execution_limits.solver]
bool_proof_rlimit = 0
[execution_limits.path_merge]
enabled = true
[execution_limits.path_merge.diagnostics]
progress = false
```

有限预算对照示例

```toml
[execution_limits]
max_forks_per_branch = 7
[execution_limits.path_merge]
max_merge_depth = 16
step_budget = 8192
```

旧 `path_merging`、`region_step_budget`、`region_options`、`regions`、`branch_region_limits`、`region_fork_limits`、`merge_policy`、`merge_enumeration` 顶层字段已删除，出现即报错并提示新位置。没有兼容别名。历史归档配置仅适用于其原二进制；复用时先迁移配置，再按语义重新验证输入。


### 平铺合并实验策略

在 `[execution_limits.path_merge]` 中，`strategy = "recursive" | "flat"` 选择就绪片段的栈或 FIFO 队列。缺省为 `recursive`。两者共用区域准入、汇合、循环和出口检查。CLI 使用 `--merge-strategy` 覆盖此字段。

`ordered_events` 缺省为 `false`，CLI 使用 `--ordered-events=true|false`。无序时，区域臂读取本臂最新的寄存器和变量值，前态读足迹按寄存器与字段合并。若需要保留寄存器访问偏序，可显式设为 `true`。两种策略都使用此配置。

区域步数、嵌套深度与片段数缺省不限。循环的可配置步数预算及切段规则由两个组织者共用。旧 `[execution_limits]` 下的策略字段和旧 `region_options` 配置位置报错。
