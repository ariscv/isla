# pte_is_invalid 函数基线（任务 B，2026-11-05）

**结论：不开路径合并，函数完整结束，路径数 N = 10；8 条返回 `true`，2 条返回符号布尔值。5 个已知失败测试全部仍失败。开启合并的同条件对照受现有命令行入口限制阻塞，合并路径数与 `[MERGE_STATS]` 均未测得，不能记为 10 或 0。**

本轮仅测量与记录，未修改解释器、合并逻辑或 Rust 源码，未做 git 写操作。对应计划 §5.1、§5.5；未进行 §5.2 的合并等价性证明、暴力枚举或端到端 solve 验收。无功能实现改动，因此没有新增实现测试；先复跑现有失败测试，再搭记录脚本。所有执行均有外层 `timeout`，单次总上限不超过 10 分钟。

## 版本与输入

- 日期：2026-11-05；分支：`feat/postprocess-enumeration`。
- `git rev-parse HEAD`：`8f118db6d74dcddcc9a561c74e5a124c2044f7b8`。
- 构建及五项测试完成后检查工作树，Rust 源码仍无差异；随后另一并行任务开始修改源码。本记录绑定上述 HEAD 和下列二进制哈希，不代表后来工作树的实现。
- IR：`/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir`；SHA-256：`c0e4661a73888c56438a6f76059370667d141a026502d0511291586067bd31c0`。
- 函数入口：`src/execute-function.rs`；隔离构建的调试二进制：`/tmp/claude-1005/-data1-baiyifan-workplace-isla-runner/a39d8bcc-3e1b-4db3-8d63-110f0b832032/scratchpad/target_b/debug/isla-execute-function`。
- 该二进制 SHA-256：`3c2bfbf11d7251f25b7926bee098db3f6d949af12173bc838f92e0ea7dcd9d69`；`--version` 输出：`v0.2.0/z3-5.3.4.0 1fd1d3613c1f34c4dff36cba3209b2234f6c6d2b 1fd1d3613`。
- 用户指定的既有二进制：本工作树 `target/release/isarch`；SHA-256：`3f8fbdd1ab7071a9abc2d7b0e1c6ec86cb2242051c230a92f71668b23f5d84ac`。本轮未重新构建或覆盖它；无法仅凭该文件证明其构建提交。
- 配置：[baseline_config.toml](baseline_config.toml)，SHA-256：`39d5a7eaad3c42526fb3408dc69b5a9f22f0a5a515869c99526e3c0e022cda90`。复用 `configs/riscv64.toml` 的工具链、地址布局与顶层设置，寄存器默认值表为空，没有配置常量原语、路径预算、采样或配额。测量后只去除了复制的英文注释，配置语义未变。

## 结构体参数与适用条件

实际 IR 签名为：

```text
val zpte_is_invalid : (%struct zPTE_Flags, %struct zPTE_Ext) -> %bool
struct zPTE_Flags { zbits: %bv8 }
struct zPTE_Ext   { zbits: %bv10 }
```

复用入口的 `pte_is_invalid _ _`：`_` 保留参数原始类型的未初始化值，解释器首次访问时由现有 `symbolic_from_typedefs` 递归创建符号结构体。没有传入具体字段值，也未使用模型取值选项 `--model`；短路提前返回时未访问的参数保持任意，迹中不一定出现它的声明。

`PTE_Flags.bits[7:0]` 全部符号，依次为 `D/A/G/U/X/W/R/V`；`PTE_Ext.bits[9:0]` 全部符号，分别为 `N[9]`、`PBMT[8:7]`、`RSW_60t59b[6:5]`、`reserved[4:0]`。**请求中的普通 RSW[9:8] 不在该函数的参数类型中，无法经此签名输入；本轮没有伪造附加字段。N=10 是实际 IR 签名下的基线，不是包含普通 RSW 的新签名测试。** 不需要结构体参数的 `--prestate` 折中；`--prestate` 本身只接受完整顶层寄存器，不能替代函数实参。

保留入口原有的模型寄存器初始化及 `reset_registers`。在读取寄存器的路径，实际迹显示 `misa.bits = 0x8000000000000000`，由模型初态产生，本轮未用命令或配置钉值。因此 N 不是对所有可能 CSR 初态取并集的结果。此 IR 的 `currentlyEnabled(Svnapot)`、`currentlyEnabled(Svpbmt)` 直接返回 `false`（IR 96054、96057 行）；`Svrsw60t59b` 还依赖 `currentlyEnabled(Sv39)`，本次初态下为 `false`。扩展位本身仍全符号。

首次尝试直接使用仓库 `configs/riscv64.toml`，在执行函数前就因 `vr0` 默认值宽度不匹配而失败：配置值 256 位，IR 要求 `Bits(128)`，退出码 101、6.215 秒；证据见 `logs/pte_config_mismatch.*`。改用上面的空默认值表配置后成功。原始 stderr 仍有缺少若干无关原语的告警，完整保存在 [pte_no_merge.stderr](logs/pte_no_merge.stderr)；本次目标函数的 10 条结果全部完成，退出码为 0。

## 不合并测量

| 项目 | 实测 |
| --- | --- |
| 完成路径数 | **10**，按原始输出 `Result:` 行计数 |
| 返回值 | 8 个 `true`；`v17`、`v19` 各 1 个 |
| 符号返回值含义 | `reserved != 0b00000`；每条路径内仍可为真或假 |
| 执行器报告耗时 | `Execution took: 131ms` |
| 整个子进程墙上耗时 | **6.613 秒**，包含 IR 加载、模型初始化和输出，不含构建 |
| 退出码 | 0，无错误路径输出、无超时 |
| 并行参数 | `-T 1`，固定输出顺序便于逐条记录 |
| 统计环境 | `ISLA_STATS=1`；函数入口没有打印统计的收尾代码，未产生 `[MERGE_STATS]` |

路径编号与原始 `Result:` 输出顺序一致。下表 `C0 = (V=1 ∧ W=0)`，`C1 = (V=1 ∧ W=1 ∧ R=1)`；`B=PBMT`，`S=RSW_60t59b`，`Q=reserved`。没有列出的字段不受该路径条件约束。

| 路径 | 路径条件摘要 | 原始返回值 | SMT-LIB |
| --- | --- | --- | --- |
| 1 | `V=0` | `true` | [path-01](paths/path-01.smt2) |
| 2 | `V=1 ∧ W=1 ∧ R=0` | `true` | [path-02](paths/path-02.smt2) |
| 3 | `C0 ∧ N=1` | `true` | [path-03](paths/path-03.smt2) |
| 4 | `C1 ∧ N=1` | `true` | [path-04](paths/path-04.smt2) |
| 5 | `C0 ∧ N=0 ∧ B≠0` | `true` | [path-05](paths/path-05.smt2) |
| 6 | `C1 ∧ N=0 ∧ B≠0` | `true` | [path-06](paths/path-06.smt2) |
| 7 | `C0 ∧ N=0 ∧ B=0 ∧ S≠0` | `true` | [path-07](paths/path-07.smt2) |
| 8 | `C1 ∧ N=0 ∧ B=0 ∧ S≠0` | `true` | [path-08](paths/path-08.smt2) |
| 9 | `C0 ∧ N=0 ∧ B=0 ∧ S=0` | `v17 = (Q≠0)` | [path-09](paths/path-09.smt2) |
| 10 | `C1 ∧ N=0 ∧ B=0 ∧ S=0` | `v19 = (Q≠0)` | [path-10](paths/path-10.smt2) |

原始迹：[pte_no_merge.stdout](logs/pte_no_merge.stdout)；命令、退出码及总耗时：[pte_no_merge.json](logs/pte_no_merge.json)。[extract_paths.py](extract_paths.py) 只转换实测迹中的声明、定义和断言，为 SMT-LIB 补足类型，将输入名统一为 `pte_flags`、`pte_ext`；原始枚举、寄存器读及分支事件保留在原始迹。10 份文件均经外层 15 秒限时的现有 Z3 检查，可解析且 `sat`，见 [验证输出](logs/smt_validation.json)。`get-value` 的单个模型取值不能用于把最后两条路径归为恒定真或假。

复现构建与运行（从本工作目录执行）：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
export LD_LIBRARY_PATH="$HOME/.local/opt/z3-official-1fd1d3613/lib:${LD_LIBRARY_PATH:-}"
export CARGO_TARGET_DIR=/tmp/claude-1005/-data1-baiyifan-workplace-isla-runner/a39d8bcc-3e1b-4db3-8d63-110f0b832032/scratchpad/target_b
timeout --signal=TERM --kill-after=5s 590s \
  cargo build --offline --features smt-thread-interrupt \
  --bin isla-execute-function -j 8
ISLA_STATS=1 timeout --signal=TERM --kill-after=5s 590s \
  "$CARGO_TARGET_DIR/debug/isla-execute-function" \
  -A /data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
  -C agents/path_merge_call_support/baseline_config.toml \
  -T 1 --timeout 540 --traces --error-traces pte_is_invalid _ _
python3 agents/path_merge_call_support/extract_paths.py
```

也可在已有隔离二进制的条件下执行 `python3 agents/path_merge_call_support/run_baseline.py`，直接重新保存日志。构建日志：[build_execute_function.log](logs/build_execute_function.log)，本轮构建报告 31.72 秒。不要重编覆盖 `target/release/isarch`。

## 开启合并：阻塞与证据

使用同一函数、同一结构体符号参数和配置，仅增加 `--path-merging` 的实际尝试：

```sh
ISLA_STATS=1 timeout --signal=TERM --kill-after=5s 590s \
  "$CARGO_TARGET_DIR/debug/isla-execute-function" \
  -A /data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
  -C agents/path_merge_call_support/baseline_config.toml \
  -T 1 --timeout 540 --traces --error-traces --path-merging pte_is_invalid _ _
```

0.108 秒后退出 1：`Unrecognized option: 'path-merging'`。见 [命令与结果](logs/pte_merge_entry.json)、[原始 stdout](logs/pte_merge_entry.stdout)、[原始 stderr](logs/pte_merge_entry.stderr)。这不是执行得到的 0 条路径，而是尚未进入符号执行。

继续核对用户指定的现有 `isarch`：

```sh
ISLA_STATS=1 timeout --signal=TERM --kill-after=5s 20s \
  target/release/isarch \
  -A /data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
  -C agents/path_merge_call_support/baseline_config.toml \
  -T 1 --timeout 15 --path-merging pte_is_invalid _ _
```

0.108 秒后退出 1：`Error: 未知命令 'pte_is_invalid'`。见 [命令与结果](logs/isarch_function_entry.json)、[原始 stderr](logs/isarch_function_entry.stderr)。源码 `src/isarch_main.rs` 的 `parse_subcommand` 只接受 `list-instructions`、`tree`、`solve-state`，并没有函数实参入口；`--clause` 面向指令构造子，不等于任意函数。`--prestate` 也只能设置寄存器，不能替代这两个结构体实参。

另核对 `src/execute-function.rs`：它直接创建 `TaskState::new()`，未把配置中的 `execution_limits` 附加到任务；`isla-lib/src/executor/task.rs` 中该构造器的 `execution_limits` 为 `None`。因此即使把 `[execution_limits] path_merging=true` 写进配置，也不能当作已经开启合并。该入口亦未调用 `src/isarch/solve_summary.rs` 的统计打印函数。

**本任务禁止修改现有 Rust 文件或新增 Rust 执行器，所以在当前范围内无法连通“函数级实参 + 开启合并 + 统计输出”三项能力。合并路径数、合并耗时及 `[MERGE_STATS]` 均为未测／阻塞；不以普通运行冒充合并对照，也不从无输出推断尝试数或成功数。**

## 五个测试与检查

五项完整测试名、失败摘要、精确耗时与命令已追加至 [agents/findings.md](../findings.md) 的“路径合并分支 HEAD 即失败的测试”一节。结论均为失败，Cargo 退出 101，无超时；没有修复它们。串行复跑脚本：[run_failed_tests.py](run_failed_tests.py)；[结果索引](logs/failed_tests.json)。

执行了只读格式检查 `timeout --signal=TERM --kill-after=5s 30s cargo fmt --all -- --check`，退出码 1，日志见 [cargo_fmt_check.log](logs/cargo_fmt_check.log)。差异来自并行任务正在修改的 `isla-lib/src/config.rs`。本任务没有 Rust 改动；为遵守仅允许文件范围及不干扰并行任务的要求，没有运行会重写这些文件的格式化命令。未运行 `make solve`：此次交付是函数级测量，不是功能实现验收。
