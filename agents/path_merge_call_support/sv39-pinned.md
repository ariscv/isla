# Sv39：钉住 CFI CSR 的短测与分叉命令

结论：本工作树的合并模式用 8 个工作线程，在 **7.94 秒**完整结束，输出 **52 条路径**，`status=finished`，错误、执行超时、SMT 超时、未完成路径均为零。单线程另一次短测在 20 秒外限被终止，不能报告为完成。这里没有运行长时间 Sv39 分叉实验，也不保证下面的分叉命令一定跑完。

## 位与语法核实

实际读取的模型文件为 `/data1/baiyifan/workplace/isla-runner/sail-riscv/model/extensions/cfi/zicfilp_regs.sail`：

| `get_xLPE` 的权限参数 | 读取 |
| --- | --- |
| Machine | `mseccfg.MLPE`，bit 10 |
| Supervisor | `menvcfg.LPE`，bit 2 |
| User，启用 S | `senvcfg.LPE`，bit 2 |
| User，未启用 S | `menvcfg.LPE`，bit 2 |
| VirtualSupervisor / VirtualUser | 当前模型调用 `internal_error`；没有实现 henvcfg 读取 |

位号来自 `model/core/sys_regs.sail` 的 `Seccfg`、`MEnvcfg`、`SEnvcfg` 位域声明。实际受测 `rv64d.ir` 的三个顶层寄存器类型分别为 `%struct zSeccfg`、`%struct zMEnvcfg`、`%struct zSEnvcfg`，均含 64 位 `bits` 字段。

`src/isarch/exec.rs::parse_fixed_prestate` 用既有 `AssignParser` 解析，并要求 `Loc::Id`：只能赋整个顶层寄存器，不能写 `menvcfg.LPE=0`。结构体赋值经过 `target.rs::validate_fixed_prestate_value` 按 IR 类型校验。因此三项都使用 **`寄存器={bits=0x0000000000000000}`**，不能沿用 satp 的裸位串写法。该命令将三个 CSR 的完整值设为零；不声称只改一个字段。上述 20 秒短测已实际通过解析与执行。

## 完整命令

在本工作树执行；外层 `timeout` 控制整个进程，因为仅有 `--timeout` 不保证进程及时退出。

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
IR=/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir
CONFIG=/data1/baiyifan/workplace/isla-runner/.worktree/mmu-symbolic-experiment/symbolic/config.toml

timeout 20 target/release/isarch \
  -A "$IR" -C "$CONFIG" -T 8 --timeout 19 \
  --instruction-bits 0x0000b103 \
  --prestate 'x1=0x0000000020000000' \
  --prestate 'cur_privilege=Supervisor' \
  --prestate 'satp=0x8000000000080200' \
  --prestate 'mstatus={bits=0x0000000a00040000}' \
  --prestate 'menvcfg={bits=0x0000000000000000}' \
  --prestate 'senvcfg={bits=0x0000000000000000}' \
  --prestate 'mseccfg={bits=0x0000000000000000}' \
  --path-merging solve-state --clause=LOAD
```

原 Sv39 命令的 IR、配置、指令、x1、权限、satp、mstatus 全部保留，仅增加三个 CSR 钉值及本次短测的工作线程数与时间外限。128 个逻辑核的主机当时没有其他计时实验，构建用 8 并行、测试用 4 线程；短测使用 8 个工作线程。单次结果不是性能分布。

分叉实验由用户运行：复用上面整条命令，**去掉 `--path-merging`**，并按实验预算同时增大外层 `timeout` 与内部 `--timeout`。例如外限 1800 秒、内部 1790 秒。通过下面的前缀增量导出，文件应使用每次实验独立的路径：

```sh
ISLA_EXPORT_SAMPLES=/tmp/sv39-fork.jsonl timeout 1800 target/release/isarch \
  -A "$IR" -C "$CONFIG" -T 8 --timeout 1790 \
  --instruction-bits 0x0000b103 \
  --prestate 'x1=0x0000000020000000' \
  --prestate 'cur_privilege=Supervisor' \
  --prestate 'satp=0x8000000000080200' \
  --prestate 'mstatus={bits=0x0000000a00040000}' \
  --prestate 'menvcfg={bits=0x0000000000000000}' \
  --prestate 'senvcfg={bits=0x0000000000000000}' \
  --prestate 'mseccfg={bits=0x0000000000000000}' \
  solve-state --clause=LOAD
```

合并运行检查这些分叉样本：在第一条命令增加 `--check-samples /tmp/sv39-fork.jsonl --check-samples-limit 100 --check-samples-report /tmp/sv39-fork-in-merge.json`，并按样本数增加时间预算。反向时，合并运行先设置 `ISLA_EXPORT_SAMPLES`，分叉运行再传 `--check-samples`。两次运行应使用相同 IR、配置、指令及钉值。

## 本次观测

| 检查 | 结果 |
| --- | --- |
| 钉值，合并，`-T 1` | 外限 20 秒退出 124，未完成 |
| 钉值，合并，`-T 8` | 7.94 秒，退出 0，52 条，完整 |
| 同配置导出，不开 E1 枚举 | 7.58 秒，52 行完整 JSONL |
| 导入前 10 个样本 | 8.24 秒，10/10 接纳且强制一致 |
| 导入全部 52 个样本 | 10.89 秒；后续 12.30 秒；最终版 10.59 秒，52/52 各接纳一次且一致 |
| 扩充为 1040 个编号不同的样本（重复上述 52 个具体状态） | 99.64 秒，1040/1040 各接纳一次且一致；这是吞吐检查，不是新增 1040 个不同状态 |

原始命令、stdout、stderr、输入样本、报告保存在 `/tmp/e2/`，包括 `sv39-pinned-t8-result.json`、`sv39-samples.jsonl`、`sv39-report52.json`、`sv39-report1040.json`。配置的既有 `__isla_always_aligned` 缺失警告仍在，没有更改模型或配置。
