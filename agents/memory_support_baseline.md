# 内存符号化注入改动前基线快照（no-regression 基准）

> 本文件为 no-regression 基准：在实施"内存符号化注入"改动（executor multi_thread 入口注入 initial_memory、物化内存事件等）**之前**采集，供改动后 T9/T10 验收对照。采集时未做任何代码改动。

## 采集环境

- 日期：2026-09-10
- 分支 / commit：`feat/memory-support` @ `0008fae`（工作区干净，无未提交改动）
- 位置：worktree `.worktrees/feat-memory-support`
- 主机：12 核（nproc=12），make 并行参数 `-j12`，`THREADS=12`
- 说明：`scripts/run.mk` 的 MEMORY 列表（`AMO LOAD LOADRES STORE STORECON C_L* C_S* ...`）中不存在裸名 `LD/SD/LW/SB/AMOSWAP_W` 子句，按任务预案从 MEMORY 列表选取 5 个实际存在的等价目标：`C_LD`、`C_SD`、`C_LW`、`C_SB`、`AMO`（`make -n solve-*` 均已确认目标存在）。

## 1. cargo test --workspace 汇总

命令：`cargo test --workspace --no-fail-fast`（预存失败会导致默认运行提前中止，故用 `--no-fail-fast` 取全量汇总）。

| 套件 | 通过 | 失败 |
|---|---|---|
| isla lib（`-p isla --lib`） | 58 | **1** |
| 其余 workspace lib/bin 测试目标（242、23、13、6、5、2、1、1 等） | 293 | 0 |
| Doc-tests（isla=1，其余为 0） | 1 | 0 |
| **合计** | **352** | **1** |

预存失败基线（改动前即失败，非本次改动引入）：

- 测试：`isarch::target::tests::rv64_target_trait`
- 症状：`panicked at src/isarch/target.rs:815:9: assertion failed: regs.contains(&"x0".to_string())`
- 处理约定：改动后验收时该测试若仍按同样方式失败，视为与基线一致；其余测试必须保持通过。

## 2. solve-MRET 状态与耗时

命令：`rm -rf output/ && make solve-MRET -j12`（THREADS=12）。

- 退出码：0（make 成功）
- 状态分类：`output/status.intime.log` 含 `MRET intime`；`status.timeout.log`、`status.failed.log` 不存在
- 耗时：秒级（依据 `output/log/MRET.log` 时间戳：创建 04:21:44 → 最后写入 04:21:47，约 3 秒完成；`/usr/bin/time` 峰值内存约 980 MB）
- 产物：`output/log/MRET.log`（3642 字节），包含 3 条 PATH_RESULT 路径
  - 勘误（改动后对照时发现）：PATH_RESULT 日志段落与 JSON `gen` 条目并非一一对应；基线二进制（0008fae，临时 detached worktree 复跑）实测 `rv64_zMRET.json` 的 `gen` 数为 **4**。改动后验收以 `gen` 数 4 + 状态 `intime` 为准。

## 3. 内存 clause 子集状态（5 条，不开 memory_regions，默认配置）

命令：依次 `make solve-<clause> -j12`（串行执行，未清理 output/，MRET 记录保留）。

| Clause（实际目标） | 状态分类 | 耗时 | 备注 |
|---|---|---|---|
| C_LD | intime | 2s | `output/status.intime.log` 记录 `C_LD intime` |
| C_SD | intime | 2s | 同上 |
| C_LW | intime | 2s | 同上 |
| C_SB | intime | 3s | 同上 |
| AMO | **failed (143)** | 1021s（约 17 分钟） | `output/status.failed.log` 记录 `AMO failed (143)`；make 退出码 2 |

AMO 预存失败说明：

- 退出状态 143 = 128+15（SIGTERM），**并非** OUTER_TIMEOUT（60m）到时触发（timeout 自身到时返回 124 会被归入 `status.timeout.log`）；1021s 远小于 60m，也未达 SOLVE_TIMEOUT（55m），SIGTERM 来自 isarch 进程内部终止。
- `output/log/AMO.log` 约 3.8 MB，尾部为大量 `pmp/pmp_control.sail` 相关 FORK 活动（`pmpcfg_n`/`pmpaddr_n` 符号 taint）。
- 该失败为改动前预存状态，作为基线如实记录；改动后验收只需对比该状态是否恶化（例如新增其他 failed 条目）。

## 4. MRET.log 尾部摘录（最后 30 行，含 isa-state JSON）

```
  "mstatus": "64'h0000_0000_0000_0000",
  "vcsr": "3'h0",
  "vl": "64'h0000_0000_0000_0018",
  "vstart": "64'h0000_0000_0000_0000",
  "vtype": "64'h0000_0000_0000_0013"
}
[PATH_RESULT]: 3. ==============================
[PATH_RESULT]: 当前汇编：Some("mret")
[PATH_RESULT]: 2. === ISA State (Thread 4) ===
[PATH_RESULT]: 当前汇编encdec：Some("32'h3020_0073")
[PATH_RESULT]: 当前汇编：Some("mret")
[PATH_RESULT]: isa_state={
  "cur_privilege": "Machine",
  "mstatus": "64'h0000_0000_0000_0800",
  "vcsr": "3'h0",
  "vl": "64'h0000_0000_0000_0018",
  "vstart": "64'h0000_0000_0000_0000",
  "vtype": "64'h0000_0000_0000_0013"
}
[PATH_RESULT]: 3. ==============================
[PATH_RESULT]: 当前汇编encdec：Some("32'h3020_0073")
[PATH_RESULT]: isa_state={
  "cur_privilege": "Machine",
  "mstatus": "64'h0000_0000_0000_1800",
  "vcsr": "3'h0",
  "vl": "64'h0000_0000_0000_0018",
  "vstart": "64'h0000_0000_0000_0000",
  "vtype": "64'h0000_0000_0000_0013"
}
[PATH_RESULT]: 3. ==============================
```

即：MRET 共 3 条路径，均 `cur_privilege=Machine`，差异仅在 `mstatus`（0x0 / 0x800 / 0x1800，对应 MIE/MPIE 位组合）。

## 5. 基线对照要点（改动后 T9/T10 使用）

1. cargo test：除 `rv64_target_trait` 这 1 条预存失败外，其余 352 项必须保持通过，且不得新增失败。
2. solve-MRET：保持 `intime`，退出码 0，`gen` 数 4（见上文勘误）。
3. 内存子集：C_LD / C_SD / C_LW / C_SB 保持 `intime`（秒级）；AMO 基线为 `failed (143)`——改动后若变为 intime/timeout 属行为变化，需在验收报告中说明；不得出现其余条目恶化。
4. `output/` 目录未清理，保留本次基线日志（MRET.log、C_LD/C_SD/C_LW/C_SB.log、AMO.log 及三个 status 日志现状）供后续 diff 对照。
