# 通用符号指令：移除固定机器码后的实测

**探索脚本已移除固定机器码及 x1 特例。纯 `--clause=LOAD/STORE` 配合路径合并，实际导出的 LOAD 的 rs1/rd、STORE 的 rs1/rs2 均覆盖 x0–x31。** 扩大采样轮总计导出 2397 条原始语义样本；仅统计符合 RV64 编码参数域的 1801 条样本时，四个操作数维度仍各覆盖全部 32 个编号。所有改动留在当前工作树，未执行 git commit。

扩大采样轮使用 `class_cap=32`，结果位于 `output/fuzz-seq-s1-symbolic/generic-clause-wide/analysis.json`：

| 场景 | 总墙钟（秒） | 枚举完成路径 | 守卫类 | 原始样本 / 符合编码参数域 | 合并成功 / 尝试 | 成功率 | 采样峰值 VmRSS（MiB） |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| E0 Bare LOAD | 93.35 | 11 | 38 | 976 / 724 | 100 / 115 | 86.96% | 2019.76 |
| E0 Bare STORE | 99.37 | 11 | 52 | 1421 / 1077 | 96 / 111 | 86.49% | 1938.87 |

这两组进程均退出为 1，输出状态为 `partial`：每组有 4 条路径触及来源配置的排除内存区域；LOAD 另有 3 条编码过滤路径。没有枚举路径截断，但分别有 8、19 个守卫类触及类内采样配额。因此，这些结果证明操作数字段已自由符号化及样本多样性，不能当作完整收敛或完整输入覆盖。

实际样本中的部分见证如下。样本编号从各场景的 `samples.jsonl` 直接读取，访问宽度以字节计：

| 场景及字段 | x5 样本编号 | x11 样本编号 | x15 样本编号 | x31 样本编号 | 宽度 |
| --- | ---: | ---: | ---: | ---: | ---: |
| LOAD rs1 | 50 | 65 | 88 | 85 | 2 |
| LOAD rd | 213 | 299 | 360 | 374 | 4 |
| STORE rs1 | 75 | 117 | 108 | 100 | 8 |
| STORE rs2 | 45 | 106 | 144 | 156 | 2 |

`encoding_domain_samples` 只检查 RV64 LOAD/STORE 的宽度与无符号标记是否可编码：宽度必须属于 1、2、4、8，8 字节 LOAD 必须是有符号形式。原始导出发生在机器码编码过滤之前，仍包含宽度 0、负值等构造子参数；不能将全部原始样本称为可重放机器码。该统计不替代求解器认证，也没有向探索过程增加参数约束。

首轮使用来源配置的 `class_cap=1`，结果位于 `output/fuzz-seq-s1-symbolic/generic-clause/analysis.json`：

| 场景 | 总墙钟（秒） | 枚举完成路径 | 原始样本 | 合并成功 / 尝试 | 成功率 | 采样峰值 VmRSS（MiB） | 状态 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| E0 Bare LOAD | 76.34 | 11 | 38 | 100 / 115 | 86.96% | 1999.96 | 排除内存区域错误，partial |
| E0 Bare STORE | 81.14 | 11 | 52 | 96 / 111 | 86.49% | 1815.55 | 排除内存区域错误，partial |
| E0 Sv39 LOAD | 180.88 | 至少 51 | 353 | 675 / 820 | 82.32% | 4624.75 | 达到 180 秒墙钟预算 |
| E0 Sv39 STORE | 180.89 | 至少 33 | 548 | 551 / 672 | 81.99% | 4117.37 | 达到 180 秒墙钟预算 |

Sv39 的路径数和合并数据来自最后一次完整快照，属于预算结束前的计数；样本文件则在终止后逐行统计，分别含 52、35 个不同路径签名，两者时间点不同。Sv39 LOAD 的 rd 在该预算内仍只有 x0；单类单代表也不能据此判定字段固定。扩大 Bare 类内配额后，四个寄存器维度均见证全部 32 个编号。各轮存在并发重叠，不能用墙钟差声称算法加速。

`run.py` 现在显式构造命令，完全不读取旧 `done.json` 作为运行输入。指令仅通过 clause 指定；`--instruction-bits` 的两种拼写、旧 x1 或其他通用寄存器的固定初值都没有继承入口。E0/E2 ISA 配置原样复制，不再插入 `[symbolic_registers] x1 = "symbolic"`。底层已有 `setup_pre_state` 为 x1–x31 建立独立初态符号，x0 遵循常零语义；`symbolic_args_from_types` 为指令的寄存器索引、立即数、宽度等字段建立自由符号变量，符号索引读取复用现有 ITE 决策链。未修改这些 Rust 接口或 IR。

脚本保留 E0 的 Supervisor/mstatus 场景及 E2 的符号特权态配置，沿用 PMA/PMP、内存区域和环境 CSR。新增 Bare 场景只将 SATP 设为无页表转换，用来完成短时多样性验证；Sv39/Sv48 仍分别使用原页表配置。枚举配额通过 `S1_CLASS_CAP` 设置，默认 32；它只控制每类最多导出多少个片段组合，不固定寄存器、立即数或其他运行态。

探索显式使用 `--path-merging`、`path_merging=true`、`ordered_symbolic_retries=true`，沿用两个虚拟内存源码区域的 `max_forks_per_branch=4096` 和 `on_limit_reached="truncate"`。有预算截断时必须报告不完整。`analyze.py` 复用现有页表解析工具的结构体、位串及字段表，按 LOAD(imm, rs1, rd, unsigned, width) / STORE(imm, rs2, rs1, width) 统计，不再读取固定的 x1。有效地址使用实际 rs1 初值加符号扩展的 12 位立即数，并按 RV64 回绕；同时支持固定整数的 i64 编码与符号整数具体化后的 64 位 bits 编码。多个样本可以属于同一守卫类，样本编号仍必须唯一。

墙钟从启动子进程计至退出，包含 IR 加载、探索、枚举及写出，当前接口不能单独分离纯探索时间。每秒读取 `/proc/<pid>/status` 的 VmRSS/VmHWM；表中内存使用实际采样的 VmRSS 最大值，`done.json` 另存 `wait4` 的峰值 RSS 及 CPU 时间，二者分别记录。合并成功率为 successes/attempts，不能等同于最终路径减少比例。本轮主机有 128 个逻辑 CPU、约 247 GiB 内存；每个导出进程使用 32 个执行线程及 16 个枚举线程。每组保留原始命令、统计、资源序列、输出及配置快照，`provenance.json` 记录 IR、配置和二进制校验值。

等价复现命令（工作树根目录，必须选择尚未使用的组名）：

```sh
cargo fmt
make solve-MRET -j 8 THREADS=32
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s agents/path_merge_call_support/fuzz-seq-s1-tools -p 'test_*.py'
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s agents/path_merge_call_support/pt_decode -p 'test_pt_decode.py'
S1_CLASS_CAP=32 PYTHONDONTWRITEBYTECODE=1 python3 agents/path_merge_call_support/fuzz-seq-s1-tools/run.py prepare
S1_GROUP=generic-clause-repeat S1_SECONDS=180 S1_THREADS=32 S1_ENUM_THREADS=16 PYTHONDONTWRITEBYTECODE=1 python3 agents/path_merge_call_support/fuzz-seq-s1-tools/run.py export E0-bare-load E0-bare-store
PYTHONDONTWRITEBYTECODE=1 python3 agents/path_merge_call_support/fuzz-seq-s1-tools/analyze.py generic-clause-repeat
make solve SOLVE_TARGETS='solve-LOAD solve-STORE' -j 2 THREADS=16 OUTER_TIMEOUT=120s SOLVE_TIMEOUT=110s
```

本轮按 TDD 验证了配置不注入通用寄存器、全部阶段不读取旧命令、Bare/Sv39/Sv48 场景、超时与资源记录、实际操作数解析、整数的两种样本编码、每类多样本及编码参数域统计。6 项脚本测试和复用解析器的 40 项测试通过；`cargo fmt --all -- --check` 与 `git diff --check` 通过。

最终验收尚未通过：`make solve-MRET` 以及上述 `make solve` 的 LOAD/STORE 均返回错误，原因都是 `zext_decode` 译码回环返回 `Poison`。LOAD/STORE 分别保留了 148、130 条部分用例；日志在 `output/log/MRET.log`、`output/log/LOAD.log`、`output/log/STORE.log`。没有通过固定机器码或限制寄存器取值绕过该错误。

来源 IR 与 E0 配置从 `../replay-p0/output/ecfg4b/` 只读加载，E2 配置从 `../isla-sym-config/output/fuzz-step6a/E2.toml` 只读加载。此前仍使用固定机器码的 `merged/` 日志仅作历史证据，不能作为通用符号指令的实测数据。
