# P1 实施与验证记录（2026-11-06）

结论：实现完成。26 项 unittest 通过；真实 fork、merge 输入各 16592 行，均解码为 **104 种形状，104 种形状逐项计数完全相同，差异为零**。最终全流程 **49.615 秒**，退出码 0。

入口：[使用说明与限制](README.md)、[分布](out/distribution.md)、[交叉检验](out/crosscheck.md)、[机器报告](out/crosscheck.json)、[模板数据](out/page_tables.json)。实施方案见 [plan.md](plan.md)。

## 修改边界

只新增本目录中的解码器、测试、文档与聚合产物。保留任务开始时 `status.md`、`docs/RESULTS.md` 和两个 Rust 文件的未提交修改；没有改 Rust，没有构建二进制，没有 Git 写操作。上级路径的状态表不在用户允许范围，故不更新；本文件是 P1 的本轮验证记录。

收尾检查时，目录外另有更多未提交改动出现，包括上级 plan 和若干 Rust 文件。本任务的全部写操作仍只针对本目录，没有处理这些并发变化。

解码器按 samples v1 的具体值协议读取；模式、根地址和 VPN 均来自样本，没有写死 Sv39 根地址或 x1。模板只保存每形状代表，不复制 33184 行原始样本。

## 测试先行

1. 首先写 18 项行为测试，运行 `python3 -m unittest`，因尚无 `pt_decode` 模块而红测。
2. 实现解码器后，18 项通过。真实样本首跑 104 对 104、逐形状计数相同，耗时 27.269 秒。
3. 扩充有效权限、Sv48/Sv57 完整遍历、A 位写回、输出结构和 CLI 差异报告用例。
4. 新增“未参与遍历的未知具体类型仍报错”的红测，确认初版缺少完整具体值标签校验；补充校验后最终 **26 项通过**。
5. 输入校验改变后重新完整处理两组真实样本；旧时间只作为历史记录，交付产物采用最终 49.615 秒运行。

最终测试命令，在本目录运行：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest
```

结果：`Ran 26 tests ... OK`，Python 3.13.9。覆盖模式和 VPN、所有位号、无效原因优先级、扩展开关、指针、叶子、大页、权限、符号立即数、小端字节、缺单元、PMA 提前终止、结果矛盾、变化位掩码、稳定代表选择、严格 JSONL 及 CLI 相同/不同报告。

## 真实数据验证

输入为任务给定 scratchpad 内的 `x_fork/samples.jsonl`、`x_merge/samples.jsonl`，只读。命令在本目录执行，`FORK_SAMPLES`、`MERGE_SAMPLES` 指向这两个原始文件：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 pt_decode.py \
  --fork "$FORK_SAMPLES" --merge "$MERGE_SAMPLES" --out out \
  --svrsw60t59b enabled --dirty-update disabled
```

| 检查 | fork | merge |
| --- | ---: | ---: |
| 输入行数 | 16592 | 16592 |
| 形状数 | 104 | 104 |
| Retire_Success | 7744 | 7744 |
| E_Load_Access_Fault | 5186 | 5186 |
| E_Load_Page_Fault | 3662 | 3662 |
| truncated=true | 0 | 16570 |
| 读取、校验与聚合耗时 | 24.930 秒 | 24.653 秒 |

总耗时包含两侧处理与全部输出写入：49.615 秒。没有解码失败或静默跳过样本。两份输入哈希、配置、耗时、Python 版本和解码器哈希写入机器报告。

| 对象 | SHA-256 |
| --- | --- |
| fork 输入 | `60a6f8a443e7232de4aba56a6b1dd9105e66d9f7e6bc20edd2c5d7609f341995` |
| merge 输入 | `705ac5ba0eb07f4255716fab9a358083f7857e473cf7a8fe886232583440d120` |
| 本次解码器 | `4d5a482b9c86aabb2cfec15e09a84b4c217ba4a04989dddaca0873843c874981` |

额外核对生成的全部 208 个模板：各模式计数和均为 16592；模板名与形状名对应；代表值满足固定掩码；固定/变化位掩码互斥且并集为 64 位；仅成功模板具有 `paddr_if_success`；机器报告 104 项 same、0 项 different。输出内记录的解码器哈希与当前文件一致。

## 分布概要

按结果与主要失败原因汇总，双方完全相同：

| 类别 | 计数 |
| --- | ---: |
| 4 KiB 叶子加载成功 | 6912 |
| 2 MiB 叶子加载成功 | 768 |
| 1 GiB 叶子加载成功 | 64 |
| 翻译后数据地址被 PMA 拒绝 | 5152 |
| 下层 PTE 地址被 PMA 拒绝 | 34 |
| A=0 且平台关闭自动更新 | 2592 |
| 叶子缺少加载权限 | 324 |
| 保留位非零 | 212 |
| L0 仍为指针 | 144 |
| N 非零、扩展未启用 | 106 |
| PBMT 非零、扩展未启用 | 106 |
| 大页未对齐 | 72 |
| V=0 | 53 |
| W=1/R=0 | 53 |

最大 8 个形状均为 `L2 pointer → L1 pointer → L0 leaf → Retire_Success`，按 R/W/X 的四种可读组合与 U 的两种取值细分，**每个 864 条**，合计 6912。之后的 8 个形状采用同样的 4 KiB 叶子权限划分，但数据读取被 PMA 拒绝，**每个 576 条**，合计 4608。完整形状表见输出，不以汇总代替交叉检验键。

## Sail 核对证据与可复用发现

本次 Isla 工作树 HEAD 为 `a8314e054d9caf9244ac7a69323ba5794c79068d`，分支 `feat/postprocess-enumeration`。只读核对的 Sail-RISC-V HEAD 为 `4f2ac293654a02db26dac5055be7f93fd6e3141e`；其工作树有既有修改，因此另记实际读取文件哈希。没有重置或修改其内容。

以下路径均以整个 isla-runner 工作区根目录为基准：

| 读取对象 | SHA-256 |
| --- | --- |
| `sail-riscv/model/sys/vmem_pte.sail` | `41def837993e7535c12e8ac04bba4d8f11fe713148073dad598cd1f19d294638` |
| `sail-riscv/model/sys/vmem.sail` | `fb7e8842da809aff9bfa50af44871cab67a02b3d436e3682fa7c80c1ca0e25ea` |
| `sail-riscv/model/sys/pma.sail` | `c7d3c92e9f3a12ff2ac36c181f13913081ae1148037a33a459bced07ac8bca8c` |
| `isla/.worktrees/memory-consistency/rv64d.ir` | `c0e4661a73888c56438a6f76059370667d141a026502d0511291586067bd31c0` |
| `.worktree/mmu-symbolic-experiment/symbolic/config.toml` | `c91fd405d69dd0f0d0f171fe9fcd369d63245103bc4910b9881bb5ea92469301` |

已确认事实：

- PTE_Ext 的相对位 `[6:5]` 对应 PTE 绝对位 `[60:59]`；真正 reserved 为 `[58:54]`。不能把 `[60:54]` 全部当作必须为零。
- 当前 Sail 固定禁用 NAPOT、PBMT；Svrsw60t59b 则取决于支持配置及 Sv39 是否启用。读取的 IR 将此扩展支持定为 true，并将 `plat_enable_dirty_update` 定为 false。配置文件中同名 const primop 不能替代 IR let 的核实。
- `pte_is_non_leaf` 只检查 X/W/R 全零。当前模型不额外拒绝指针的 U/A/D 位；L0 指针才在遍历中失败。
- 当前 Sail 的顺序是 invalid → pointer/leaf → 大页对齐 → 权限 → A/D 更新；因此失败归因使用首个实际检查失败的原因。
- pre_memory 按地址排序，成功样本的数据地址可能在根 PTE 之前。不能依赖数组次序或把前几个 8 字节单元直接当作各层 PTE。
- 缺少下级单元可能是读之前的 PMA 拒绝；仅凭样本的异常类型不足以证明提前终止。本次所有此类缺失均由样本 PMA 证明。

这些发现保存在本目录，遵守用户只准修改本目录的边界。

## 不确定之处与结论边界

本次证明的是 **两份已给定代表样本的形状计数一致**。合并的 16570 个截断标记不被删除，也不解释成一级类丢失或已证明完整；本工具没有从枚举运行日志独立验证一级类覆盖。

free_mask 来自样本间实际变化。单形状中的字段相关性、未观察值和完整求解约束未知；模板不保证自由位的任意组合可行。双方具体代表模型及掩码可不同。

Sv48/Sv57、Bare、MPRV、权限和 A 位写回有构造测试；真实数据仅覆盖给定的 S 态 Sv39 ld。工具不模拟 PMP、TLB、设备、非对齐负载或写回失败；遇到这些影响且证据不足时直接报错。详细支持边界见 README。
