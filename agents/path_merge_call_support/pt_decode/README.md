# 页表样本解码与形状分布交叉检验

这是独立的 Python 3 标准库工具。它读取 [samples v1](../samples.md) 的 JSONL，重建 RV64 `ld rd, imm(rs1)` 的页表路径，为每种形状输出一个具体模板，并逐形状比较分叉与合并样本的计数。它不调用 Isla、Sail、Z3 或任何二进制。

本次两份各 16592 行的输入均得到 **104 种形状，所有形状计数相同**。详细结果见 [交叉检验](out/crosscheck.md)、[分布](out/distribution.md)、[验证记录](status.md)。合并输入有 16570 行 `truncated=true`，因此本结论只覆盖已导出的代表样本。

## 使用

在本目录执行测试：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest
```

将 `FORK_SAMPLES`、`MERGE_SAMPLES` 设为两份输入 JSONL 的路径，再执行：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 pt_decode.py \
  --fork "$FORK_SAMPLES" \
  --merge "$MERGE_SAMPLES" \
  --out out \
  --svrsw60t59b enabled \
  --dirty-update disabled
```

这两个模型开关是必填项。样本 v1 不携带扩展支持表或 `plat_enable_dirty_update`，工具不会猜测。上述取值对应本次核对的 IR；其他实验应使用其实际配置。

默认从 `pre_registers.$instruction` 解码 Sail 的 `LOAD(imm, rs1, rd, false, 8)`。元组字段名称和顺序来自 `sail-riscv/model/extensions/I/base_insts.sail`。如果没有该字段，则接受 `isa_state.$instruction` 中的 `ld x2, -0x8(x1)` 汇编字符串。取址为寄存器值加符号扩展的 12 位立即数，结果按 RV64 回绕；`x0` 为零。

指令无法取得时必须指定以下一种方式：

```sh
# 直接指定虚拟地址
python3 pt_decode.py --fork "$FORK_SAMPLES" --merge "$MERGE_SAMPLES" \
  --out out --svrsw60t59b enabled --dirty-update disabled --va 0x20000000

# 指定取址寄存器与有符号字节偏移
python3 pt_decode.py --fork "$FORK_SAMPLES" --merge "$MERGE_SAMPLES" \
  --out out --svrsw60t59b enabled --dirty-update disabled \
  --va-register x1 --offset=-8
```

显式指定地址时，调用者保证负载仍是 8 字节对齐的 RV64 ld。未知或损坏的自动指令格式直接报错，不自动换用另一个解释。`--va` 与寄存器方式互斥；`--offset` 要求寄存器方式。

退出码：`0` 为形状计数相同；`1` 为计数不同且已生成差异报告；`2` 为输入、解码或文件错误。输入错误包含文件行号；遍历错误包含 `sample_id`，缺单元另列缺失地址。空文件、重复编号、重复 JSON 字段、NaN、未知顶层字段、未知具体值标签均拒绝。寄存器名和结构体成员名沿用样本协议；参与语义解析的结构必须匹配已支持字段。

## 输出

根目录的 `shapes.json`、`distribution.md`、`page_tables.json` 采用 fork 输入；`fork/` 和 `merge/` 各自保存三份报告。所有计数均按输入行统计，不去重具体状态，不对截断行降权。输入流逐行读取，只保存形状聚合、编号集合和代表样本的解码结果，不复制原始样本全集。

| 文件或字段 | 含义 |
| --- | --- |
| `metadata` | 输入文件名、SHA-256、样本数、截断数、模式计数、显式配置、地址覆盖选项、Python 版本、解码器哈希、实测耗时 |
| `shapes.json: shapes` | 按计数降序排列的形状；计数相同按描述性名字排序 |
| `key` | 有效翻译模式、带层号的 PTE 种类序列、叶子层、结果、异常类型、失败原因 |
| `sequence` | 根至终止位置的已读取 PTE；叶子种类带 R/W/X/U，G/A/D 等在 fields 和位掩码中保留 |
| `representative` | 该形状中最小 `sample_id` 的具体路径；同一输入改变行序不影响代表选择 |
| `distribution.md` | 形状计数与占比、结果汇总、叶子层汇总；叶子层汇总包括在叶子处失败的样本 |
| `page_tables.json: page_tables` | 每种形状一个可供模板消费的条目；名字由形状生成，无预设类别名 |
| `satp`、`root_paddr`、`va`、`vpn` | 代表样本的 satp、根物理地址、虚拟地址、VPN 数组；VPN 按低层至高层排列 |
| `entries` | 沿实际路径排序；PTE 后接成功读取的 data；每项有 level、paddr、64 位十六进制 value、role、fields 和位约束 |
| `role` | `pointer`、`leaf`、`invalid` 或 `data`；权限不足或大页未对齐仍为 leaf，以 failure_reason 说明失败 |
| `fields` | V/R/W/X/U/G/A/D、RSW、PPN、reserved、RSW_60t59b、PBMT、N；data 的 fields 为空 |
| `fixed_mask`、`fixed_value`、`free_mask` | 同形状、同层条目值的实际固定和变化位；均为 64 位十六进制串 |
| `paddr_varies` | 该层地址是否在形状内变化；输出的 paddr 仍只是代表值 |
| `context_varies` | satp、根地址、VA、有效权限或 MXR/SUM 是否在形状内变化 |
| `expected` | 代表样本的 result、exception_type、paddr_if_success；异常时最终成功地址为 null |
| `translated_paddr` | shapes 中另记已算出的翻译地址；后续数据访问被拒绝时仍可存在 |
| `termination` | PMA 能证明的提前终止，包含未读取位置的 level、paddr 与证据名；不伪造 PTE 条目 |
| `crosscheck.json` | equal、same、different；每行有完整形状键、双方计数、`delta_merge_minus_fork`，以及输入元数据 |
| `crosscheck.md` | 所有形状的双方计数及差值；不同时列出待调查的可能原因 |

对形状内同层的值求 `and_all` 和 `or_all`：

```text
free_mask   = and_all XOR or_all
fixed_mask  = NOT free_mask（限定 64 位）
fixed_value = and_all
```

因此每个成员都满足 `value & fixed_mask == fixed_value`。这只说明观察到哪些位变过；不能把 free 位任意组合，也不能认为固定的 PPN、数据值或 satp 就是求解器约束。单成员形状的所有位都显示为观察固定，`notes` 明确说明这个限制。

## Sail 语义核对

源码均按工作区根目录定位，SHA-256 见 [验证记录](status.md)。

| PTE 字段 | 绝对位号 | Sail 依据 |
| --- | --- | --- |
| V/R/W/X/U/G/A/D | 0/1/2/3/4/5/6/7 | `sail-riscv/model/sys/vmem_pte.sail:57` 的 PTE_Flags |
| RSW | 9:8 | 同文件顶部布局；不参与 invalid 检查 |
| PPN | 53:10 | `PPN_of_PTE` |
| reserved | 58:54 | PTE_Ext.reserved=4:0，ext 来自 PTE[63:54] |
| RSW_60t59b | 60:59 | PTE_Ext.RSW_60t59b=6:5 |
| PBMT | 62:61 | PTE_Ext.PBMT=8:7 |
| N | 63 | PTE_Ext.N=9 |

`[60:54]` 整段不再统一视为保留位：其中 `[60:59]` 是扩展的软件位。当前 Sail 的 NAPOT 和 PBMT 固定未启用；RSW_60t59b 是否允许由显式配置给定。本次 IR 中 `hartSupports(Ext_Svrsw60t59b)=true`，且支持 Sv39，故这些软件位可以非零。

invalid 的首个原因依次为 V=0、W=1/R=0、N 未启用、PBMT 未启用、RSW_60t59b 未启用、reserved 非零。顺序对应 Sail 短路判断；其他同时成立的位仍完整保存在 fields 中。合法项的 R/W/X 全零即 pointer。**当前 Sail 不额外拒绝指针的 U/A/D 非零**，工具遵循这一点。L0 的 pointer 终止为页异常。

叶子先检查低 `9 × level` 个 PPN 位是否全零，再检查 U/S、SUM、MXR 和读权限，最后处理 A 位。页大小是 `2^(12+9×level)`；大页地址由 PPN 高位、低层 VPN 与页内偏移拼接。D 位不影响 ld。dirty-update 关闭时，A=0 为页异常；开启时必须从 post_memory 核实 A 位写回，未证实的写回失败不猜测。

有效权限遵循 `sys_control.sail::effectivePrivilege` 的 MPRV/MPP；有效 M 态使用 Bare。其他模式从 RV64 satp.MODE 决定：Bare/Sv39/Sv48/Sv57 对应 0/3/4/5 层，PTE 固定 8 字节。分页模式先检查 VA 符号扩展是否合法。

## 边界和限制

- 本目录包含全部 ISA 专用后处理；Isla 核心仍不感知页表、RISC-V 位号或模板形状。
- 仅支持 RV64、对齐 ld、单阶段翻译。Sv32、非对齐或跨页负载、取指/写入、虚拟化、NAPOT、PBMT、非标准 PTE 扩展未实现，不能直接套用。
- 必须有冷页表路径所需的前置字节。工具不重建 TLB、精确事件时序或未观察状态。只依据地址查单元，不把排序最前的内存当成页表。
- 访问异常只有在样本 `pma_regions` 能证明 PTE 或数据地址不可读时才归因。缺失 PMA 不是拒绝证据；不模拟 PMP、设备或其他平台拒绝。此类样本缺单元时明确报错。
- PMA 采用 Sail 的首个包含完整访问区间的区域，检查 readable；本工具限定对齐的普通 ld，不模拟其他属性相关的访存类别。未使用属性保持原协议，只对当前读取需要的字段解释语义。
- 后态寄存器保留在输入中但不做指令执行重放；本任务验证页表形状与导出结果类别的一致性，不检验加载值或全部后态。ret_val 展示文本不作为结果来源。
- 形状计数相同不代表双方具体 PTE 值、地址集合或形状内全部解相同。两侧各自计算 free_mask，可能因代表模型不同而不同。
- `truncated=true` 保留在统计中。一级守卫叶子各有代表，与类内所有具体值完整枚举是两个不同结论。本次只能确认用户提供样本的形状分布一致。
- 工具严格拒绝新格式，后续扩展必须同步代码与测试。没有遇错补零、忽略未知字段、忽略缺单元或调整分类以凑齐计数的路径。

本次只读核对了现有抽象：样本具体值协议、Sail LOAD 参数和原有逐路径脚本。现有 Python 脚本解析的是 SMT 迹，不能表达 JSONL 页表重建，因此本目录新增直接解码模块；没有向核心引入 ISA 依赖。
