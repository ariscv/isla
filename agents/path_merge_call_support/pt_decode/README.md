# 页表样本解码与形状分布交叉检验

这是独立的 Python 3.10+ 标准库工具。它读取 [samples v1](../samples.md) 的 JSONL，重建 RV64 `ld rd, imm(rs1)` 和 `sd rs2, imm(rs1)` 的页表路径，为每种形状输出一个具体模板，并逐形状比较分叉与合并样本的计数。它不调用 Isla、Sail、Z3 或任何二进制。

初版 LOAD 的两份各 16592 条输入均得到 **104 种形状，所有形状计数相同**。这些历史产物见 [交叉检验](out/crosscheck.md)、[分布](out/distribution.md)、[验证记录](status.md)，保留初版形状键和名字。本轮 STORE 扩展与 F5 LOAD 回归结果见下文；合并输入包含截断的代表样本，结论只覆盖已导出的样本。

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

没有 Sv48 fork 基线时，可以只解码合并样本：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 pt_decode.py \
  --merge-only --merge "$MERGE_SAMPLES" --out out-sv48 \
  --svrsw60t59b enabled --dirty-update disabled
```

`--merge-only` 与 `--fork` 互斥；不指定单边选项时仍要求同时提供 `--fork`、`--merge`。单边模式在输出根目录生成 `shapes.json`、`distribution.md`、`page_tables.json`，元数据来自 merge，不生成双边交叉检验，也不声称与 fork 相同；成功退出码为 0。请使用独立的空输出目录，避免混入旧的双边报告。错误仍按原规则返回 2。

这两个模型开关是必填项。样本 v1 不携带扩展支持表或 `plat_enable_dirty_update`，工具不会猜测。上述取值对应本次核对的 IR；其他实验应使用其实际配置。

默认从 `pre_registers.$instruction` 解码 Sail 的 `LOAD(imm, rs1, rd, false, 8)` 或 `STORE(imm, rs2, rs1, 8)`。元组字段名称和顺序来自 `sail-riscv/model/extensions/I/base_insts.sail:270`、`:320`、`:327`，并已核对本轮两份 STORE 样本：

| 构造子 | 结构体字段 | 字段含义与样本值 |
| --- | --- | --- |
| LOAD | `tuple#%bv12_%bv5_%bv5_%bool_%i64{0..4}` | imm、rs1、rd、is_unsigned、width |
| STORE | `tuple#%bv12_%bv5_%bv5_%i64{0..3}` | imm=0、rs2=2、rs1=1、width=8 |

因此 STORE 使用字段 2 的 x1 取址，字段 1 是数据来源 x2。如果前态没有该指令字段，则接受 `isa_state.$instruction` 中的 `ld x2, -0x8(x1)` 或 `sd x2, -0x8(x1)` 汇编字符串。取址为寄存器值加符号扩展的 12 位立即数，结果按 RV64 回绕；`x0` 为零。

指令缺失时必须显式指定 `--access load` 或 `--access store`，并指定以下一种取址方式：

```sh
# 直接指定虚拟地址
python3 pt_decode.py --fork "$FORK_SAMPLES" --merge "$MERGE_SAMPLES" \
  --out out --svrsw60t59b enabled --dirty-update disabled --access store --va 0x20000000

# 指定取址寄存器与有符号字节偏移
python3 pt_decode.py --fork "$FORK_SAMPLES" --merge "$MERGE_SAMPLES" \
  --out out --svrsw60t59b enabled --dirty-update disabled \
  --access store --va-register x1 --offset=-8
```

显式指定地址时，调用者保证指令仍为 RV64 ld/sd。工具继续校验已有指令的字段、宽度与访问类型；未知或损坏的指令直接报错，不自动换用另一个解释。`--access` 与已有指令矛盾也报错。`--va` 与寄存器方式互斥；`--offset` 要求寄存器方式。

对齐的访问不需要非对齐平台配置。非对齐 VA 必须显式指定 `--misaligned-access disabled`，工具才按 Sail `vmem_utils.sail::check_misaligned` 在遍历前预测 `E_Load_Addr_Align` / `E_SAMO_Addr_Align`；未提供开关直接报错。`enabled` 下的非对齐拆分访问尚未实现，直接拒绝。

退出码：`0` 为形状计数相同；`1` 为计数不同且已生成差异报告；`2` 为输入、解码或文件错误。输入错误包含文件行号；遍历错误包含 `sample_id`，缺单元另列缺失地址。空文件、重复编号、重复 JSON 字段、NaN、未知顶层字段、未知具体值标签均拒绝。寄存器名和结构体成员名沿用样本协议；参与语义解析的结构必须匹配已支持字段。

## 输出

根目录的 `shapes.json`、`distribution.md`、`page_tables.json` 采用 fork 输入；`fork/` 和 `merge/` 各自保存三份报告。所有计数均按输入行统计，不去重具体状态，不对截断行降权。输入流逐行读取，只保存形状聚合、编号集合和代表样本的解码结果，不复制原始样本全集。

| 文件或字段 | 含义 |
| --- | --- |
| `metadata` | 输入文件名、SHA-256、样本数、截断数、模式计数、显式配置、地址覆盖选项、Python 版本、解码器哈希、实测耗时 |
| `shapes.json: shapes` | 按计数降序排列的形状；计数相同按描述性名字排序 |
| `key` | 访问类型 access（load/store）、有效翻译模式、带层号的 PTE 种类序列、叶子层、结果、异常类型、失败原因；形状名字也增加 load/store 前缀 |
| `sequence` | 根至终止位置的已读取 PTE；叶子种类带 R/W/X/U，G/A/D 等在 fields 和位掩码中保留 |
| `representative` | 该形状中最小 `sample_id` 的具体路径；同一输入改变行序不影响代表选择 |
| `distribution.md` | 形状计数与占比、结果汇总、叶子层汇总；叶子层汇总包括在叶子处失败的样本 |
| `page_tables.json: page_tables` | 每种形状一个可供模板消费的条目；名字由形状生成，无预设类别名 |
| `satp`、`root_paddr`、`va`、`vpn` | 代表样本的 satp、根物理地址、虚拟地址、VPN 数组；VPN 按低层至高层排列 |
| `entries` | 沿实际路径排序；PTE 后接成功访问的 data；LOAD data 取 pre_memory，STORE data 取 post_memory；每项有 level、paddr、64 位十六进制 value、role、fields 和位约束 |
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

叶子先检查低 `9 × level` 个 PPN 位是否全零，再检查 U/S、SUM 和访问权限，最后处理 A/D 位。LOAD 要求 R=1 或 X=1 且 MXR=1；STORE 要求 W=1，MXR 不能赋予写权限。权限与更新规则分别核对 `vmem_pte.sail::check_PTE_permission`、`update_PTE_Bits`，并共用一个遍历流程。页大小是 `2^(12+9×level)`；大页地址由 PPN 高位、低层 VPN 与页内偏移拼接。

dirty-update 关闭时，A=0 为 `accessed_update_disabled`；STORE 的 A=1、D=0 为 `dirty_update_disabled`，均预测对应访问类型的页异常。两位同时为零时先归入 A 位原因。D 位不影响 LOAD。开启更新时，LOAD 核对 A 置位、STORE 核对 A/D 均置位后的完整 PTE 与 `post_memory` 一致，未证实的写回失败直接报错。PTE 读取失败即使发生在 STORE 中，也预测 `E_SAMO_Access_Fault`；预测异常族由原始访问类型决定。

有效权限遵循 `sys_control.sail::effectivePrivilege` 的 MPRV/MPP；有效 M 态使用 Bare。其他模式从 RV64 satp.MODE 决定：0/8/9/10 分别为 Bare/Sv39/Sv48/Sv57，对应 0/3/4/5 层，PTE 固定 8 字节。分页模式先检查 VA 符号扩展是否合法；Sv48 使用 48 位 VA 和四个 9 位 VPN。

## 本轮验证（2026-11-06）

先新增 STORE 行为测试，确认原实现失败后再修改代码。最终 39 项 unittest 通过。测试覆盖 STORE 的元组/汇编取址、异常族匹配、未知输入拒绝、W 权限、MXR/SUM/MPRV、A/D 更新、PMA 读写区分、写前未知值与写后数据、Sv48 四级遍历及非规范 VA、显式平台配置下的对齐异常。原 LOAD 测试保持通过。

STORE 验收命令，在本目录执行：

```sh
SAMPLES_ROOT=/tmp/claude-1005/-data1-baiyifan-workplace-isla-runner/a39d8bcc-3e1b-4db3-8d63-110f0b832032/scratchpad
PYTHONDONTWRITEBYTECODE=1 python3 pt_decode.py \
  --fork "$SAMPLES_ROOT/w_storefork/samples.jsonl" \
  --merge "$SAMPLES_ROOT/w_store/samples.jsonl" --out /tmp/ptstore \
  --svrsw60t59b enabled --dirty-update disabled --va 0x20000000
```

实际两份输入均为 **6920 条**，各 **92 种形状**，92 种逐项计数完全相同，差异为零，退出码 0。fork 无截断行，merge 有 6898 条 `truncated=true`。当前提供的 STORE 样本全部为 satp.MODE=8（Sv39），没有对齐异常；Sv48（mode 9）与 `E_SAMO_Addr_Align` 的支持由上述单元测试确认。

| STORE 结果类别 | fork | merge | 双方各自占比 |
| --- | ---: | ---: | ---: |
| E_SAMO_Page_Fault | 3662 | 3662 | 52.9191% |
| E_SAMO_Access_Fault | 1322 | 1322 | 19.1040% |
| Retire_Success | 1936 | 1936 | 27.9769% |
| E_SAMO_Addr_Align | 0 | 0 | 0% |

LOAD 原数据回归使用相同配置，将输入换为 `$SAMPLES_ROOT/x_fork/samples.jsonl` 和 `$SAMPLES_ROOT/x_merge/samples.jsonl`，输出至 `/tmp/ptload-original`：双方各 16592 条、104 种形状，逐形状计数完全相同，退出码 0。F5 回归命令为：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 pt_decode.py \
  --fork "$SAMPLES_ROOT/x_fork/samples.jsonl" \
  --merge /tmp/f5/enumeration-final-samples.jsonl --out /tmp/ptload \
  --svrsw60t59b enabled --dirty-update disabled
```

F5 双方各 16592 条、104 种形状；与历史同 SHA-256 输入产物比较，除新增 access 字段与名字前缀外，形状键及逐项计数均未改变。F5 已有两种差异仍如实保留，故该命令退出码为 1；本次解码器 LOAD 回归通过，不宣称 F5 双方计数相等：

| LOAD 差异形状（Sv39，L2 pointer→L1 leaf，U=0，superpage_misaligned 页异常） | fork | F5 merge | merge − fork |
| --- | ---: | ---: | ---: |
| leaf_--x_u0 | 16 | 0 | -16 |
| leaf_r-x_u0 | 0 | 16 | +16 |

双方 LOAD 结果类别仍为页异常 3662（22.0709%）、访问异常 5186（31.2560%）、成功 7744（46.6731%）。本轮没有为消除差异调整分类，也不据此推断类内全部具体解相同。

## stride 抽样验证（2026-11-06）

本轮固定 LOAD 编码 `0x0000b103`、VA `0x20000000`、Supervisor、`mstatus=0x0000000a00040000`，`class_cap=1/path_cap=1000000`，`-T 8`。构建与运行产物全部位于工作树 `output/stride-validation/`，使用其中 `scratchpad/target_f6/release/isarch`，未覆盖默认 release 二进制。脚本 `run.sh` 由指定 scratchpad 的 `x_cmd2.sh` 复制并只替换二进制路径；三份 `stride*.toml` 保存完整枚举配置。超过 10 分钟的运行通过 `setsid nohup` 启动并轮询。

Sv39 使用 `satp=0x8000000000080200`，三次均完整访问 **16592 类、20 条路径**，全部 `path_truncated=false`。stride=1 导出 16592 条，stride=7 导出 2382 条，stride=11 导出 1516 条。逐路径从 DFS 序号 0 抽取，样本数与各路径 `ceil(counted_paths/stride)` 的和一致，且与 `MERGE_STATS` 汇总相同。

[集合对照](stride_reports/subset.json)确认 stride=7、stride=11 每条样本的稳定签名都在本轮 stride=1 集合中，缺失为 **0**。签名包括完整前后态内存、结构化 result、截断状态及前后态寄存器与 ISA 状态；只移除 sample_id/class_id/path_signature、冗余 ret_val 展示文本，以及 LOAD 不使用且跨运行代表值可变化的 vl/vtype。JSON 对象键排序后计算 SHA-256；没有屏蔽页表位、数据、地址、异常或 LOAD 权限上下文。这里验证的是此明确归一化下的样本内容子集，不声称所有无关寄存器的具体代表值逐字节相同。

Sv39 同版本、同配置的 [stride=1 分布](stride_reports/sv39-stride1/distribution.md)为 **106 种形状**，[stride=11 分布](stride_reports/sv39-stride11/distribution.md)为 **79 种形状**，遗漏 **27 种**。按两组形状并集计算，每个形状的占比差取 `sample_count/1516 − full_count/16592`，缺失形状计零；[全部差值](stride_reports/sv39-bias.md)的最大绝对值为 **0.523952 个百分点**。最大差来自 Sv39 L2 pointer→L1 pointer→L0 `leaf_r-x_u0` 成功：全量 864/16592=5.207329%，抽样 71/1516=4.683377%。机器结果见 [sv39-bias.json](stride_reports/sv39-bias.json)。

本轮样本代表模型选择与旧二进制不同，因此全量的 106 种不能与历史 104 种混作抽样对照。已同时使用 `--fork` 和 `--merge` 解码两组 Sv39 数据；与旧 fork 的计数差异如实保存在 `output/stride-validation/decode-sv39-{1,11}/crosscheck.*`，退出码 1 表示双方计数不同。抽样偏差始终用本轮 merge stride=1 对照本轮 merge stride=11。

Sv48 使用 `satp=0x9000000000080200`、stride=11，完整访问 **122654 类、27 条路径**，导出 **11162 条样本**，用时 **666 秒**，全部 `path_truncated=false`。样本文件、逐路径输出和 stats 三者计数一致。没有 Sv48 fork 基线，使用 `--merge-only` 解码，15.618 秒得到 **118 种已观察形状**；这不是全域形状数。产物：[distribution.md](stride_reports/sv48-stride11/distribution.md)、[page_tables.json](stride_reports/sv48-stride11/page_tables.json)、[验收汇总](stride_reports/validation.json)。

| Sv48 结果类别 | 样本数 | 占全部样本 |
| --- | ---: | ---: |
| Retire_Success | 5174 | 46.3537% |
| E_Load_Access_Fault | 3467 | 31.0607% |
| E_Load_Page_Fault | 2521 | 22.5856% |

| Sv48 叶子层（包括叶子处失败） | 样本数 | 占全部样本 |
| --- | ---: | ---: |
| L0 | 9125 | 81.7506% |
| L1 | 1338 | 11.9871% |
| L2 | 154 | 1.3797% |
| L3 | 14 | 0.1254% |
| 无叶子 | 531 | 4.7572% |

复核本轮分布（从仓库根目录执行；`RUNS` 指向运行产物目录）：

```sh
RUNS="$PWD/output/stride-validation"
PYTHONDONTWRITEBYTECODE=1 python3 agents/path_merge_call_support/pt_decode/pt_decode.py \
  --merge-only --merge "$RUNS/sv48-11-final/samples.jsonl" \
  --out "$RUNS/decode-sv48-recheck" --svrsw60t59b enabled --dirty-update disabled
python3 "$RUNS/check_subset.py" sv39-1-final sv39-7-final sv39-11-final
```

**这不是随机抽样。** DFS 的周期顺序与字段位相关，各完成路径又从 0 重置；小路径和罕见形状可能被高估或漏采。Sv39 最大差较小并不保证 Sv48 具有相同偏差，缺失 27 种也说明频率误差不能代表完整覆盖。频数以守卫类的代表模型为单位，不是所有具体处理器状态的概率。`class_cap=1` 产生的类内截断按原协议保留，不能解释成守卫类枚举未完成。

验证采用先红后绿：配置、stride 回调与上限、真实样本集合及单边 CLI 均保留红测日志；Python 40 项通过，枚举专项 8 项通过、2 项默认忽略，真实 `pte_is_invalid` 显式测试通过。isla-lib 默认特性全量 **706 通过、既有 12 项失败、6 忽略**，失败项逐名一致；可选 `smt-thread-interrupt` 全量曾复现历史文档已有的 1ms deadline 提前返回 Sat 不稳定项，未修改或跳过该测试。`cargo fmt --check`、isarch 样本专项和 `make -j1 solve-MRET THREADS=8` 通过。

## 边界和限制

- 本目录包含全部 ISA 专用后处理；Isla 核心仍不感知页表、RISC-V 位号或模板形状。
- 仅支持 RV64 ld/sd、单阶段翻译及显式配置下的提前对齐异常。Sv32、非对齐或跨页访问的执行、取指、原子指令、虚拟化、NAPOT、PBMT、非标准 PTE 扩展未实现，不能直接套用。
- 必须有冷页表路径所需的前置字节。工具不重建 TLB、精确事件时序或未观察状态。只依据地址查单元，不把排序最前的内存当成页表。
- 访问异常只有在样本 `pma_regions` 能证明 PTE 不可读、LOAD 数据不可读或 STORE 目标不可写时才归因。缺失 PMA 不是拒绝证据；不模拟 PMP、设备或其他平台拒绝。此类样本缺单元时明确报错。
- PMA 采用 Sail 的首个包含完整访问区间的区域；PTE 读取及 LOAD 数据检查 readable，STORE 数据检查 writable，不要求目标可读。不模拟其他属性相关的访存类别；缺少当前访问所需的属性直接报错。
- STORE 成功写入目标的前态字节可以为 null，保留为未知值，必须有对应的具体 post_memory 字节。读取 PTE 或 LOAD 数据遇到 null、出现未归属内存或缺失写后字节均报错，不补零。STORE 的 data 位掩码描述写后值。
- 后态寄存器保留在输入中但不做指令执行重放；本任务验证页表形状与导出结果类别的一致性，不检验加载值、STORE 源寄存器与写后数据相等或全部后态。ret_val 展示文本不作为结果来源。
- 形状计数相同不代表双方具体 PTE 值、地址集合或形状内全部解相同。两侧各自计算 free_mask，可能因代表模型不同而不同。
- `truncated=true` 保留在统计中。一级守卫叶子各有代表，与类内所有具体值完整枚举是两个不同结论。本次只能确认用户提供样本的形状分布一致。
- 工具严格拒绝新格式，后续扩展必须同步代码与测试。没有遇错补零、忽略未知字段、忽略缺单元或调整分类以凑齐计数的路径。

初版只读核对了现有抽象：样本具体值协议、Sail LOAD 参数和原有逐路径脚本。现有 Python 脚本解析的是 SMT 迹，不能表达 JSONL 页表重建，因此本目录新增直接解码模块。本轮沿用该模块的解析、遍历、聚合和报告结构，以访问类型参数化扩展 STORE；没有向核心引入 ISA 依赖。
