# ecfg4b 新模型的精确位组合数（2026-11-07）

**四场景已重新导出并完成精确计数；122 条路径的双向内存证明全部通过，共 244 个查询，无失败。** 新值均低于旧 F16 值。旧值只适用 Svnapot、Svpbmt、非叶保留位三个补丁之前的模型；本轮不要求新旧相等。

| 场景 | 旧精确值（补丁前 F16） | 新精确值（ecfg4b） | 新值／旧值 |
| --- | ---: | ---: | ---: |
| Sv39 LOAD | `332144680109393789376138014863778140` | `5514120510135610817624373165828855` | 0.0166015620311 倍 |
| Sv39 STORE | `83036170028299945185146712422637916` | `1378530133032885303540753485488923` | 0.0166015620971 倍 |
| Sv48 LOAD | `5704808353133930814591640390286476702485901468` | `23677182437521065801180778230445315411080560` | 0.00415039050777 倍 |
| Sv48 STORE | `1426202088299825319259236416038502073801699868` | `5919295632992447936312069551708712036685320` | 0.00415039052428 倍 |

整数为精确值，上下界相同；倍数使用十进制高精度除法后保留约 12 位有效数字。机器结果及全部逐路径整数见 [results.json](../../output/exact-count-ecfg4b/results.json)。

本结论按指定四场景的**已完成路径**计数，保留原来的设备排除范围。isarch 原始状态仍为 `partial`、退出码 1、错误数 5/5/7/7；没有改写成 finished，也没有宣称原始执行无错误。执行超时、SMT 超时、终值查询超时、未完成路径和待处理批次数全部为零。

## 为什么变化

路径增加不等于位组合数增加。新模型更细地分出了非法情况，同时给继续遍历和成功访问增加了约束：

- **Svnapot**：N=1 只允许最低层叶 PTE，且 PPN[3:0]=1000；合法时用 VPN 的低 4 位替换 PPN 对应位，形成 64 KiB 映射。高层 N=1 或其他低位编码进入页异常。
- **Svpbmt**：本批 `menvcfg=0`，所以 PBMTE=0，PBMT 非零进入页异常；模型还明确检查 PBMT=11 的保留编码。本轮没有验证 PBMTE=1 的行为。
- **非叶保留位**：非叶 PTE 的 U/A/D/N/PBMT 必须为零；不满足时在读取下级页表前进入页异常。这改变了可继续遍历的 PTE 位组合和对应守卫约束。

这些检查可在 ecfg4b 冻结模型的 `model/sys/vmem_pte.sail`（`pte_is_invalid`、`pte_has_reserved_encoding`）和 `model/sys/vmem.sail`（`pt_walk`）中核对。新完成路径总数比旧模型每个 Sv39 场景多 6 条、每个 Sv48 场景多 8 条；按实际八字节读取次数分组，Sv39 的 1/2/3 次读取各多 2 条，Sv48 的 1/2/3/4 次读取各多 2 条。LOAD 最后多一次数据读取的那组路径数量不变。逐组数据见 [path-comparison.json](../../output/exact-count-ecfg4b/path-comparison.json)。

**内存配置也有差异，倍数不能全部归因于三个补丁。** 本轮严格沿用 ecfg4b 的 `config-xs.toml`，没有替换成旧 F16 配置。实际文本比较发现：旧 `mmio_hole` 排除段被 ecfg4b 的 low_rw、flash、mid_rw、debug、upper_rw、high_rw 六个设备排除段取代，并增加对应 PMA 属性；旧显式 `plat_clint_size` 配置项也已移除。两版均有 harness 排除区。完整差异见 [config-changes.diff](../../output/exact-count-ecfg4b/config-changes.diff) 和 [config-changes.json](../../output/exact-count-ecfg4b/config-changes.json)。这使页表地址和访问地址的可行范围、守卫类划分一起变化。

此外，计数对象仍按每条路径实际被测位确定，模型变化后位布局也会变：最大被测位宽由 Sv39 的 164 位变为 182 位、Sv48 的 218 位变为 243 位。倍数是两版各自口径下的精确总数之比，不能解读为同一完整架构状态全集的保留比例。本轮没有逐补丁 A/B 实验，因此不把总差值强行拆成三个补丁各自的数值贡献。

## 路径数与类数

| 场景 | 旧路径数 | 新路径数 | 旧类数 | 新类数 |
| --- | ---: | ---: | ---: | ---: |
| Sv39 LOAD | 20 | 26 | 2404 | 728 |
| Sv39 STORE | 20 | 26 | 1204 | 380 |
| Sv48 LOAD | 27 | 35 | 6918 | 1122 |
| Sv48 STORE | 27 | 35 | 3510 | 606 |

新四场景合计 **122 路径、2836 类**，与 ecfg4b 的 728/380/1122/606 类、26/26/35/35 路径逐项一致。新导出的路径签名集合和每路径类数也与 ecfg4b 种子目录一致；SMT 和守卫定义均由本轮重新导出，没有沿用旧约束。

## 方法和验证

只数每条路径的被测位组合；其他寄存器位、字节数组等状态只要求存在可行取值，不把它们的赋值数量乘进结果。不同路径最后相加，不对完整架构状态跨路径去重。

逐路径展开守卫定义并检查：全部规范守卫只依赖这些被测位，122/122 通过。因此每个被测位赋值唯一确定守卫类，可以先合并互斥类再精确计数，避免逐类重复处理同一批约束。随后按位化简、拆独立分量，用共享决策图精确计数；隐藏位按“是否有可行取值”消去，使用 Python 任意精度整数。最大单分量节点数 119858，未触及原工具 2000000 节点上限，没有抽样误差。

对**本轮新导出的每一条约束**重新做两个 SMT 证明：

1. 原字节数组约束推出“同地址读取必须同值”的有限一致性约束。
2. 从全零数组出发按每次读取写入八字节，构造显式数组；有限一致性约束保证这个数组满足原约束。

两方向的反例查询均为 UNSAT，即没有反例。Sv39 LOAD/STORE 各 26/26 路径、Sv48 LOAD/STORE 各 35/35 路径全部通过，**证明失败 0**。工具仍严格检查单数组、八字节对齐读取及所有数组用途，不支持的形式直接报错。逐路径证据在各场景 `validation.json`。

旧模型的 256 个小类逐项核对已跳过：补丁改变路径、分支位置和守卫目录，不能直接复用旧类或只按签名匹配。此跳过只影响旧小类对照，未跳过任何新路径的计数、守卫依赖检查或双向内存证明。

5 项原人工小公式测试及 3 项新增汇总测试共 **8/8 通过**。新增测试先失败再修改汇总脚本，覆盖精确求和及倍数、缺失路径拒绝、缺失证明拒绝；日志见 [修改前](../../output/exact-count-ecfg4b/test-summary-before.log)、[通过后](../../output/exact-count-ecfg4b/test-tools.log)。`ruff check`、`cargo fmt --all -- --check` 均通过。没有修改 Rust 生产代码，也没有运行与本次独立离线计数无关的 `make solve`。

原始 24 个错误的路径签名和错误文本与同一 ecfg4b 新模型种子导出一致，详情见 [raw-status-audit.json](../../output/exact-count-ecfg4b/raw-status-audit.json)。来源 ecfg4b 已有逐查询设备排除证明，但本轮没有重新采集这些错误查询，也没有只凭相同文本把它们改记为本轮证明通过。本轮精确值限定为指定已完成路径，不包含设备排除终止。

## 输入、耗时与工具改动

输入只读使用相邻工作树 `../replay-p0/output/ecfg4b/`：`bin/isarch`、`rv64d.ir`、`config-xs.toml`、`count.toml`；导出命令从该批各场景 `done.json` 读取，沿用指令、前态和 SMT 参数。模型版本为 Sail-RISC-V `d79d8b32`，Isla `ae1a3355`。仅确认指定新 isarch、新 IR 的实际路径，没有重新计算哈希。枚举配置 `enumeration.toml` 对应的种子仅用于核对路径和类数，实际约束导出使用原 `count.toml`。

本批四路最多同时运行四个 isarch，全部 `-T 32 --smt-timeout 5 --timeout 890`，外限 900 秒。没有额外单独运行 isarch；单独复跑时应按用户要求设 `-T 64`。离线每场景一个 Python 进程，最多四路；Z3 为本机已有 4.16.0，isarch 动态 Z3 沿用其已有 5.3 库。临时文件、缓存和日志均在本工作树输出目录。

| 场景 | 重新导出约束／秒 | 精确计数／秒 | 双向内存证明／秒 |
| --- | ---: | ---: | ---: |
| Sv39 LOAD | 28.178 | 48.470 | 8.985 |
| Sv39 STORE | 27.108 | 47.234 | 7.784 |
| Sv48 LOAD | 57.860 | 97.509 | 31.988 |
| Sv48 STORE | 71.781 | 95.651 | 22.873 |

四路导出按最慢场景约 71.78 秒；离线计数加证明批次实测 129.50 秒。两阶段执行时间合计约 201 秒，不含准备、阅读和文档整理。所有阶段均远低于单步 40 分钟无进展停止线，没有超时或停止事件。

只读来源工具实际位于 `../exact-count/agents/path_merge_call_support/tools/`（不是该工作树根目录的 `tools/`）。副本放在本树 `output/exact-count-ecfg4b/tools/`：

- `exact_capture.py`：移除 F16 目录和旧二进制哈希绑定；接受指定 ecfg4b 新二进制，读取新命令、新 IR 和原 count 配置；从种子提取新路径签名以导出全部守卫定义；保留原始退出码，检查零超时和新路径／类数完整性。
- `exact_validate.py`：增加显式 `--skip-f16-classes`，只跳过旧类对照，保留原双向内存证明逻辑。
- `exact_summary.py`：改为按新路径／类数与全部新证明核账，读取旧精确值作对照；拒绝不完整批次，取消旧预测均值及无关哈希计算。
- `exact_count.py`、`exact_bdd.py`、`exact_observe.c` 和原 5 项测试原样复用；观察器继续按符号名定位，没有改地址常量。新增 `run_offline.py` 保存阶段耗时和退出码，新增 3 项汇总测试。

三份修改副本的精确差异见 [tools-changes.diff](../../output/exact-count-ecfg4b/tools-changes.diff)。原工具、旧文档、新 isarch 和新 IR 全部未修改；无 Git 写操作。

## 可复现命令

从 isla-judge 工作树根执行。新导出目录必须不存在；脚本拒绝覆盖已有场景。下面使用 `capture-repro`，不会覆盖本轮 `capture`。

```sh
export PYTHONDONTWRITEBYTECODE=1
export EXACT_BASE="$PWD/output/exact-count-ecfg4b"
export EXACT_SOURCE="$(realpath ../replay-p0/output/ecfg4b)"
export EXACT_CAPTURE="$EXACT_BASE/capture-repro"
export TMPDIR="$EXACT_BASE/tmp"
export XDG_CACHE_HOME="$EXACT_BASE/cache"
export Z3_LIBRARY_PATH="$(brew --prefix z3)/lib"
export PYTHONPATH="$(brew --prefix z3)/lib/python3.14/site-packages"
mkdir -p "$TMPDIR" "$XDG_CACHE_HOME"
cc -shared -fPIC -O2 -I"$(brew --prefix z3)/include" \
  "$EXACT_BASE/tools/exact_observe.c" -o "$EXACT_BASE/observe.so" -ldl
/usr/bin/python3 "$EXACT_BASE/tools/exact_capture.py" \
  --source "$EXACT_SOURCE" --binary "$EXACT_SOURCE/bin/isarch" \
  --out "$EXACT_CAPTURE" > "$EXACT_BASE/capture-repro.log" 2>&1
/usr/bin/python3 "$EXACT_BASE/tools/run_offline.py" "$EXACT_CAPTURE" \
  > "$EXACT_BASE/offline-repro.log" 2>&1
/usr/bin/python3 "$EXACT_BASE/tools/exact_summary.py" "$EXACT_CAPTURE" \
  --old ../exact-count/agents/path_merge_call_support/enumeration-exact-count-results.json \
  --output "$EXACT_BASE/results-repro.json"
```

若只复算本轮已导出的新约束，令 `EXACT_CAPTURE="$EXACT_BASE/capture"`，从 `run_offline.py` 开始即可。它会更新该目录下计数、验证日志和对应结果，不会重新运行 isarch。每个离线阶段外限 2400 秒，每条内存证明单查询上限仍为 30 秒。

```sh
/usr/bin/python3 -m unittest discover -s "$EXACT_BASE/tools"
RUFF_CACHE_DIR="$EXACT_BASE/cache/ruff" ruff check "$EXACT_BASE/tools"
cargo fmt --all -- --check
```

每场景完整 argv、观测环境、原始输出、逐路径 SMT、守卫定义、精确整数及证明均在 [capture/](../../output/exact-count-ecfg4b/capture/)。批次日志：[导出](../../output/exact-count-ecfg4b/capture.log)、[离线计数及证明](../../output/exact-count-ecfg4b/offline.log)、[汇总](../../output/exact-count-ecfg4b/summary.log)。

## 未做与遗留

- 四场景指定口径的精确总数均已完成，无剩余估值、未知总数或失败的内存证明。
- 未输出全部守卫类的逐类精确分布，未重做旧 256 小类对照；总数使用已检查适用条件的合并类计数。
- 未逐补丁切换模型或单独量化内存配置差异的贡献，不能把倍数当成某一个补丁的独立效果。
- 未重新证明 24 个设备排除错误查询；原始 partial/退出 1 保留，计数范围限定为已完成的 122 条路径。
- 未生成全量样本，未做硬件重放、完整架构状态去重、PBMTE=1 验证或生产计数后端集成；未重建 IR/isarch，未修改 Rust，未运行 make solve。
- 本轮全部写入仅限用户指定的输出目录和本文；未改其他工作树、未向 `/home` 写输出、未做 Git 写操作。

## 工具副本入库位置

上文提到的修改副本已入库：[tools/ecfg4b/](tools/ecfg4b/)（`exact_capture.py`、`exact_validate.py`、`exact_summary.py`、`run_offline.py`，以及汇总测试若有）。原 `tools/` 下的 F16 版本不变，用于复现旧结果；复现新结果时按“可复现命令”一节，把其中 `output/exact-count-ecfg4b/tools/` 换成 `agents/path_merge_call_support/tools/ecfg4b/` 即可，其余脚本（`exact_count.py`、`exact_bdd.py`、`exact_observe.c`）复用原目录。
