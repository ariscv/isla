# Path merge 场景测试

[scenarios/](scenarios/) 下每个 `.sail` 文件定义一个独立场景。文件开头的 Sail 注释是 TOML 元数据，下面是可编译的 Sail。添加守卫断言时，再放一个同名的 `.shape`。这些场景复用 property 的 Sail 插件、`--expect-paths`、`--dump-paths` 和 [守卫检查器](../property/include/check_paths.rb)。既有 S1–S6 用例、原命令和设计依据见 [内层合并验收](../property/README-nested-merge.md)及[骨架审核](REVIEW.md)。

## 运行

在 Isla 工作树根目录运行。使用 Python 3.11+、Ruby、Sail、与 Sail 匹配的 Isla Sail 插件、官方 Z3 动态库和命令行程序。以下命令把构建和结果放在工作树的 `output/`。本仓可把 `scenario_out` 指到数据盘上已有的输出目录。

```sh
scenario_z3="$HOME/.local/opt/z3-official-d6c9b4fbb"
export LIBRARY_PATH="$scenario_z3/lib"
export LD_LIBRARY_PATH="$scenario_z3/lib"
export PATH="$scenario_z3/bin:$PATH"
scenario_out="$PWD/output/path-merge-scenarios"
make -C isla-sail
CARGO_TARGET_DIR="$scenario_out/target" cargo build --locked --bin isla-property --bin isla-property129
python3 test/path-merge/run_scenarios.py --bitvector both \
  --property-bin-dir "$scenario_out/target/debug" \
  --output-dir "$scenario_out/runs" --markdown "$scenario_out/scenarios.md"
```

`--path-merge-filter '^D'` 只选 D 组。默认运行 B64，`--bitvector 129` 选 B129，`--bitvector both` 运行两种位向量实现。每次 property 执行固定 `-T 2`。`--timeout` 给每个 Sail、property、Z3 或形状检查命令设墙钟外限，默认 30 秒。`--scenarios-dir` 可指定独立场景目录。`--plugin` 可选已构建的兼容插件。每个实际运行的场景保留 Sail 编译日志、IR、三种配置、路径 JSON 和日志。

## 新增场景

用 `A1-concrete-diff-bits.sail` 的 [完整样例](scenarios/A1-concrete-diff-bits.sail) 起步。编号由 A–D 组字母、组内正整数编号和短英文名组成。源码通常 5–20 行，使用 Sail 标准库和 property 的共用配置。

1. 把输入位写到专用寄存器。在 TOML 的 `inputs` 中按位宽登记这些寄存器。符号条件和影响观测的自由选择都应有对应输入。场景会穷举登记的有限输入域，通常只需几位。
2. 在 `prop` 中执行候选代码，把它的返回值写入 `out_value`，再返回布尔性质。可以用无分叉的独立规格校验候选返回值。复合值在 Sail 里投影成可区别各结果的整数、布尔值或位向量。把要比较的后态寄存器写入 `registers`。这些寄存器在每条完成路径上都应已初始化。
3. 存在特定分组要求时，添加可选的同名 `.shape`。先用 `(declare-const path_x (_ BitVec 1))` 声明观测输入，再给每条期望的合并路径一行谓词。两个合并策略都核对这份形状，谓词排列不限。[D1 形状样例](scenarios/D1-four-fragments.shape)

| 字段 | 意义及默认值 |
| --- | --- |
| `id`、`group` | 来自文件名。显式填写时须一致。 |
| `title`、`intent` | 审阅标题和一句话能力要求。默认使用编号和通用说明，新增用例宜写具体要求。 |
| `inputs` | 观测寄存器名到正位宽的表。默认 `{}`，即没有外部输入。 |
| `observe`、`registers` | 候选返回值寄存器默认 `out_value`。其他后态寄存器默认空列表。 |
| `expect_paths_unmerged`、`expect_paths_merged` | 关闭合并和开启合并的可满足完成路径数。默认 2 和 1。 |
| `must_merge`、`must_not_merge` | 应该合并或分开保留的语义原因。都默认留空，部分分组可同时填两项。 |
| `modes` | 默认 `["off", "recursive", "flat"]`，三种都运行。 |
| `ordered_events` | 测试配置是否要求合并时保留访问次序，默认 `false`。 |
| `merge_concrete_values` | 省略时使用执行器缺省值。D1 显式设置 `false`，覆盖不同字符串仍需分组的情况。 |
| `status`、`reason` | 默认 `ready`。标 `todo` 或 `xfail` 时填写原因。 |

访存场景中的真实 `ReadMem`、`WriteMem` 按事件次序比较，包括地址、宽度、读写数据、标签及访问类型。遇到抽象内存的读值时，把能决定该字节的自由量登记为输入。[符号读值样例](scenarios/C3-symbolic-memory-read.sail) 把高七位限制为零，将最低位作为输入。[不同访存序列样例](scenarios/C2-different-memory-events.sail) 检查两臂的一次写与两次写。访存种类使用具体值。寄存器语义比较使用完成时的选定寄存器值。需要测试寄存器事件顺序的路径准入时，用 `ordered_events` 加计数和守卫断言表达。

## 读结果

每格显示模式结果和实际完成路径数。Z3 对每个输入核对可完成性，证明返回值、选定寄存器和访存观测在该输入下唯一，再和 off 的结果比较。自由量未登记导致非唯一时，该场景报 FAIL。平铺和递归还比较由各条守卫覆盖的输入集合，忽略路径输出顺序。当前 property CLI 没有控制片段到达顺序的开关。

| 结果 | 含义 |
| --- | --- |
| PASS | 性质、观测、路径数和适用的守卫断言均通过。 |
| FAIL | 编译、执行、求解、语义、两策略分组一致性或普通场景断言失败。 |
| XFAIL | 已标记的合并模式只在路径数或形状上失败。其语义和两策略一致性已核对。 |
| XPASS | 已标记的合并模式全部通过。更新标记后再运行。 |
| TODO | 仅显示原因，跳过编译和执行。 |

整次运行存在 FAIL 或 XPASS 时退出 1。入口参数或必需工具文件有误时退出 2。Markdown 可用于逐场景审阅，其中包含源码、预期、实测和诊断。

A3 在旧缺省下有两条完成路径，标为 XFAIL。缺省开启且字符串比较能直接读带守卫值后，递归和平铺在 B64 和 B129 下都得到一条完成路径，实测 XPASS 后已移除标记。
