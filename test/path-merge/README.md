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

`--path-merge-filter '^(C8|C9|C10|D6)-'` 只运行逐事件守卫的四个场景。`--path-merge-filter '^D'` 只选 D 组。默认运行 B64，`--bitvector 129` 选 B129，`--bitvector both` 运行两种位向量实现。每次 property 执行固定 `-T 2`。`--timeout` 给每个 Sail、property、Z3 或形状检查命令设墙钟外限，默认 30 秒。`--scenarios-dir` 可指定独立场景目录。`--plugin` 可选已构建的兼容插件。每个实际运行的场景保留 Sail 编译日志、IR、三种配置、路径 JSON 和日志。

纯 JSON 夹具可用同一个 Z3 运行，无需编译 Sail 或 property。

```sh
python3 -m unittest discover -s test/path-merge
```

## 新增场景

用 `A1-concrete-diff-bits.sail` 的 [完整样例](scenarios/A1-concrete-diff-bits.sail) 起步。编号由 A–H 组字母、组内正整数编号和短英文名组成。源码通常 5–20 行，使用 Sail 标准库和 property 的共用配置。

1. 把输入位写到专用寄存器。在 TOML 的 `inputs` 中按位宽登记这些寄存器。符号条件和影响观测的自由选择都应有对应输入。场景会穷举登记的有限输入域，通常只需几位。
2. 在 `prop` 中执行候选代码，把它的返回值写入 `out_value`，再返回布尔性质。可以用无分叉的独立规格校验候选返回值。复合值在 Sail 里投影成可区别各结果的整数、布尔值或位向量。把要比较的后态寄存器写入 `registers`。这些寄存器在每条完成路径上都应已初始化。
3. 存在特定分组要求时，添加可选的同名 `.shape`。先用 `(declare-const path_x (_ BitVec 1))` 声明观测输入，再给每条期望的合并路径一行谓词。两个合并策略都核对这份形状，谓词排列不限。[D1 形状样例](scenarios/D1-four-fragments.shape)

| 字段 | 意义及默认值 |
| --- | --- |
| `id`、`group` | 来自文件名。显式填写时须一致。 |
| `title`、`intent` | 审阅标题和一句话能力要求。默认使用编号和通用说明，新增用例宜写具体要求。 |
| `inputs` | 观测寄存器名到正位宽的表。默认 `{}`，即没有外部输入。 |
| `observe`、`registers` | 候选返回值寄存器默认 `out_value`。其他后态寄存器默认空列表。 |
| `assertion_inputs` | 失败断言应覆盖的完整输入取值列表。每个取值按 `inputs` 的顺序填写。省略时沿用普通性质判定。 |
| `expect_paths_unmerged`、`expect_paths_merged` | 关闭合并和开启合并的可满足完成路径数。默认 2 和 1。 |
| `must_merge`、`must_not_merge` | 应该合并或分开保留的语义原因。都默认留空，部分分组可同时填两项。 |
| `modes` | 默认 `["off", "recursive", "flat"]`，三种都运行。 |
| `ordered_events` | 要求合并器保留访问次序，也按次序比较选定的寄存器读，默认 `false`。 |
| `ordered_memory_events` | 按次序比较访存事件，默认 `true`。`false` 时比较包含重复项的无序集合。 |
| `register_reads` | 寄存器名到预期读次数的表，默认空表。对每条路径的每个可达输入检查所列寄存器的生效读次数，并与 off 比较字段路径和读值。 |
| `merge_concrete_values` | 省略时使用执行器缺省值。本组场景使用缺省开启的具体值合并。 |
| `status`、`reason` | 默认 `ready`。标 `todo` 或 `xfail` 时填写原因。 |

访存事件比较地址、宽度、读写数据、标签及访问类型。遇到抽象内存的读值时，把能决定该字节的自由量登记为输入。C3 把高七位限制为零，将最低位作为输入。C10 检查 `x=1` 恰好有一笔读，`x=0` 的访存序列为空。D6 检查四个路径组的每个可达输入都恰好读一次 `R`。[C3](scenarios/C3-symbolic-memory-read.sail) · [C10](scenarios/C10-load-conditional.sail) · [D6](scenarios/D6-four-register-reads.sail)

## 路径 JSON

运行器使用 `--dump-paths <文件> --scenario-observations` 导出观测。同一条路径中的新增字段与外层 `guard_smtlib` 共用 SMT-LIB 符号。

- `memory_event_guards[i]` 是 `memory_events[i]` 的生效条件，两数组等长，均按执行迹顺序记录。既有 `memory_events` 对象的字段保持原样。
- `register_reads` 按执行迹顺序列出主迹的 `ReadReg`，每项有 `register`、`accessors`、`data` 和 `guard_smtlib`。寄存器读反映执行器发布的访问事件，默认合并策略可折叠重复访问。
- 守卫为 `true` 时，该事件在这条路径的全部可达输入上生效。其余条件可以是由外层 SMT-LIB 声明并约束的布尔别名。条件访存并集中，每一笔读都有自己对应的条件。

设置 `assertion_inputs` 的场景另用 `--dump-assertions` 导出失败断言。Z3 验证失败叶各自可达、守卫互斥，且正常出口与失败域分开。B11 的普通出口只覆盖 `x=1`，一条独立失败叶覆盖 `x=0`。 [B11](scenarios/B11-assert-leaf.sail)

## 读结果

每格显示模式结果和实际完成路径数。Z3 对每个输入核对可完成性及各事件是否生效，证明返回值、选定寄存器和生效事件的观测在该输入下唯一，再和 off 比较。自由量未登记导致非唯一时，该场景报 FAIL。平铺和递归还比较由各条守卫覆盖的输入集合，忽略路径输出顺序。当前 property CLI 没有控制片段到达顺序的开关。

| 结果 | 含义 |
| --- | --- |
| PASS | 性质、观测、路径数和适用的守卫断言均通过。 |
| FAIL | 编译、执行、求解、语义、两策略分组一致性或普通场景断言失败。 |
| XFAIL | 已标记的合并模式只在路径数或形状上失败。其语义和两策略一致性已核对。 |
| XPASS | 已标记的合并模式全部通过。更新标记后再运行。 |
| TODO | 仅显示原因，跳过编译和执行。 |

整次运行存在 FAIL 或 XPASS 时退出 1。入口参数或必需工具文件有误时退出 2。Markdown 可用于逐场景审阅，其中包含源码、预期、实测和诊断。

## 场景索引

编号指向可独立运行的 Sail。D2 是架子保留的占位，D7 检查五个叶子能否共享一个覆盖全域的守卫，D8 要求在同一棵树的不同到达次序下得到相同划分。D4 和 D9 仅改变源码嵌套次序，均用相同的全域谓词验收。

### A 值种类

- [A1 合并两个不同的等宽位向量](scenarios/A1-concrete-diff-bits.sail)
- [A2 读回相同具体整数](scenarios/A2-equal-int.sail)
- [A3 合并后继续消费不同的具体字符串](scenarios/A3-concrete-diff-string.sail)
- [A4 读回不同具体整数](scenarios/A4-distinct-int.sail)
- [A5 比较相同具体字符串](scenarios/A5-equal-string.sail)
- [A6 区分两个符号表达式](scenarios/A6-two-symbols.sail)
- [A7 区分常量位和符号位](scenarios/A7-mixed-bits.sail)
- [A8 读回不同布尔值](scenarios/A8-boolean.sail)
- [A9 辨别不同位宽](scenarios/A9-distinct-width.sail)
- [A10 读取结构体的两个字段](scenarios/A10-struct.sail)
- [A11 读取定长向量的元素](scenarios/A11-vector.sail)
- [A12 读取等长列表的首项](scenarios/A12-list.sail)
- [A13 辨别 Some 和 None](scenarios/A13-option-tag.sail)
- [A14 区分 union 的相同标签与相同负载](scenarios/A14-union-equal.sail)
- [A15 区分 union 的相同标签与不同负载](scenarios/A15-union-payload.sail)
- [A16 区分 union 的不同标签与单位负载](scenarios/A16-union-tag.sail)
- [A17 读取同一构造子的负载宽度](scenarios/A17-union-width.sail)
- [A18 比较同一标签的不同字符串](scenarios/A18-union-string.sail)
- [A19 比较不同枚举成员](scenarios/A19-enum.sail)
- [A20 单臂初始化寄存器](scenarios/A20-init-slot.sail)
- [A21 读回具体与符号整数](scenarios/A21-mixed-int.sail)
- [A22 复用同一个符号值](scenarios/A22-equal-symbol.sail)

### B 控制结构

- [B1 合并两层菱形分叉](scenarios/B1-nested-diamond.sail)
- [B2 单菱形的共同后继](scenarios/B2-diamond.sail)
- [B3 单臂赋值](scenarios/B3-implicit-else.sail)
- [B4 三路 match 共用后继](scenarios/B4-three-match.sail)
- [B5 只在外层一臂再分叉](scenarios/B5-one-inner.sail)
- [B6 臂内提前返回](scenarios/B6-early-return.sail)
- [B7 单臂调用纯函数](scenarios/B7-pure-call.sail)
- [B8 臂内调用写寄存器函数](scenarios/B8-write-call.sail)
- [B9 臂内调用读寄存器函数](scenarios/B9-read-call.sail)
- [B10 两臂执行不同次数的有界循环](scenarios/B10-unequal-loops.sail)
- [B11 失败断言是独立错误出口](scenarios/B11-assert-leaf.sail)
- [B12 调用方捕获臂内异常](scenarios/B12-caught-exception.sail)

### C 状态与事件

- [C1 同一寄存器接收两种值](scenarios/C1-same-register-diff-value.sail)
- [C2 保留不同数量的访存事件](scenarios/C2-different-memory-events.sail)
- [C3 保留符号访存读值](scenarios/C3-symbolic-memory-read.sail)
- [C4 两臂写不同寄存器](scenarios/C4-disjoint-writes.sail)
- [C5 从两臂读取不同寄存器](scenarios/C5-register-read.sail)
- [C6 同地址写不同字节](scenarios/C6-store-same.sail)
- [C7 不同地址写相同字节](scenarios/C7-store-address.sail)
- [C8 两臂从同地址读取](scenarios/C8-load-same.sail)
- [C9 两臂从不同地址读取](scenarios/C9-load-address.sail)
- [C10 只在一个分支读取](scenarios/C10-load-conditional.sail)
- [C11 两笔写的顺序相反](scenarios/C11-memory-order.sail)
- [C12 覆盖局部变量](scenarios/C12-local-reassign.sail)
- [C13 分支内同名 let](scenarios/C13-let-scope.sail)
- [C14 交换独立寄存器的写序后合为一条](scenarios/C14-register-order.sail)

### D 汇合点分组

- [D1 四个片段的字符串按守卫合为一组](scenarios/D1-four-fragments.sail)
- [D2 五个片段汇合](scenarios/D2-five-fragments.sail)
- [D3 三个 I64 片段 3、符号值、7](scenarios/D3-i64-bridge.sail)
- [D4 P("a")、Q(())、P("c") 的分组](scenarios/D4-union-bridge.sail)
- [D5 外层两臂的标签集合分别是 {b,c} 和 {c,d}](scenarios/D5-overlap.sail)
- [D6 四个叶子各自读 R 后合为一组](scenarios/D6-four-register-reads.sail)
- [D7 五个叶子的 a、b、c 按守卫合为一组](scenarios/D7-five-labels.sail)
- [D8 改变五片段到达次序后守卫分组一致](scenarios/D8-permute-five.sail)
- [D9 P("a")、Q(())、P("c") 的分组](scenarios/D9-union-other-tree.sail)

### E 符号模式映射为整数后的返回与使用

- [E1 直接返回 match 选出的整数](scenarios/E1-match-width.sail)
- [E2 直接返回 mapping 正向映射的整数](scenarios/E2-mapping-width.sail)
- [E3 按映射位宽切片并比较两种扩展](scenarios/E3-extend-width.sail)
- [E4 按模式选择 VPN 每级位数后切片](scenarios/E4-vpn-index.sail)
- [E5 从 Bare 提前返回到翻译结果](scenarios/E5-translate-result.sail)
- [E6 同一个宽度同时用于切片和整数比较](scenarios/E6-two-consumers.sail)

[六个场景的开关对照、逐输入结果与拒绝位置](../../agents/path_merge_scenarios_20261119/review-satp.md)

S1–S6、S6 边界、S1 控制及故意写错的规格继续使用 [property 的内层合并索引](../property/README-nested-merge.md)。该索引给出每项的守卫目标与独立运行命令。

A3 在旧缺省下有两条完成路径，标为 XFAIL。缺省开启且字符串比较能直接读带守卫值后，递归和平铺在 B64 和 B129 下都得到一条完成路径，实测 XPASS 后已移除标记。

## F 组 不同位宽的备选值

- [F1 调用者只检查 Ok 标签](scenarios/F1-union-width-tag.sail)
- [F2 解包后检查长度、拼接并扩展至固定宽度](scenarios/F2-union-width-append.sail)

## G 组 有限域算术与具体整数消费者

- [G1 乘加端点的同宽切片](scenarios/G1-affine-slice.sail)
- [G2 独立选择层号和每级位数](scenarios/G2-chosen-slice-size.sail)
- [G3 层号递减循环中的组合下标](scenarios/G3-descending-index.sail)

## H 组 带符号长度的访存

- [H1 读取一或两字节](scenarios/H1-symbolic-read-size.sail)
- [H2 写入一或两字节](scenarios/H2-symbolic-write-size.sail)
