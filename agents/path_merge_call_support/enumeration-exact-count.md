# F16 完整位组合的精确计数（2026-11-07）

**四个场景都能算出精确值，无需逐个生成样本。** 本轮得到全部 94 条路径的精确整数；F16 原二进制与当前基线 `fff25fa` 对应的冻结二进制，逐路径结果完全相同。

| 场景 | 路径／守卫类 | 精确位组合数（上下界相同） |
| --- | ---: | ---: |
| Sv39 LOAD | 20／2404 | `332144680109393789376138014863778140` |
| Sv39 STORE | 20／1204 | `83036170028299945185146712422637916` |
| Sv48 LOAD | 27／6918 | `5704808353133930814591640390286476702485901468` |
| Sv48 STORE | 27／3510 | `1426202088299825319259236416038502073801699868` |

机器结果及逐路径整数见 [enumeration-exact-count-results.json](enumeration-exact-count-results.json)。这是 F16 新配置的结果；不能用来替换 F12 旧配置的真值。

## 与 F16 的估计对照

| 场景 | F16 均值 | 本轮精确值约数 | 精确值相对 F16 均值 | 位于 F16 的 95% 近似区间内 |
| --- | ---: | ---: | ---: | --- |
| Sv39 LOAD | 2.843226e35 | 3.321447e35 | +16.82% | 是 |
| Sv39 STORE | 7.327010e34 | 8.303617e34 | +13.33% | 是 |
| Sv48 LOAD | 4.427329e45 | 5.704808e45 | +28.85% | **否：高于上端 1.58%** |
| Sv48 STORE | 1.472013e45 | 1.426202e45 | −3.11% | 是 |

F16 的 Sv48 LOAD 区间为 `[3.2387005788834166e45, 5.6159566917080106e45]`。本轮真值落在该区间之外，说明固定 256 次探测的正态近似区间确实不能当作严格上下界。保留 [F16 原记录](enumeration.md#f16新配置下的重做)，不回写或修饰其估计。

现在四个场景的区间宽度均为零。相比 F16 限时 count 的严格下界，信息增量如下：

| 场景 | F16 已知下界 | 本轮精确值／旧下界 |
| --- | ---: | ---: |
| Sv39 LOAD | 868608 | 3.824e29 倍 |
| Sv39 STORE | 848128 | 9.791e28 倍 |
| Sv48 LOAD | 815364 | 6.997e39 倍 |
| Sv48 STORE | 811268 | 1.758e39 倍 |

按原先的 1300 B／组合换算，四场景仍分别需要约 `4.318e38`、`1.079e38`、`7.416e48`、`1.854e48` B。精确计数可行，全量落盘仍不可行；1300 B 只是沿用的换算系数。

## 计数对象与方法

### 只数被测位，隐藏变量只要求有解

沿用 F12/F16 的口径：每条路径的二级投影覆盖该路径全部被测位，跨守卫类复用同一位布局。其他寄存器位、枚举变量、字节数组等只要求存在可行取值，不把它们的所有赋值乘进结果。不同路径的计数最后相加；这不是对完整架构状态去重后的数量。

设 `b` 是被测位、`h` 是隐藏变量、`C` 是原路径约束、`G_c` 是一个规范守卫类。用户指定的方法是先求 `#{b : ∃h. C ∧ G_c}`，再对互斥类求和。

本轮对 94 条路径逐个展开守卫定义、转成按位布尔表达式，检查所有规范守卫只依赖 `b`。因此，每个 `b` 唯一确定一个规范守卫类，可以先把所有类的和合并：

```text
Σ_c #{b : ∃h. C ∧ G_c} = #{b : ∃h. C}
```

这一步省掉了逐类重复处理相同的大块约束。它依赖实际守卫的按位依赖检查，不以“守卫边际域乘积相等”代替证明。若守卫还依赖未投影位，工具直接报错，不能使用这个等式。

### 先处理内存，再化简和拆分量

F16 的保守 Support 图每路径都是一个分量。共享字节数组和宽操作数会连接大量位，不能直接乘候选分量。

本批约束中的内存读取全部是同一个字节数组上的八字节对齐读取。工具逐项检查读取布局及对齐，精确改写为有限读取的一致性：

```text
读地址 A_i = A_j  ⇒  读值 V_i = V_j
```

对齐的八字节读取，只有同起始地址才可能重叠。这些等式保留真实别名的影响，没有假设页表读取互不别名。

每条路径再做两个 SMT 反例查询，均要求得到 UNSAT：

1. 原数组约束能推出有限读取一致性。
2. 从全零数组开始，按各读取的地址写入对应八字节，得到一个显式数组见证；有限一致性约束能保证该数组满足原约束。

因此，消去整个数组后保留了所有可行投影值。转换遇到其他数组使用方式、未对齐读取或多个数组时直接拒绝，不悄悄丢约束。

随后用 Z3 的 `simplify → bit-blast → simplify` 把位运算转成布尔约束。按实际布尔变量的连通关系拆分量；各分量独立计数后相乘。没有约束的 `k` 个投影位一次乘 `2^k`；不含投影位的分量只检查 SAT，不累计其隐藏赋值数。

### 对剩余分量精确计数

本机 PATH 没有 `ganak`、`sharpSAT`、`d4`、`approxmc`、`kissat` 或 `minisat`。有 Z3，但没有可直接调用的通用精确模型计数接口。本轮没有联网或安装软件。

剩余布尔分量由独立的共享决策图工具计数，见 [exact_bdd.py](tools/exact_bdd.py)。图中相同的剩余约束只计算一次：

- 一个节点按当前位为 0／1 分成两个子问题；相同子问题共用节点。
- 隐藏位用两臂的逻辑“或”消去，只保留投影位能否有见证。
- 投影位的两臂计数相加；跳过的自由位按 `2^k` 乘入。
- 所有计数使用 Python 任意精度整数，没有浮点累加或抽样误差。

按 PTE 间同一位相邻的顺序建图，可以复用地址比较的中间结果。本批最大投影宽度为 218 位；单个分量最多创建 **139649 个决策节点**，不需要访问约 `10^45` 个赋值。节点数达到两百万时工具会报错；本轮未触发。

## 验证与实测

两套冻结二进制各完成 94 条路径的转换和计数；逐路径精确整数全部相同。每套的 94 条路径均通过上述双向内存证明。

F16 已知精确的小路径也逐类核对：Sv39 LOAD／STORE 各 4 路径、54 类；Sv48 LOAD 为 5 路径、86 类；Sv48 STORE 为 5 路径、62 类。合计 **18 条路径、256 个守卫类逐项相同**。核对先检查函数、分支位置、父边和类位序，不能直接比较跨进程的 `record_id`。

另有 **5 项人工小公式测试通过**，覆盖自由位、隐藏变量、分量相乘、位运算、变量顺序及同址读取。`ruff check` 通过，Python 文件已格式化。未改 Rust，不需要构建或修改 Isla。

当前基线冻结二进制的本次单次测量如下。四场景最多同时运行四个进程；isarch 均为 `-T32`、`enumeration_threads=4`。离线 Python 每进程单线程。

| 场景 | 导出约束及守卫定义 | 离线精确计数 | 双向证明及小路径核对 |
| --- | ---: | ---: | ---: |
| Sv39 LOAD | 11.85 s | 10.73 s | 9.89 s |
| Sv39 STORE | 11.32 s | 10.34 s | 8.03 s |
| Sv48 LOAD | 21.33 s | 20.97 s | 27.57 s |
| Sv48 STORE | 19.27 s | 21.27 s | 21.26 s |

这些是本轮运行耗时，不是普遍性能保证。每阶段均远低于 30 分钟停止线。导出复用既有 `ISLA_ENUM_GLUE_DETAIL`，它会附带每路径至多 257 个投影域探测；这些有限诊断不生成完整样本，也不用于本轮精确总数。计数后端不逐个枚举位赋值。

## 输入与复现

工作树基线：`feat/exact-count`，`fff25fac2fcae623008538e63e8168270b8778cd`。本轮只新增本议题文档和独立工具，并在 status.md 追加一行；未改生产代码、配置或 IR，未做 git 写操作。

| 冻结输入 | SHA-256 |
| --- | --- |
| F16 原 isarch | `eff8ee5feed41bfd31041a30f55cb1afed8b52127623bbd98b18d7178118a3f0` |
| 当前基线对应的 isarch | `610df5395219d4202a0dc347d05104737f521562d85dd47a70fbe25d8d31a3db` |
| 新 config-xs.toml | `40d728925731cd7a8d7308b4f1f0b0f61940a79881ad4955780c48a366704129` |
| rv64d.ir | `c0e4661a73888c56438a6f76059370667d141a026502d0511291586067bd31c0` |

isarch 沿用冻结的 Z3 `5.3.4.0 / 1fd1d3613`；离线转换与证明使用本机 Homebrew Z3 `4.16.0` 及其已有 Python 绑定。配置、IR、两份二进制及 F16 预测报告已只读复制到本工作树的输出目录。所有新增产物、日志和缓存均在本工作树 `output/exact-count/`；不往 `/home` 写输出。

### 直接复算已有约束

以下命令在本工作树根执行。它们不需要重新运行 isarch，也不读取其他工作树。日志使用新的文件名，逐路径结果可重新生成。

```sh
export PYTHONDONTWRITEBYTECODE=1
export Z3_LIBRARY_PATH="$(brew --prefix z3)/lib"
export PYTHONPATH="$(brew --prefix z3)/lib/python3.14/site-packages"
for scene in sv39-load sv39-store sv48-load sv48-store; do
  timeout 1800 /usr/bin/python3 agents/path_merge_call_support/tools/exact_count.py \
    "output/exact-count/current/$scene" > "output/exact-count/$scene-recount.log" 2>&1
  timeout 1800 /usr/bin/python3 agents/path_merge_call_support/tools/exact_validate.py \
    "output/exact-count/current/$scene" > "output/exact-count/$scene-revalidate.log" 2>&1
done
python3 agents/path_merge_call_support/tools/exact_summary.py \
  output/exact-count/current \
  --f16 agents/path_merge_call_support/enumeration-f16-results.json \
  --compare output/exact-count/detailed \
  --output output/exact-count/recomputed-results.json
/usr/bin/python3 -m unittest discover \
  -s agents/path_merge_call_support/tools -p test_exact_bdd.py
```

### 从冻结输入重新导出

[exact_capture.py](tools/exact_capture.py) 复制 F16 输入和参数，逐项校验哈希；[exact_observe.c](tools/exact_observe.c) 转发原 Z3 查询，只复制一级守卫目录首次根查询的断言。观测器检查额外假设全部为 true，防止把部分守卫赋值误当作原路径。它通过已有路径日志关联签名，用二进制符号表定位调用位置，不修改原求解器。

下面使用一个新的输出目录。工具默认使用本机已有的冻结 Z3 动态库；不安装软件。省略 `--binary` 可复算 F16 原二进制。

```sh
export EXACT_REPRO="$PWD/output/exact-count-repro"
mkdir -p "$EXACT_REPRO/tmp"
export TMPDIR="$EXACT_REPRO/tmp"
cc -shared -fPIC -O2 -I"$(brew --prefix z3)/include" \
  agents/path_merge_call_support/tools/exact_observe.c \
  -o "$EXACT_REPRO/observe.so" -ldl
python3 agents/path_merge_call_support/tools/exact_capture.py \
  --source ../isla-enumerate/output/f16 \
  --binary ../isla-enumerate/target_edev/release/isarch \
  --out "$EXACT_REPRO/current" --detail
```

再对新目录执行上一节的 count／validate／summary。工具从 F16 `command.json` 保留指令、前态及 SMT 参数，只替换本地冻结输入、输出目录和时限；每场景完整 argv 和观测环境另存 `command.json`。脚本拒绝覆盖已有场景目录。导出阶段设 1770 秒路径时限、1800 秒进程硬时限。

主要证据：

- 当前基线：[逐路径约束、报告与结果](../../output/exact-count/current/)，各场景 `validation.json` 保存双向证明与小类核对。
- F16 原版本：[完整对照批次](../../output/exact-count/detailed/)，与当前版逐路径整数一致。
- 批次耗时：[导出](../../output/exact-count/current/capture.log)、[计数](../../output/exact-count/current-counts.log)、[验证](../../output/exact-count/current-validate.log)。
- 工具测试：[test-delivery.log](../../output/exact-count/test-delivery.log)；汇总入口：[exact_summary.py](tools/exact_summary.py)。

## 未完成部分与适用边界

- **四场景精确总数均已完成，无剩余估值或未知总数。** 没有输出全部守卫类的逐类精确分布；总数用已证明等价的“先合并类求和”计算，256 个已知小类另作逐项核对。
- 未重算 F12 旧配置。新旧配置的内存范围和排除区不同，不能把本轮整数移作旧配置结论。
- 工具针对本批可化成有限、对齐读取与布尔约束的问题。它不承诺任意 SMT、浮点、量词或任意数组更新都可高效精确计数；超出支持范围直接报错。
- 未把新计数后端接入 Isla 的 count／samples／predict。现有枚举输出和种子逻辑完全未改；本轮没有生成全量样本，也没有以完整状态数量或硬件覆盖率解释这些位组合数。
