# F9：完整位组合的可插拔样本后端

三个后端消费同一次枚举、同一个已物化模型。样本编号由共享写端分配；不分别求解，也不替换未测试位。现有 `ISLA_EXPORT_SAMPLES` 仍选择普通 v1 JSONL；TOML 可同时启用三个后端。count 模式不打开样本后端。

```toml
[execution_limits.merge_enumeration]
enabled = true
mode = "samples"
class_cap = 512
path_cap = 256
sample_stride = 1
enumeration_threads = 4

[[execution_limits.merge_enumeration.outputs]]
format = "v1_jsonl"
path = "samples.jsonl"

[[execution_limits.merge_enumeration.outputs]]
format = "compact_jsonl"
path = "compact.jsonl"

[[execution_limits.merge_enumeration.outputs]]
format = "binary"
path = "samples.bin"
```

相对路径基于运行目录。任务运行目录必须选 `/data1` 下的 output/ 或 scratchpad。输出格式名、必需路径、重复格式、重复路径及未知配置键均会校验。已有 v1 文件仍能续写编号；紧凑文本和二进制必须使用新文件，拒绝覆盖或无依据地拼接旧结果。不要把环境变量的 v1 路径与 TOML 的 v1 后端重复配置。

## 共同的类骨架与增量

每个守卫类有一份完整 v1 样本骨架，类内每个被导出的位组合有一个增量。所有增量均相对同一份不可变骨架，不是相对上一行。

| 字段 | 含义 |
| --- | --- |
| `compact_schema_version` | 1，与 samples v1 和枚举版本独立 |
| `path_signature/class_id` | 原始路径签名及最终规范类号；非枚举样本的类号为 null |
| `guard_assignment/tested_slices` | 原枚举的守卫赋值及片段布局，含原有符号命名空间 |
| `solution_count` | 本类实际导出的位组合数 |
| `skeleton` | 本类第一条完整 v1 样本，包括最终截断状态 |
| `increments` | 按类内解号递增的组合集合，每项含 `solution_index/slice_values/delta` |

`delta.set` 是 JSON Pointer 到新值的映射；`delta.remove` 是要删除的对象字段路径。按 RFC 6901 的 `~0/~1` 规则转义字段名。先删除字段，再应用 set。对象递归比较，等长数组逐项比较；数组长度或值结构改变时精确保存整个变化子值。空值、整数类型、位宽、构造子载荷、前后寄存器、内存、ISA 展示文本和返回值全部保留。

这是一种物化后完整样本的数据差分，没有实现此前设计中的 SMT 表达式 DAG 求值器。它仍逐组合求解和物化，保存所有实际变化，不能仅凭守卫位替换骨架来猜测其他字段。骨架不允许在缺少赋值时默认填零。

F8 已先建立全路径计数计划，因此消费者在样本写出时可直接取得最终 `class.truncated || path_truncated`，不再为新输出会话逐样本保存待补写索引。旧 SampleWriter 的原位补写 API 仍保留。

## 紧凑 JSONL

每个守卫类一行，包含上述骨架和该类全部已导出的增量。当前模型只保留在内存中完成差分，增量暂存到输出文件旁的专用目录；类结束后流式拼接成一行并删除该类暂存文件。多个类可并发积累增量，写最终文件时按完整类互斥。异常退出的临时文件和未完成尾行不能视作完整结果。

类内组合不积攒在 Vec 中。Python 读回工具按单个增量值解析，可处理单行内很大的组合集合；内存仍需容纳一个完整样本和一个增量。不同后端的物理行序可不同，比较时按 `sample_id` 对齐。

## 二进制格式

文件头先写 8 字节 `ISLASB1\0`，接着四个 u32 小端整数：版本 1、固定头长度 24、类索引长度 40、JSON 元数据长度。元数据包括 samples/compact 版本、端序、字段表、保留空类号、结束标记和载荷编码名。

每个类先写以下五个 u64 小端字段，再写对应字节长度的载荷：

| 字节偏移 | 字段 | 含义 |
| ---: | --- | --- |
| 0 | path_signature | 原路径签名 |
| 8 | class_id | 规范类号；u64::MAX 表示 null |
| 16 | solution_count | 本类导出组合数 |
| 24 | payload_bytes | 随后的完整类载荷长度 |
| 32 | flags | 0/1 为本类样本最终 truncated |

每类索引严格 **40 B**。载荷先编码类头（含完整骨架），随后编码 solution_count 个增量；没有把 JSON 文本假充二进制载荷。以下类型码递归编码 JSON 值：

| 类型码 | 载荷 |
| ---: | --- |
| 0/1/2 | null / false / true，无附加载荷 |
| 3/4/5 | u64 / i64 / IEEE f64，各 8 字节小端 |
| 6 | UTF-8 字符串，u32 字节长度及原字节 |
| 7 | 数组，u32 元素数及递归编码元素 |
| 8 | 对象，u32 字段数及递归编码的字符串键、值 |
| 9/10 | 纯 0/1 字符串／带 `#b` 的位串，u32 位宽及向低地址写入的低位字节；高位补零并校验，前导零仍按位宽还原 |

文件末尾还有一条 40 B 的结束记录，前四个 u64 为零，flags=u64::MAX。未知版本、错误字段表、非法类型码、载荷长度不符、位串补位错误或缺少结束记录均拒绝读取，不产生替代样本。

40 B 只指每类索引。文件头、结束记录、骨架和全部增量均额外统计，不能称为“每类总共 40 B”。二进制读回按增量流式还原；位串长度和各类组合数仍受相应整数协议字段限制，不静默截断。

## 枚举 JSON 与规模

只使用旧环境变量时保留枚举 schema=2 和原 solutions 数组。显式配置 outputs 时，枚举 schema=3、`solutions_external=true`，各类 solutions 数组不再保存完整组合；solution_count、counted_paths、exported_samples 和守卫赋值仍保留。外置解已在模型回调中交给各后端，类结束时通过计数校验。samples v1 字段没有变化。

这避免 gen JSON 随类内组合数积累全部片段向量；守卫类计划及最终类数组仍随守卫类数增长，不能声称总内存恒定。增量暂存和二进制类载荷暂存也占磁盘，估算落盘空间时必须计入。四个全场景的 count 均在二十分钟停止，完整位组合总数仍未知；本轮不生成估算超过 20 GB 的全场景输出。

## 读回与比较

在仓库根目录运行，输入和输出路径均选择数据盘目录：

```sh
python3 agents/path_merge_call_support/pt_decode/sample_outputs.py \
  --format compact_jsonl --input output/f9/acceptance/compact.jsonl \
  --output output/f9/acceptance/restored-compact.jsonl

python3 agents/path_merge_call_support/pt_decode/sample_outputs.py \
  --format binary --input output/f9/acceptance/samples.bin \
  --output output/f9/acceptance/restored-binary.jsonl

python3 agents/path_merge_call_support/pt_decode/compare_sample_outputs.py \
  --v1 output/f9/acceptance/samples.jsonl \
  --compact output/f9/acceptance/compact.jsonl \
  --binary output/f9/acceptance/samples.bin \
  --report output/f9/acceptance/comparison.json
```

比较器对全部 v1 字段排序后计算完整内容签名，按 sample_id 一一对齐；不删除 ret_val、向量寄存器、内存、编号或其他字段。它为本轮小场景保存每条记录的签名，内存随比较样本数增长；单纯展开工具则按类内增量流式写出。输出文件必须不存在，避免覆盖输入或已有还原结果。

## F11：有预算的二进制流式会话

只配置一个 binary 后端时，默认 `max_output_bytes=25000000000`（十进制25 GB）。也可以显式设置该字段；显式预算要求只配置 binary，且 `sample_stride=1`。多后端 F9 会话保留原格式和逐类暂存方式。有界会话使用二进制 schema=2；samples v1 的字段及含义不变。预算至少1024字节，以容纳正常协议头尾。

```toml
[execution_limits.merge_enumeration]
enabled=true
mode="samples"
class_cap=9223372036854775807
path_cap=9223372036854775807
sample_stride=1
enumeration_threads=4
max_output_bytes=25000000000
[[execution_limits.merge_enumeration.outputs]]
format="binary"
path="samples.bin"
```

### 小块提交与精确预算

复用 F9 的完整样本物化、JSON Pointer 差分及 typed-json-v1 编码。每个活动类最多缓冲256个组合，或达到256 KiB增量后提交一个完整块；每60秒也提交尚未满块的缓冲。每块仍为40 B索引＋完整骨架＋相对该骨架的增量，不经过磁盘文本暂存，也不等待整个类结束。骨架随块重复，略增空间，换取有界缓冲、持续写出及正常预算停止。

接纳每条组合之前，在同一个互斥临界区精确计算其编码字节数，包含新块的骨架／索引、新路径／类的最终汇总空间、所有待提交缓冲，以及正常结束标记。无法容纳时整条拒绝，不接受半条、不丢弃此前已接纳的组合。并发线程共享同一额度。预算只计二进制主文件（含其所有协议开销）；配置、stderr、gen JSON 和人类可读汇总另计。

schema=2 继续使用8字节 magic 和24字节固定头，版本数字改为2，头内说明新载荷布局。普通块索引 flags=0/1，含义是块内骨架原始 truncated；骨架额外携带 `path_nonce`，区分同签名重复会话。相同 path_nonce/class_id 可有多个块，类内 solution_index 连续且唯一。守卫赋值和片段布局仍在 gen JSON，不依赖其还原完整 v1 样本。

### 结束汇总与截断语义

路径／类是否截断要到生成结束才知道，不能在写块时提前宣称完整。schema=2 在全部普通块之后写 flags=2 的40 B汇总索引，再写定长小端汇总载荷：

- 四个 u64：停止原因（0正常、1 output_budget、2 no_progress）、已接纳组合总数、有样本的路径数、有样本的类数。
- 每路径四个 u64：path_nonce、path_signature、组合数、path_truncated。
- 每类四个 u64：path_nonce、class_id、组合数、class_truncated。
- 正常40 B文件尾：前3个u64为0，第4个为汇总索引偏移，flags=u64::MAX。

读回先从固定文件尾定位汇总，再逐块展开；最终样本 `truncated = path_truncated || class_truncated`，与 v1 原定义一致。完整结束文件才有最终截断语义，缺少汇总或正常尾的文件明确拒读。最终汇总、文件尾和全部已接纳组合均在预算内；并不靠截断文件或捕获 I/O 错误补救。

旁置 `samples.summary.json` 包含组合数、实际字节数、上限、truncated、reason、每路径组合数（包括未能写出组合的路径）。正常业务停止不会成为执行 panic。每60秒 `MERGE_ENUMERATION_PROGRESS` 输出组合数、已编码／提交字节数、已知总量下界和上限；下界不伪称完整总数。连续60分钟组合数不增长，或检测到同目录 `samples.stop`，会请求正常停止，原因为 no_progress。收尾后停止监控线程。

### 随机读回

读回工具同时支持 schema=1/2。可均匀无放回抽100个组合，只读取命中块，避免把几十GB全部展开成v1：

```sh
python3 agents/path_merge_call_support/pt_decode/sample_outputs.py \
  --format binary --input output/f11/sv39-store/samples.bin \
  --random 100 --seed 11 --output output/f11/sv39-store/random100.jsonl
```

抽样依据组合序号而非块序号，避免偏向小块。展开的每条仍是普通 samples v1，可直接交给既有 pt_decode 和 --check-samples；只根据结束汇总补齐 truncated，不更改代表值、内存、寄存器或结果。
