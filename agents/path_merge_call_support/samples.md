# E2：样本导出与成员检查

> **注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。**
> 这是 F4 按用户指定放宽的项目内使用范围。主迹保留两臂所有 ReadMem；寄存器读也仍取并集。
> 仅适用于 RAM 与已核实的顺序数组内存回调；设备 Custom 与任意 Constrained 生成器区域保守拒绝。
> 不支持未经审计、会通过内部可变状态执行 IO 或改变内存的读回调。新增此类回调必须先重新核实。


已实现 solve-state 的增量样本导出，以及分叉、合并共同使用的真实 Z3 成员检查。检查发生在完成路径的求解器释放前，早于有限域代表值钉选、encdec 过滤与用例配额筛选，避免额外抽样约束改变成员结论。样本数可能多于最终保留的用例数。此证据证明具体样本的成员关系与结果投影，不证明两个 Sv39 路径全集等价。

## 使用方法

```sh
# 在既有 isarch solve-state 命令前设置环境变量：
ISLA_EXPORT_SAMPLES=/tmp/fork.jsonl target/release/isarch … solve-state --clause=LOAD

# 在另一种模式的既有命令中增加以下选项：
target/release/isarch … --path-merging \
  --check-samples /tmp/fork.jsonl \
  --check-samples-limit 100 \
  --check-samples-report /tmp/fork-in-merge.json \
  solve-state --clause=LOAD
```

`--check-samples` 读取 UTF-8 JSON Lines。`--check-samples-limit N` 只读取前 N 行，N 必须为正整数；省略时读取全部。`--check-samples-report` 可省略，收尾始终在 stderr 输出 `[SAMPLE_CHECK_REPORT] {JSON}`，指定路径时还写入易读 JSON。后两个选项必须同时有 `--check-samples`。进程退出码仍表示执行是否成功；等价性结论须读取报告。被外部强杀的运行没有最终检查报告。

导出以追加方式打开文件，编号从已有最大编号之后继续。进程内共用写端；整行序列化后持互斥锁调用无用户态缓冲的 `File::write_all`。每条完成路径独立落盘，不等待整个运行结束；枚举路径的样本在该路径枚举收尾取得截断标志后追加。不同进程不要同时写同一文件。已有损坏行、模型失败、未知值和内部状态不变量违反不会降级为虚构样本。SIGKILL 前尚未写完的最后一行应由实验方核查，导入不会静默跳过损坏数据。

环境变量由 solve-state 启动时读取一次。函数 CLI 没有新增检查选项；函数交叉检验使用 isla-lib 的同一套 `SamplePath` / `SampleChecker`，见下文。完整 Sv39 命令见 [sv39-pinned.md](sv39-pinned.md)。

## 样本字段

版本为 1；值保留类型和完整位宽，不携带跨路径无意义的 SMT 变量号。

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `schema_version` | 整数 | 当前为 1 |
| `sample_id` | u64 | 文件内唯一编号；并发文件顺序不保证编号递增 |
| `mode` | 字符串 | `fork` / `merge`；全局启用合并或该路径确有合并时为 merge |
| `path_signature` | u64 | 来源路径的既有签名 |
| `class_id` | 整数或 null | E1 一级类编号；不开枚举为 null |
| `truncated` | 布尔 | E1 路径截断或所属类截断；不开枚举为 false |
| `pre_registers` | 名字→具体值 | 初始已初始化的寄存器及目标 pre_state；另有 `$instruction` 绑定完整指令，避免把不同指令混为一个输入 |
| `post_registers` | 名字→具体值 | 终态帧中已初始化的寄存器，包含实际 mcause 等 CSR |
| `isa_state` | 名字→字符串 | 复用既有 `Target::solve_pre_state` 与 FmtVal 的展示输出，与本样本模型同源 |
| `pre_memory` | 单元数组 | 复用原 pre-memory 的首触规则；按字节规范化，内容与稀疏段表示相同 |
| `post_memory` | 单元数组 | 复用原 post-memory 的最终触碰规则；普通写提交，独占写由原事件返回 Bool 决定提交 |
| `result` | 具体值 | 原处理器 ExecutionResult 或函数返回值；保留构造子与全部载荷，不另造正常/异常分类 |
| `ret_val` | 字符串 | 原返回值的既有文本表示，可能包含符号名字；检查使用已具体化的 `result` |

每个内存单元为 `{"address":4096,"value":85,"bytes":1}`。地址为 u64，value 为字节；首次触碰为写时，该字节前置值为 null，与原 pre-memory 相同，不用写数据编造初值。后置值必须具体。

具体值表示：`{"bits":"00101101"}`（最高位在左）、`{"bool":true}`、`{"enum":"Supervisor"}`、`{"unit":true}`、`{"i64":"-1"}`、`{"i128":"-1"}`、`{"string":"…"}`。结构体为 `{"struct":{"字段":值}}`，构造子为 `{"ctor":"名字","value":载荷}`，向量和列表分别为 `{"vector":[值]}` / `{"list":[值]}`。名字由 Sail 解码得到；结构体不能仅凭单字段显示文本还原，因此检查保留完整类型结构。长位串直接使用 SMT 位串，不压缩到执行器的固定 BV 容量。

下面是一个缩小寄存器集合的格式示例；实际导出保留完整集合：

```json
{"schema_version":1,"sample_id":0,"mode":"merge","path_signature":42,"class_id":0,"truncated":false,"pre_registers":{"r0":{"bits":"00000000"}},"post_registers":{"r0":{"bits":"00000001"}},"isa_state":{"r0":"8'h00"},"pre_memory":[{"address":4096,"value":85,"bytes":1}],"post_memory":[{"address":4096,"value":85,"bytes":1}],"result":{"ctor":"Retire_Success","value":{"unit":true}},"ret_val":"Retire_Success(())"}
```

E1 的 `class_cap`、`path_cap` 原样生效；每个解的回调拿到该解尚存活的完整模型，寄存器、内存、返回值都从这个模型取值，不重用路径代表状态。原来的 `merge_enumeration` JSON 结构不变。关闭样本且关闭枚举时不增加模型查询和输出字段。

## 检查与报告

每个样本在原路径求解器上建立 push/pop 保存点，绑定全部样本前置寄存器与完整指令。对每次内存读的小端字节，断言地址和值同时匹配样本前置单元中的某一项；相邻地址关系仍保留在原表达式中。UNSAT 表示不接纳，SAT 后逐项查询后置寄存器、返回值与内存字节的不等式，全部 UNSAT 才记录一致。未改写且与已绑定前置值相同的后置项可直接由该等式证明。后置内存按原事件顺序构造覆盖表达式，独占失败写不覆盖，额外提交的足迹也会检测。Unknown 或错误明确失败，不当成 UNSAT 或一致。回滚恢复原断言、符号表、模型缓存和迹；不为每个样本创建求解器。

历史 E2 / F3 按分类拒绝访存，并以断言禁止条件 ReadMem；该边界自 F4 起修订。最外层提交把完整读 guard 与主迹访存序号保存进帧的合并记录；检查点不会丢失这些条件。`src/isarch/samples.rs` 将条件交给 SamplePath：导出仅采用当前模型下 guard 为真的读取；成员检查只对实际读断言匹配 pre_memory，后置内存及额外足迹检查也沿用同一 guard。未执行臂的地址无需存在于样本 pre_memory。实际执行的每次读仍绑定初始内存，继续保留下面的写后再读限制。两臂同址的数组读约束按各自 guard 生效；不把不活动读的新鲜值写入样本。样本不是完整精确事件序列的输出格式。本轮只适配样本 JSONL，原 solve-state JSON 的 pre-memory/post-memory 消费方尚未按 guard 过滤；并集里不活动读可能引入额外地址，同址时也可能先取到不活动读的任意值。故发生内存读合并后，旧 JSON 的内存展示不能直接作为精确重放见证，应使用本节的样本协议。当前 Sv39 在内存读之前仍受状态写入限制，未出现这种内存读合并。

| 报告字段 | 含义 |
| --- | --- |
| `schema_version` | 1 |
| `sample_total` | 实际读取且参与检查的样本数，已应用 limit |
| `samples` | 每项有 sample_id、accepted_paths、consistent_paths、inconsistent_paths |
| `unaccepted_sample_ids` | 没有任何路径接纳的样本编号 |
| `inconsistent` | `[样本编号, 接纳路径签名]` 数组，按这两个键排序 |
| `completed` | solve-state 成功且既有执行摘要为 finished；受限、未完成的执行不能当成全集结论 |

一致/不一致计数只针对已接纳路径；前者加后者等于 accepted_paths。汇总受互斥锁保护，每条路径的求解查询不占用报告锁。

```json
{"schema_version":1,"sample_total":3,"samples":[{"sample_id":0,"accepted_paths":2,"consistent_paths":2,"inconsistent_paths":0},{"sample_id":1,"accepted_paths":0,"consistent_paths":0,"inconsistent_paths":0},{"sample_id":2,"accepted_paths":1,"consistent_paths":0,"inconsistent_paths":1}],"unaccepted_sample_ids":[1],"inconsistent":[[2,99]],"completed":true}
```

## 规格冲突与范围

1. 原 isarch JSON 没有完整的后置寄存器字段，只有 isa-state 前置展示值、访存和返回值。本次样本从同一终态帧补充 post_registers，mcause 等保留原寄存器含义；没有修改原 JSON 格式。
2. **每次读绑定 pre_memory 与任意写后再读不兼容。** 例如地址 A 先读 0、写 1、再读 1，原 pre_memory[A]=0、post_memory[A]=1；指定的成员规则却要求最后一次读取也为 0，因此同模式导出的这个样本也会不被接纳。`samples_initial_memory_protocol_rejects_read_after_changed_write` 用真实 Z3 固定此事实。实现保留指定规则，没有擅自改为时序内存数组绑定。若后续要覆盖这种负载，必须先修订绑定规格。Sv39 本次 52 个样本全部自洽，不受此反例影响。
3. 区域寄存器读仍沿用访问足迹取并集语义；样本不是精确事件次序的重建。样本仅绑定记录的具体输入、检查记录的后置投影，不证明未观察状态或全集覆盖。
4. 分叉 Sv39 全集和长时间反向 Sv39 实验未运行；按用户要求交给后续实验。已完成真实函数的双向跨模式检查，不把它冒充 Sv39 全集证明。

## 验证与改动文件

所有 Cargo 命令使用离线模式、`smt-thread-interrupt` 和任务给定的 RUSTFLAGS；构建并行 8，测试并行 4，单次命令外包 590 秒上限。日志及现场 HEAD 只读归档在 `/tmp/e2/` 与 `/tmp/e2-head/`，没有 Git 写操作，没有修改 smt.rs 或 smt/。

- TDD 红测首先缺少 SamplePath/SampleChecker 实现；后续红测捕获续写编号重复。两臂/嵌套真实 IR 测试覆盖两种模式的正样本、违反共同前置约束而无人接纳的样本、错误结果样本，以及 JSON 往返和同模式、跨模式自洽。另有内存重放、条件读断言、8 线程共 256 行并发与续写/limit 检查。
- `pte_is_invalid` 沿用 I2–I5 的真实 IR 初始化和常量配置：分叉输出 10 个样本，合并检查 10/10 接纳且一致；合并枚举取 10 个样本，分叉检查 10/10 接纳且一致。每个方向均恰由一条路径接纳。显式真实 IR 测试通过，结果在 `pte-report-false.json`、`pte-report-true.json`。
- 关闭功能：相同 argv 的 MRET 原 JSON **17,179 字节完全一致**；合成 IR 合并函数 stdout **196 字节完全一致**。真实 PTE 合并迹存在既有哈希遍历顺序导致的符号编号变化，不声称该非确定输出跨进程稳定。
- `merge_enumeration` 筛选 4 通过，真实 IR 项另行显式运行；两二进制 cargo check、cargo fmt 与 release 构建通过。
- 完整 isla-lib 单元测试 690 通过、13 失败、4 默认忽略（真实 IR 另行显式通过）；失败集合仍为给定 12 项，加已知 1ms deadline 测试波动；现场 HEAD 同样复现这 13 项。应用层全量 219 通过、1 失败，HEAD 218 通过、同一项失败：`tests/review37_boundaries.rs::整数绝对值极值保持具体与符号结果一致`。没有修改基线失败，也没有新增失败。
- `make -j1 solve-MRET THREADS=8 EXECUTION_LIMITS_CONFIG=/tmp/e1/enabled.toml` 启用导出冒烟：退出 0，4 个生成用例、4 个枚举解、4 行样本；既有摘要含 1 条 unfinished，status=partial，不能把 MRET 冒烟称为完整覆盖。关闭功能的 HEAD 字节对照也含该状态。
- Sv39 短测、52 个样本全量自检与 1040 行吞吐检查见 [sv39-pinned.md](sv39-pinned.md)。

| 实际改动文件 | 原因 |
| --- | --- |
| `isla-lib/src/executor.rs` | 公开 samples 模块 |
| `isla-lib/src/executor/samples.rs` | 样本格式、保类型模型物化、增量成员检查、并发写端与报告、真实 Z3 单测 |
| `isla-lib/src/executor/merge_enumeration.rs` | 保留原接口，增加每解完整模型回调 |
| `isla-lib/src/executor/region_merge.rs` | 在 guard 信息扁平化前断言无条件内存读不变量 |
| `isla-lib/src/executor/tests/region_merge_tests.rs` | 合成两臂/嵌套及真实 pte 双向检查，共用原执行器测试辅助 |
| `src/isarch/mod.rs` | 声明 solve-state 样本适配模块 |
| `src/isarch/samples.rs` | 选项校验、单次运行共享写端/检查器、既有寄存器状态适配与报告收尾 |
| `src/isarch/exec.rs` | 完成路径释放 solver 前调用检查器及每解样本物化；保持旧 JSON |
| `src/isarch_main.rs` | 沿用原选项写法注册并传递 check-samples、limit、report |
| `agents/path_merge_call_support/samples.md` | 字段、使用方法、证据及冲突 |
| `agents/path_merge_call_support/sv39-pinned.md` | CSR 位/类型核实、完整实验命令及短测结果 |
