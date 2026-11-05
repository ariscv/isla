# E1：合并路径终态枚举

> **注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。**
> 这是 F4 按用户指定放宽的项目内使用范围。主迹保留两臂所有 ReadMem；寄存器读也仍取并集。
> 仅适用于 RAM 与已核实的顺序数组内存回调；设备 Custom 与任意 Constrained 生成器区域保守拒绝。
> 不支持未经审计、会通过内部可变状态执行 IO 或改变内存的读回调。新增此类回调必须先重新核实。

F4 保留完整带条件内存读记录；枚举不改变主迹。每个解导出样本时用该解的 guard 选择真实发生的读，再按既有首次触碰规则构造内存。仅浏览旧主迹或原 isarch JSON 的访存并集不能恢复逐路径读序列。具体保护条件与事件见 [合并记录](merge-record.md)，样本协议及写后再读限制见 [样本说明](samples.md)。


合并路径在自己的求解器仍存活时进行两级投影枚举。一级按带上下文的守卫分出原始分叉叶子；二级在叶子内用深度优先分裂枚举实际被守卫测试的位片段组合。核心不包含 ISA 字段名、页表格式或页表遍历解码。

## 配置与入口

在 `--execution-limits-config` 指定的独立 TOML 中添加：

```toml
[execution_limits.merge_enumeration]
enabled = true
class_cap = 1024
path_cap = 65536
```

三个字段均可省略，默认分别为 `false`、`1024`、`65536`。上限必须是正整数；未知字段、错误类型、零和负数会在加载时拒绝。`execution_limits.enabled=false` 仍沿用原有规则，不能同时配置其他限制字段。枚举开关与合并开关独立；还需用 `--path-merging` 或 `merge_policy` 开启希望合并的区域。

isarch 将结果放在每个路径 item 的 `merge_enumeration` 字段中。`isla-execute-function` 在该路径的 `Result:` 后输出单行 `merge_enumeration: {JSON}`，`--tree` 模式也保留此行。没有开启枚举时不查询模型、不扫描枚举依赖、不输出字段或附加行。旧 JSON 反序列化时缺少此字段仍有效。

正常完成的处理器结果都参与枚举，包括 fault、page fault、access fault、非法指令等构造子。被路径条件排除、`Run::Dead`、执行器错误或未完成的路径不是正常处理器结果，不作为可行解输出。求解器返回 Unknown 或错误时明确报错，不替换成代表值，也不把它当作完整枚举或 UNSAT。

## 前置核实

| 核实项 | 结论与源码证据 |
| --- | --- |
| (a) 记录归属与回滚 | 原实现已经将记录保存在 `executor/frame.rs` 的 `Frame/LocalFrame.region_merge_records` 中；`freeze_frame`、`unfreeze_frame`、`new_call` 都复制历史。`region_merge.rs` 的 `execute_region` 在克隆帧中推演，`merge_states` 只拼接成功臂的新记录，最后才替换原帧。拒绝不替换原帧，求解器保存点同步回滚。记录不是按 task_id 收集的全局列表。E1 增加稳定编号和父子上下文，并让 isarch 的 ExecuteAs 检查点续执行同时携带帧内合并历史及纯定义区间。 |
| (b) DefineConst 与阻断 | `smt.rs` 的 `add_internal(DefineConst)` 将表达式翻译、化简后存入 `decls`；`Model::get_exp/get_var` 复用该 AST，`Assert` 也经同一符号表翻译。F5 按位分裂 `Extract(hi, lo, Var(symbol))`，模型中的片段值从完整符号取值本地截取；符号可以是派生定义。派生 XOR 符号的两位片段测试得到四个组合，证明没有把 DefineConst 当成自由声明或只枚举守卫真值。不修改求解器 API。 |
| (c) 输出位置 | `src/isarch/exec.rs` 的完成路径 collector 在取得路径模型后物化 `AssemGenJsonItem`；E1 在释放该模型借用后、求解器销毁前调用枚举，并将结果写入可省略字段。代表状态继续沿用既有物化代码。函数入口在 `model_collector` 中枚举后入队，沿用既有输出队列。 |

`ISLA_MERGE_RECORDS` 仍是合并提交时的独立 JSON Lines 观测输出，不是最终路径清单。E1 将其记录格式版本升级为 **2**：`record_id` 在推演前分配，新增 `parent_record` 和 `arm`。回滚尝试消耗的编号可以留下空洞，但不会留下记录；继承记录保持原编号。未启用枚举时，普通路径输出保持不变；显式开启旧记录日志时，该日志按新的记录协议输出上下文。

## 枚举结果字段

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `schema_version` | 整数 | 枚举格式当前为 `1`，与独立记录日志的版本区分 |
| `class_cap` / `path_cap` | 整数 | 本次实际使用的类内解数上限／路径总解数上限 |
| `guard_records` | 数组 | 本路径保存的全部合并记录，包括嵌套记录 |
| `guard_classes` | 数组 | 实际访问并枚举的可行叶子类 |
| `enumerated_total` | 整数 | 已输出的解数，等于所有类的 `solution_count` 之和 |
| `path_truncated` | 布尔 | 路径总上限阻止了尚存的可行解或后续叶子类输出 |

`guard_records` 每项包含：

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `record_id` | 整数 | 本进程唯一、随帧继承的合并记录编号，不是 SMT 符号编号 |
| `parent_record` | 整数或 null | 外层记录编号；根为 null |
| `arm` | 字符串 | 该记录位于父记录的 `then` / `else` 臂；根为 `root` |
| `condition` | 对象 | `symbol` 为迹中的 `vN`，`smt_id` 为变量号 |
| `function` / `branch_pc` | 字符串／整数 | Sail 解码函数名与原 IR 分支位置 |
| `source_loc` | 对象 | 原始 `file/line1/char1/line2/char2`，不伪造未知位置 |

`guard_classes` 每项包含：

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `class_id` | 整数 | 此路径内的发现顺序，从 0 开始 |
| `guard_assignment` | 对象 | 记录编号字符串 → **上下文与守卫合取的布尔值**；上下文不成立的记录规范化为 false，不声称其裸守卫为 false |
| `tested_slices` | 数组 | 本路径全部守卫定义所测试的片段并集，保留记录归属 |
| `solutions` | 数组 | 满足该类和真实路径条件的片段组合，每个组合只输出一个代表模型 |
| `solution_count` | 整数 | 已输出的 `solutions` 数量，不是估算的完整域大小 |
| `truncated` | 布尔 | 类上限或路径总上限阻止了本类尚存解的输出 |

每个 `tested_slices` 项包含 `symbol`（`vN`）、`smt_id`、`hi`、`lo`、`source_loc`、`record_id`。位下标沿用 SMT Extract 的闭区间语义。源码位置来自对应定义事件；原始 IR 标为未知时保留未知位置。沿定义追踪别名，并折叠连续的 Extract；一般派生计算保留其符号，使用其真实 AST。相同片段被不同守卫引用时保留各自的记录归属，可能重复出现在数组中，但分裂用的位集合会去重，不会重复计算组合。

每个解包含：

| 字段 | 类型 | 含义 |
| --- | --- | --- |
| `slice_values` | 字符串数组 | 与 `tested_slices` 按下标对应的定宽 `#b…` 值，最高位在左 |
| `representative.result` | 字符串 | 在这个解的模型下物化的函数／处理器返回值 |
| `representative.inputs` | 数组 | 被选中片段所属的完整符号及其代表位向量；每项为 `symbol/smt_id/value`，未测试的位只保留该模型的一个取值 |

顶层原有 `isa-state`、访存等字段仍代表原路径选出的一个模型；本次没有为每个解复制这些 ISA 输出。每解明确携带自己的返回结果和片段输入代表值。完整 SMT 定义仍来自对应路径迹；仅凭进程外另一条路径的同号 `vN` 不能解释本结果。

下面是单条守卫 `v2 = (v0[0] == 0)` 为真时的简化输出示例：

```json
{
  "schema_version": 1,
  "class_cap": 1024,
  "path_cap": 65536,
  "guard_records": [{
    "record_id": 0, "parent_record": null, "arm": "root",
    "condition": {"symbol": "v2", "smt_id": 2},
    "function": "example", "branch_pc": 0,
    "source_loc": {"file": 0, "line1": 10, "char1": 0, "line2": 10, "char2": 8}
  }],
  "guard_classes": [{
    "class_id": 0,
    "guard_assignment": {"0": true},
    "tested_slices": [{
      "symbol": "v0", "smt_id": 0, "hi": 0, "lo": 0,
      "source_loc": {"file": 0, "line1": 10, "char1": 0, "line2": 10, "char2": 8},
      "record_id": 0
    }],
    "solutions": [{
      "slice_values": ["#b0"],
      "representative": {"result": "true", "inputs": [{"symbol": "v0", "smt_id": 0, "value": "#b00000000"}]}
    }],
    "solution_count": 1,
    "truncated": false
  }],
  "path_truncated": false,
  "enumerated_total": 1
}
```

## 算法与上限语义

1. 从终态帧取记录，检查编号唯一、父链完整且无环。沿父链计算 `ctx(root)=true`，子上下文是父上下文与父守卫对应极性的合取。按照守卫树前序排序，父记录及其子树先于下一棵树；JSON 中记录和片段的顺序仍沿用原帧顺序。
2. 一级类的定义仍是 `p_r = ctx_r ∧ g_r`。DFS 栈保存待访问的分支前缀和已固定的守卫位置；每次复用现有 `check_sat_with`，在原路径求解器上用假设检查前缀，UNSAT 时整支剪去，Unknown/错误直接返回错误。
3. Sat 模型已经证明沿其守卫取值的后续分支都可行，无需逐个重复查询这些所选分支。用 `Ite(g, #b1, #b0)` 和 Concat 将裸守卫打包，一次 `Model::get_exp` 取值，再沿父链规范化：上下文不成立的记录直接赋 false；活动上下文中 `ctx∧g` 等于裸 `g`。依次将每个活动守卫的相反分支压栈，从最深的未访问分支继续。这是以模型作可满足性见证的 DFS 分裂，不是阻断已发现的类。
4. 二级仍使用整条路径全部守卫测试过的片段并集；跨类只扫描一次。对去重的实际位同样做模型引导的 DFS：模型选中的位分支直接走到叶子，相反分支进入前沿，随后在当前守卫类和真实路径条件下剪枝。字段耦合仍由 Z3 保留，例如 `¬(W∧¬R)` 只产生三个组合。一般派生表达式沿用原 AST，不把它当成自由输入。
5. 一级取得的 Sat 模型直接提供该类第一个二级解与完整样本。`class_cap=1` 每类只创建一次 Model；完整输入符号每个只求值一次，所有重复、重叠片段均本地截取。到达类上限时，将剩余 DFS 前沿因式分解后作一次存在性查询；存在未输出解才标记截断，不再抽取额外模型。
6. 求解器中不增加逐类或逐解阻断断言；前沿的大小只与守卫数、被测位数有关，不随已输出类数增长。外层仍使用一个保存点保护模型缓存等状态，正常或错误返回都配对回滚。旧阻断算法仅保存在测试模块中作为独立参照。

完整样本仍逐解物化。访存导出每个事件只查询一次提交条件、基址、完整数据，再本地拆字节；8 字节事件的 `Model::get_exp` 从 24 次降为 3 次。未改写的后态寄存器复用同一模型的前态物化结果，`isa_state` 通过现有 FmtVal 复用已物化的前态，避免再次求值。逐字节参照与旧 ISA 格式化的字节比较覆盖带条件读、宽位向量及地址回绕。

上限按**输出解数**计数。达到数值后额外查询一次：只有确有未输出可行解才设置截断，刚好完整时保持 false。类上限触发后仍尝试其他类；因此类 `truncated=true` 可以与 `path_truncated=false` 同时出现。路径上限触发后可能仍有未发现的类，不能把当前类数当作完整叶子数。类没有片段时每类只消耗一个解的预算。

类顺序由守卫前序、DFS 前沿与 Z3 模型取值共同决定，代表值由 Z3 模型决定，不保证跨运行相同；编号在进程内唯一，不保证跨运行稳定。上限生效时不声称得到均匀样本，也不声称完整覆盖。完整性须同时检查 `path_truncated=false` 和全部类的 `truncated=false`。这里的完整性只指选定守卫和片段的投影域；若未被守卫测试的位会影响返回值，一个代表结果不等于穷举了全部可能返回值。

## 适用范围与验收

**寄存器读取采用并集语义。** 只在一臂读取的寄存器，在合并路径主迹上也视为读过。枚举恢复叶子输入和返回结果，不恢复逐条精确寄存器读写顺序、事件因果关系或每臂精确迹。需要这些信息时仍须实现全消费方的 guarded events。含内存访问或被调函数写状态的区域继续按既有规则拒绝合并。RISC-V 字段名映射与页表遍历解码留给 `agents/` 下的薄后处理层；不应写入 isla-lib。

函数级真实 IR 验证沿用 `baseline_config_const.toml`：分叉 **10** 条、合并 **1** 条，一级恢复 **10** 类；默认上限与实际不限额（测试中将两上限设为 `usize::MAX`）均输出 **256** 个二级解，无截断。`class_cap=2/path_cap=5` 输出 **3** 类、**5** 解，路径截断为 true。每个输出解均在原路径 Z3 求解器上复核片段约束。该函数末尾关于 reserved 的直接返回表达式未形成分叉守卫，因此其位保留代表值；这与原始叶子中存在符号返回值一致。

显式运行真实 IR 测试：

```sh
export RUSTFLAGS="-L $HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
ISLA_REGIONS_IR=/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir \
ISLA_ENUMERATION_TEST_OUTPUT=/tmp/e1 \
  cargo test -j 8 -p isla-lib merge_enumeration_real_ir --offline --features smt-thread-interrupt -- --ignored --nocapture
```

本机现场全量基线为 681 通过、13 失败、2 忽略（新配置红测未计入基线）。除给定 12 项外，原版本也复现了 `smt::tests::deadline到期中断check返回超时错误`：1ms 内查询提前返回 Sat。E1 全量为 685 通过、相同 13 失败、3 忽略；没有修复、跳过或增加基线失败。原始日志和红测证据在 `/tmp/e1/`。函数入口关闭枚举的真实工作负载 stdout 前后均为 4555 字节，`cmp` 完全一致；计时 stderr 不属于稳定输出。

最终验收还包括：`merge_enumeration` 4 通过、真实 IR 1 项显式通过；`region_merge` 37 通过、2 默认忽略；`path_merging` 6、`stats` 12、`execution_limits` 50 通过；isarch 旧字段逐字节序列化测试通过。两个二进制 `cargo check`、`cargo fmt` 和 release 构建通过，二进制保留在 `target/release/`。开启枚举的 `make -j1 solve-MRET THREADS=8` 冒烟产出 4 条用例，四条均包含枚举字段、各 1 解且无截断。构建并行度为 8，测试线程数为 4；每条验证命令外包 590 秒上限，没有单条超过 10 分钟。

二级展开采用本路径全部守卫测试过的片段并集。某片段对应的守卫在当前类上下文不成立时，该片段也参与二级展开；其取值受真实路径约束。一级仍用上下文投影，绝不因此增加虚假叶子类。

## F5 差分与边界验证

测试模块冻结旧阻断算法，并在嵌套上下文、`W∧¬R`、失败结果、派生片段及真实 `pte_is_invalid` 上比较完整类/解集合；有上限时用完整参照集合验证子集、计数和截断条件，不要求不同发现顺序得到相同的有限前缀。每个输出解连同完整投影类条件回投原路径 Z3。另覆盖空记录、空片段、UNSAT、消费者返回错误后的保存点/轨迹恢复、70 层且倒序保存的记录，以及显式运行的单路径 16384 类压力测试。

输出译码回环复用入口译码的“初始化寄存器表 + 全部钉值”环境，继续按当前模型具象化显式符号 CSR，并通过现有带限额函数入口继承主运行执行限额和合并策略。译码的扩展可用性守卫会读取权限与 CSR，故不能只传指令位，也不能向独立 solver 传主执行的符号或执行后寄存器。

F5 真实负载的一次完整测量得到 20 条路径、16592 类及 16592 个代表样本，路径截断为 false。与指定旧合并基线分别按原始 merge 模式复用 pt_decode 解码，均为 104 种形状，但 103 种计数相同，2 项差值为 −16/+16：16 个 L1 超级页未对齐样本从 `leaf_--x_u0` 变为 `leaf_r-x_u0`。该类中 W=0、X=1，相关 R 守卫的上下文不活动，且未对齐检查在权限检查之前返回，R 可有两种代表值。旧、新各取一个样本并只切换 R 位（同步前后内存）后，四个样本均被原路径 Z3 各接纳一次且结果一致。没有调整代表值或分类凑齐形状计数，因此本次不宣称达到“形状差异 0”，也不宣称具体 PTE 内容多重集合相同。详细原始证据见 `/tmp/f5/` 的报告及交叉检验。
