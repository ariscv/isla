# fuzz 的路径 DAG 导出

探索结束后，每条完成路径写入 `dag/path-<path_signature>.json`，目录索引为 `dag-manifest.json`。三种 fuzz 模式都写出。数据直接来自当前检查点的 Isla 执行迹与 `SamplePath`，没有经 Z3 化简，也不使用来源哈希判定有效性。

第 5 步起，fuzz 的文件接口使用 `schema_version=2`：守卫的 `record_id` 改用规范坐标，与 judged 的既有重编号方式一致，避免进程内追加编号受线程顺序影响。原始 SMT 定义、守卫表达式和父坐标不变。通用 `SamplePath::export_dag` 仍返回原始版本 1；仅 fuzz 落盘适配层转为版本 2。历史版本 1 保存的是进程内编号，不能据此要求跨进程字节相同。

## 格式

顶层 `schema_version=2`，字段如下。

| 字段 | 含义 |
| --- | --- |
| `path_signature` | 当前完成路径的身份，与 judged v1 对齐 |
| `definitions` | 按执行先后排列的原始 SMT `Def` 序列；包含声明、定义、断言和枚举定义 |
| `guards` | 按既有父链规则排列的规范守卫定义，与 judged 的向量逐位对应 |
| `declarations` | 自由常量声明及类型；`input_reference` 说明它是否直接出现在前态或读取值中 |
| `state.pre`、`state.post` | 前后寄存器；指令仍是 `pre.$instruction` |
| `state.result`、`state.ret_val` | 返回结果的保类型结构及原展示文本 |
| `state.memory` | `SamplePath` 的访存并集；每项含地址、数据、字节数、活动条件与可选标签 |

每个定义含 `sequence`、`trace_index`、`kind`、`smtlib`、源码位置 `source` 和原 `attributes`。`sequence` 是定义序号，`trace_index` 是完整执行迹中的位置，均从零开始。`DeclareConst`、`DefineConst` 保留 `symbol` 和推断类型；`DeclareFun` 另含参数类型；`DefineConst`、`Assert` 的 `references` 列出直接常量引用。函数调用仍完整保存在 `smtlib`。`DefineEnum` 单独保存名字、成员和数量，SMT 文本可为空。

表达式沿用 Isla 现有 SMT-LIB 输出器，作为带类型的文本存储，不另造表达式运算符。`vN` 只在当前路径文件中有意义；定义中对其他 `vN` 的引用形成 DAG。保留 `DefineConst` 与 `Assert` 的先后顺序，不排序断言，不展开共享定义。类型支持布尔、位向量、枚举、数组、浮点及舍入模式。

状态中的具体叶值沿用 samples v1；符号叶值形如 `{"symbol":"v0","smtlib":"v0","type":{"kind":"bool"}}`，混合位串保存表达式和类型。结构体、构造子、向量、列表递归保留。尚未确定的构造子保存 `discriminant` 及各 `possibilities`。

守卫含规范 `coordinate`、以规范坐标重编号的 `record_id`、`parent_coordinate`、所属 `arm`、原条件 `condition`、父链活动条件 `active`、`canonical=active && condition`，以及函数、分支位置和死亡标志。非活动守卫的规范值因此为 false，与 judge 的规则相同。版本 2 的文件内记录编号就是规范坐标；探索诊断中的原进程内编号仍可能变化，跨进程使用规范坐标及完整类身份。

## 小例子

以下省略源码位置和原属性，仅展示关键字段；`v0` 为前态布尔值，`v1` 为其取反，路径要求 `v1` 为真。

```json
{
  "schema_version": 2,
  "path_signature": 42,
  "definitions": [
    {"sequence":0,"trace_index":0,"kind":"declare_const","symbol":"v0","type":{"kind":"bool"},"smtlib":"(declare-const v0 Bool)"},
    {"sequence":1,"trace_index":1,"kind":"define_const","symbol":"v1","type":{"kind":"bool"},"references":["v0"],"smtlib":"(define-const v1 Bool (not v0))"},
    {"sequence":2,"trace_index":2,"kind":"assert","type":{"kind":"bool"},"references":["v1"],"smtlib":"(assert v1)"}
  ],
  "guards":[{"coordinate":0,"record_id":0,"parent_coordinate":null,"arm":"root","condition":{"smtlib":"v1","type":{"kind":"bool"}},"active":{"smtlib":"true","type":{"kind":"bool"}},"canonical":{"smtlib":"(and true v1)","type":{"kind":"bool"}}}],
  "state":{"pre":{"flag":{"symbol":"v0","smtlib":"v0","type":{"kind":"bool"}}},"post":{"flag":{"symbol":"v1","smtlib":"v1","type":{"kind":"bool"}}},"result":{"bool":true},"memory":[]}
}
```

## 重读检查与限制

每条路径写出后立即用 serde JSON 重读，与内存中的整个 JSON 逐字段相等，并核对路径签名和守卫数。manifest 汇总实际路径数、守卫总数、每文件定义数及 `reread_consistent=true`。单元测试另验证声明、定义、断言的顺序和前后寄存器的符号引用。实验脚本可按 manifest 重新打开全部文件；这只证明序列化完整，本阶段没有表达式解析或求值器。

自由符号保持声明，不擅自具体化。不由输入决定的符号也保留 `declare_const`；`input_reference=false` 只表示没有直接输入引用，不能据此推断是否可由断言间接确定。活动读取是否由具体内存决定、后态是否唯一，仍由 `path-index.json` 的静态事实和认证档判断。

导出覆盖 judge 所需的完整前后寄存器、结果、访存活动条件、地址、数据与标签。未保存 Z3 内部 AST、模型偏好、调用栈、可恢复的求解器二进制状态、全部非 SMT 调试事件或指令级精确寄存器读写顺序。`state.memory` 沿用合并主迹的并集及既有活动保护条件；不把它声称为每个守卫类的精确时序。内存初值和写后读限制继续沿用 samples v1。标签保存供后续使用，当前 judge 的内存判定仍按既有协议。

只导出拥有 `SamplePath` 的完成路径；执行错误和未完成路径没有对应文件，原 partial 状态继续保留。文件本身不包含完整配置，应与同批 `seed-map.json`、`path-index.json` 和来源记录一起使用；枚举定义等信息也使这里的文本不等同于可直接交给 Z3 的独立脚本。

路径签名、SMT 变量编号与来源位置不构成跨配置有效性证明。重新使用具体输入时，仍须用当前 IR、配置和 Isla 语义确认。
