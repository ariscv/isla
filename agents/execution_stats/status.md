# 执行统计状态（2026-11-05）

结论：仅统计改动已实现，限定验证通过；没有运行 Sv39，不能据此判断真实页表遍历是否触发合并。改动留在 `feat/postprocess-enumeration` 工作树，基线 `dc76449`，没有写 Git 元数据。

计划见 [plan.md](plan.md)，命令和逐次结果见 [验证记录](../../docs/RESULTS.md#2026-11-05-可选执行统计)。根仓状态文件不在授权写入范围内，本记录及本工作树的 TODO、议题入口已同步。

## 统计口径与输出

只有创建 SharedState 时环境变量恰为 `ISLA_STATS=1` 才启用。solve-state 开始执行 clause 前清零，结束全部 clause、编码批次和 ExecuteAs 续执行后，向 stderr 各打印一行：

```text
[MERGE_STATS] {"attempts":N,"successes":N,"failures":N,"candidate_attempts":N,"failure_reasons":{原因枚举:N,...}}
[FORK_STATS] {"total":N,"unique_locations":N,"top":[{"function":"函数名","location":"文件 起始行:列 - 结束行:列","source_loc":{"file":N,"line1":N,"char1":N,"line2":N,"char2":N},"count":N},...]}
```

上面是格式示意，`N` 为整数。正式输出为合法单行 JSON，原因键包含零计数。

- `attempts`：进入 try_merge_diamond 的调用次数。`successes` 为返回汇合点的次数，`failures` 为返回 None 或错误的次数；正常收尾后 `attempts = successes + failures`。
- `candidate_attempts`：实际模拟的候选汇合点数。候选失败后仍会尝试下一个，所以候选失败原因之和不等于调用失败数。
- `failure_reasons`：按入口拒绝点分类，使用枚举序列化，不拼接原因字符串。`no_join` 与提交后读取值合并错误属于调用级原因，其余属于候选级原因。
- `total`：真实提交分叉子任务的总次数；包括 Jump、Monomorphize、长度／条件／表达式重试。初始任务、成功合并产生的 Fork 事件、预算截断和采样都不计入。
- `unique_locations`：按已有 `(Name, SourceLoc)` 聚合的位置数。函数通过既有符号表解码，位置使用 `SourceLoc::location_string`，保留原始 SourceLoc。相同函数不同位置分别计数。
- `top`：按次数降序，仅输出前 30 项；同次数按函数及位置排序。总数仍统计所有位置。

失败枚举：

| 键 | 含义 |
| --- | --- |
| `no_join` | 静态检测没有候选汇合点 |
| `else_arm_unsupported` / `then_arm_unsupported` | 对应臂模拟返回 None |
| `else_arm_error` / `then_arm_error` | 对应臂模拟返回错误 |
| `else_transaction_invalid` / `then_transaction_invalid` | 臂模拟返回状态，但事务无效 |
| `limited_pc_modified` | 某臂写入受限架构 PC |
| `depth_mismatch` | 深度预算启用且两臂深度不同 |
| `loop_history_mismatch` | 回跳预算启用且两臂循环历史不同 |
| `frame_merge_rejected` | 状态合并返回 false |
| `frame_merge_error` | 状态合并返回错误 |
| `frame_transaction_invalid` | 状态合并返回 true，但事务无效 |
| `equality_error` | 共同读取值的相等约束构造失败 |
| `equality_transaction_invalid` | 相等约束构造成功，但事务无效 |
| `register_read_merge_error` | 事务提交后，读取事件中的值构造 ITE 失败；保留原错误返回 |

所有计数和直方图由 Mutex 保护；SharedState 中的 Arc 跨 worker 共享，不随路径复制。求解收尾在 worker 全部结束后读取。

## 验证与限制

- 先增加菱形统计断言，首次测试因统计接口缺失按预期编译失败。
- cargo check 通过；没有本轮新增编译错误，日志保留既有未用变量等警告。
- 最终定向测试：统计单元 2/2、路径合并 4/4、多线程访存分叉 1/1、Monomorphize 1/1、操作数重试 1/1，共 9 个不同测试通过。
- 四线程统计单元覆盖 3280 次更新、160 个源码位置及前 30 项排序；菱形样例覆盖启用合并成功和关闭合并零尝试。
- 拒绝样例第一次新增断言把单臂声明误归为模拟不支持；源码核实是状态合并拒绝，修订断言后通过。没有修改生产行为来迎合断言。
- cargo fmt 已执行；其对无关既有代码的排版改动已恢复。git diff --check 通过。
- 未运行 CLI 求解，因此未动态核对两行 stderr 或未设环境变量时完整 CLI 输出逐字一致；源码仅在统计启用时打印，禁用计数单元通过。
- 未逐个制造全部失败枚举，未跑 release、make solve、Sv39、全量测试、性能实验或额外 feature 组合；没有修复历史枚举 sort 等问题。
