# 本次差异审查

仅审查 fe2c9e08 之后的本轮修改；无子代理。

- 配置 DTO 删除旧字段，入口先拒绝旧字段并给迁移路径，随后 serde deny_unknown_fields 拒绝未知字段；没有别名、fallback 或旧字段转换路径。
- PathMergeConfig 将功能、局部配置、枚举和诊断分开，solver 只有本基线已有的 bool_proof_rlimit；未提前加入其它任务的字段。
- 四种局部规则按 kind 明确区分。with_config 仍按筛选范围、每分支点预算、区域预算、合并策略的原顺序应用；未知位置、严格策略验证、冲突拒绝和策略优先级不变。内部策略编号仍是 merge_policy 子序列的编号，保持原统计输出。
- 枚举解析复用既有实现，包括所有输出后端、预算、stride 和预测限制；输出消费改为新字段。
- CLI 名称/覆盖时机不变；先 clone 再校验，错误不部分更新配置。isla-execute-function 的 --path-merging 同步迁移。
- 求解热路径继续读取 RegionOptions 运行时冻结快照；该类型不再是外部配置字段。默认快照不改变执行行为。未改 Sail 模型、IR、区域算法或 SMT 求解算法。
- 新解析器使用 serde 作类型校验，保留 strict/hash、百分比、judge正数、case_quota、异常过滤和诊断语义检查。63项配置回归通过。
- 78份现存workaround与一份混合四类规则配置的运行时ExecutionLimits文本前后一致；ITYPE固定编码输出48945字节前后相同。

没有发现本轮致命代码问题。交付不能标为整个仓库迁移完成：真实scheduler与Sail配置在指定树外，只生成并检查了external-migration.patch；make入口默认仍指向未迁移的Sail配置。整组isarch exec未在短测预算内完成，常规全integration test构建也有基线共享历史夹具编译错误；均保留原日志，不把这些未通过项记PASS。
