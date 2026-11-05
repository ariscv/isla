# 执行统计实施计划

基线：`dc76449`，工作树 `feat/postprocess-enumeration`。仅增加统计，保留控制流、事务、约束及任务调度行为。

- 在现有菱形测试中先断言开启合并成功、关闭合并零尝试。
- 新建 executor 统计模块；按实际合流入口拒绝点定义枚举。统计每次调用与每个候选的失败。
- 复用 ForkSink，在实际提交子任务时记录已有函数 Name 与 SourceLoc，覆盖 Jump、Monomorphize 和操作数重试。
- 在 solve-state 收尾统一输出；仅 `ISLA_STATS=1` 启用，直方图只输出前 30 项。
- 验证仅 cargo check、定向 isla-lib 测试及 cargo fmt，每条构建和测试命令最多 600 秒。固定官方 Z3 链接路径、rpath 与 smt-thread-interrupt feature。

热点：`isla-lib/src/executor.rs`、`executor/stats.rs`、`ir.rs`、`src/isarch/solve_summary.rs`、`src/isarch/exec.rs`。

不运行 release、make solve、Sv39 或全量测试，不修改 Git 元数据。根仓状态文件不在授权写入目录内，本地记录保留于本工作树。
