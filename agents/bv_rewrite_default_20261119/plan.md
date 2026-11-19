# SMT 等价改写缺省开启计划

从 Isla `c652949e` 开出 `perf/bv-rewrite-default-20261119`。在 `isla-lib/src/smt/rewrite.rs` 调整共用缺省值，让 TOML、CLI 和直接使用库的调用方都开启三条规则。沿用 `--bv-rewrite=false`、`bv_rewrite = false` 和空列表关闭，保留规则列表选择。更新 CLI 帮助、README、规格及依赖旧缺省值的测试。

先用配置测试固定省略和显式值的行为，再验证 SMT 改写、配置、区域串行和 `nested_merge_` property。PMP=2 judge 用已签收的 LOAD IR、TOML 和两份输入，在本机持共享文件锁运行，逐路径限时 120 秒，省略改写开关以覆盖新缺省。比较接纳、前后态、访存、返回值和可比的守卫信息。

在独立分支提交。逐项记录命令、结果和有限签收边界。
