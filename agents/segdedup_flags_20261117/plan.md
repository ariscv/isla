# 分段去重线环境变量改配置

目标：只迁移 a286b00c 相对 isarch 新增的功能／诊断环境变量，保持默认行为；不包含 lazy Z3 scope。

范围：isla-lib/src/config.rs 及区域配置模块、现有环境变量读取点、相关测试、src/isarch_main.rs、README.md、specs/isarch-cli.md。

步骤：记录原始区域／去重／isarch 回归与冻结程序；整合 dbfc6e70 的唯一新增提交到工作目录（不执行 Git merge，简报规则将 Git 写操作留给 Claude）；先写配置及 CLI 红测；迁移读取和测试设置；格式检查及有限回归；冻结新程序；scheduler 本机 T32、逐路径30秒、judge墙钟310秒、默认对照各20秒、总包装365秒／scheduler外限7分钟、64GiB 单次 PMP=2 judge；逐字段比较；限定 review；报告交付。

配置：使用 [execution_limits.region_options] 及同名横线 CLI 参数，布尔显式 true/false，CLI 覆盖 TOML；不保留环境变量兼容。沿用现有 SMT 进程内冻结配置方式，执行前完成初始化。

边界：仅当前指定工作树；不动基础配置／Sail／其他工作树，不提交、不 merge、不 push。共享根文档只追加本任务摘要及结果。没有用户实时答复，选择保守可回退方案。

验收：配置默认／TOML／CLI／优先级／非法值红绿测试；区域111通过5忽略、去重义务14通过；isarch exec/samples/path_cache；fmt、release；默认与冻结改前程序等价；两份PMP=2输入 sample0拒绝、sample1接纳且后态与历史一致。不运行大规模实验。

实施及验证已收尾，实际结果和验收缺口见 [状态](status.md) 与 [验证数据](verification.json)。PMP=2在310秒仍未进入resident；遵守一次本机运行的边界，不追加预算。
