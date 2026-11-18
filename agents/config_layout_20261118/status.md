# 配置统一迁移状态

实现完成，限定验证通过；跨仓实际落地尚未完成，不签全仓迁移PASS。基线fe2c9e08，分支refactor/config-layout-20261118，无Git写操作。

新解析/CLI/运行时应用及README和CLI文档完成；默认ITYPE样本48945字节逐字节相同。配置63、区域118/5忽略、去重义务14、共享历史4、执行限制31、CLI3、isarch配置应用9、samples8、cache7、主入口27通过；两个release二进制及fmt通过。

待合入时应用树外迁移补丁（78份Sail workaround、scheduler读取与夹具/文档、根术语表）；真实树外文件未改。isarch exec整组短测超时、基线integration夹具编译错误保留。

[计划](plan.md) · [字段映射](inventory.md) · [差异审查](review.md) · [树外迁移补丁](external-migration.patch)。具体命令与原始证据见 output/config-layout，根报告与归档按brief另行追加。
