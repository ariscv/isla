# Review 36 修复计划

目标：修复审查 F1～F5，保留设备副作用、Constrained 生成器约束及逐字节排除语义。范围以 Isla HEAD `985e0a93645367cdcb8fb10d5491adf494255802` 为基线；开始时工作树干净。

热点文件：`isla-lib/src/memory.rs`、`isla-lib/src/bitvector/b129.rs`、`isla-lib/src/bitvector/b64.rs`、`src/isarch/memory_model.rs`。复用已有重叠检查、唯一地址分派及地址拆分重试，不引入静默替代结果。

步骤：应用审查全量复现补丁；运行失败基线；修复区域分派、129 位切片、有符号 MIN 减法和地址回绕；补充边界测试；执行复现、核心库、内存模型、工作区全量、扩展 feature 与 MRET smoke；格式化并同步状态和代码发现。

验证：审查 8 项必须全部通过；具体命令、配置、版本、结果与日志记录到 `docs/RESULTS.md`。不重生 IR，不改父仓库或其他工作树，不提交改动。未决问题：全量回归是否存在依赖旧错误行为的断言，按源码和反例判定，不能删减测试掩盖失败。
