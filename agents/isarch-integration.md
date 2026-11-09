> 后续状态：模型已推进到cbb4766f并重生当前v128 IR，见[std-gaps对齐](isarch-std-gaps-merge.md)。下文记录std-gaps合并前的34903a1e版本。

# isarch 模型与 IR 对齐

本分支直接继承 `a8b610dd`，完整包含 path merge 的 `78b04e3d`、`d824ec21`、`ff975203`，未删除其代码、提交或 fuzz 资产。

当前模型为 `34903a1e`：`d5aec317` 的 x0 修复，加 `5667f347`（Svnapot）和 `7d7e76f3`（Svpbmt）的 cherry-pick。`rv64d.ir` 与 `ir/rv64d_v128_e64.ir` 已从该模型用严格 SYMBOLIC 配置重新生成。现行入口见 [isarch 来源](../ir/provenance/isarch.json)；旧 `manifest.json` 和其他 IR 保留其历史来源，不授予新模型验证结论。

`scripts/run.mk` 的 `SAIL_RISCV_DIR` 默认仍为 `../sail-riscv`；独立工作树可显式指定整合模型目录。

本轮在独立候选源码重新构建 release 程序，path_merging 专项 6/6，executor 回归 396 通过、5 忽略，退出码均为 0；原生 fuzz smoke 结果由 runner 的整合状态记录。
