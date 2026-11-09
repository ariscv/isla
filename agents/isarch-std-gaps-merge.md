# std-gaps 模型与 IR 对齐

当前模型为 `cbb4766f`，完整合入 `feat/sail-std-gaps@7d7e76f3`；旧isarch34903a1e的x0及分页修复保留。`rv64d.ir` 与 `ir/rv64d_v128_e64.ir` 已用该模型严格重生。最新来源见 [isarch.json](../ir/provenance/isarch.json)。其他IR保持各自历史来源，不继承本轮PASS。

本轮path merge6通过、executor396通过/5忽略，退出码0；新IR向量定向22通过、原生fuzz20/20认证及20次变异/判定，退出码0。普通/SYMBOLIC模型严格类型检查均退出0。完整证据由runner的isarch_std_gaps_merge_20261109议题归档。
