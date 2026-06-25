# guides

## V 扩展符号执行约束原则

不要为了让 solve-state 快速通过而把运行上下文固定成单一代表值。`vl`、`vstart`、`vtype`、mask/tail policy、寄存器选择等都属于程序运行态，除非用户明确要求生成某个特定上下文，否则不能在 Isla 入口层覆盖成固定值。

可以固化真实 RISC-V 处理器不可变的编译/配置参数，例如 `vlen`、`elen`、`xlen`，以及由这些参数决定的静态上界。此类参数来自 Sail config 或目标配置，本来就不是每条 path 上变化的程序上下文。

应优先加强 Sail/RISC-V 语义中已有但模型表达过松的约束，例如：
- `SEW` 只能是 8/16/32/64，`LMUL_pow` 只能是 -3..3 且排除保留编码；
- `num_elem` 只能落在 `vlen` 和合法 SEW/LMUL 推导出的有限集合中；
- vector crypto 的 `vl`/`vstart` element-group 对齐、`EGW <= LMUL * VLEN`、寄存器组不重叠等 encdec 条件；
- 访存、CSR、寄存器组等路径如果是非法状态，应通过原模型的 `Illegal_Instruction`、`assert` 或已有检查丢弃，而不是替换成任意合法代表值。

需要限制的是两类路径规模：
- 符号执行可能无限 fork 或无法停机的路径，例如未受约束的循环边界、动态宽度导致的无限候选、递归/回边没有可证明上界；
- Sail 模型约束过松导致的不必要 fork，例如明知只有有限合法编码却让 solver 在更大整数域上枚举。

如果 timeout 来自有限上下文的笛卡尔积，而不是无限 fork 或错误建模，应先估算规模再处理。V 扩展常见规模来自 `SEW * LMUL * vstart/vl * mask/tail * 32 个 vreg 分组` 的组合；当这些组合都是真实合法状态时，可以在合理范围内调高单 clause 或全量 solve timeout，而不是把上下文固定成单点。调整阈值前应先看 itrace 中的具体停点：如果停在固定上界的 vector crypto element group 写回等路径，属于可控规模；如果停在无法证明上界的循环、递归或动态宽度候选，则应先补语义约束或改执行策略。
