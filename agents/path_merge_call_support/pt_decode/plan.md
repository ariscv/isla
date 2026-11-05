# P1 实施计划

目标：独立解码样本中的 RV64 页表，生成模板数据，并比较分叉与合并代表样本的形状计数。

范围只限本目录。不修改 Isla 核心、Sail 模型、既有记录或输入样本；不构建二进制、不执行 Git 写操作。

热点依据：上级目录的 `samples.md`、`enumeration.md`、`plan.md`、`merge-record.md`、`sv39-pinned.md`；模型的 `model/sys/vmem_pte.sail`、`vmem.sail`、`pma.sail`；LOAD 参数顺序见 `model/extensions/I/base_insts.sail`。

步骤：

1. 先写 unittest，覆盖位域、模式、取址、遍历、异常、掩码和分布比较；记录红测。
2. 用 Python 标准库实现严格 JSONL 输入、模式驱动的遍历和按形状聚合。
3. 分别输出 fork、merge 分布，再输出逐形状交叉检验；保留输入哈希、截断计数与实际耗时。
4. 核对全部输出、说明适用边界，将结论记在本目录 `status.md` 和 README。

验证：在本目录执行 `python3 -m unittest`，然后通过 CLI 完整处理两份真实样本。

已核实：`RSW_60t59b=[60:59]`、保留位 `[58:54]`；N/PBMT 在当前 Sail 未启用。真实 IR 支持 Svrsw60t59b，dirty_update=false。这两项属于样本格式未携带的模型配置，CLI 必须显式指定。

未决：访问异常可能发生在下层 PTE 读取前。只有样本 PMA 能证明该地址不可读时才接受缺失单元为提前终止；其余缺失一律报错。形状分布是否相同由实际结果决定。

用户限定可写范围，因此不修改上级 TODOs、findings、RESULTS 或 status；证据与可复用发现统一保存在本目录。
