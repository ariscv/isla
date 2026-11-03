# 旧专用浮点测试迁移回归

旧 `float.rs::softfloat_tests` 有 21 项：其中 20 项含结果位或异常标志断言，本目录将其全部按原始输入映射成 35 条独立 Berkeley SoftFloat 向量；另一项 `dispatch_unknown_name` 只检查已删除的 Rust 私有分发表形状，随该实现退役。`mapping.tsv` 逐行标明旧测试、普通 Sail helper、输入、完整结果位与五位 RISC-V flags。原有测试中的部分断言只查一个 flag；新回归检查完整五位 flags。

`generate.py` 调用浮点议题的独立 [SoftFloat oracle](../../../agents/float_support_review/oracle/README.md)，固定输入后生成 `cases.tsv` 和 `mapping.tsv`。预期值不从待测 Sail 或 Isla 计算。构建 oracle 后，在本仓库根目录执行：

```sh
python3 isla/test/softfloat_legacy/generate.py --oracle /path/to/oracle
python3 isla/test/softfloat_legacy/wrap.py \
  --ir isla/rv64d.ir --output /tmp/rv64d_legacy_wrapped.ir
cargo run --manifest-path isla/test/softfloat_legacy/runner/Cargo.toml -- \
  /tmp/rv64d_legacy_wrapped.ir isla/test/softfloat_legacy/cases.tsv
```

`wrap.py` 只在 IR 的外部测试副本附上调用包装器，先要求每个 helper 有普通 IR 函数体；它不改正式 `rv64d.ir`。runner 对每例要求恰好一条完成路径、普通函数进入事件、SAT，再要求“完整结果位或五位 flags 与 oracle 不同”这一公式为 UNSAT。求解器返回 Unknown 或超时、漏函数体、额外路径和任一位差异均失败。这个回归覆盖旧测试给出的 35 组具体输入，不声称全域等价或指令状态通过。

`cases.tsv` 是可审阅的固定参考快照。重生前须确认 oracle 对应的 Sail-RISC-V SoftFloat 版本与构建选项；若变更了预期值，审查 `mapping.tsv` 的逐行差分。当前 IR 与该向量的运行版本、命令和结果记在浮点专题实施/验证记录。
