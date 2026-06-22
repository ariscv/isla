# Findings

- `isla-lib/src/isarch_exec.rs` 的 `run_symbolic_execute(...)` 当前通过 `executor::execute_ir_function_with_checkpoint(...)` 启动 `zexecute`，只把 `regs/lets` 注入 `LocalFrame`，没有注入 `Memory`。
- `isla-lib/src/executor/frame.rs` 的 `LocalFrame` 原生持有 `Memory<B>`，并提供 `set_memory(...)` 与 `task_with_checkpoint(...)`，适合按方案 A 新增一个可传入 `Memory` 的执行入口。
- `isla-lib/src/primop/memory.rs` 的 `read_mem(...)` / `write_mem(...)` 直接调用 `frame.memory().read/write`，因此只要把 `Memory` 注入到 `LocalFrame`，Sail 的访存 primop 就会自动走到底层内存模型。
- `isla-lib/src/memory.rs` 的 `Memory::read_symbolic(...)` / `write_symbolic(...)` 会分别产生 `Event::ReadMem` / `Event::WriteMem`，因此可以通过 `solver.trace()` 提取内存访问摘要作为 `isarch` 的可观测输出。
- `configs/riscv64.toml` 已配置 `[symbolic_addrs]` 区间，可直接作为 `isarch` 初始化 symbolic memory region 的来源。
- 对于`LOAD(..., width)`/`ones()`这样的函数输入的值，需要一个concrete的参数或者一个限定范围的数字有两种，1.`assert(a == 1 | a == 2 | ...)`，但有的时候由于ir结构无法fork出唯一确定的值作为函数参数输入；2.薄分摊`match a { 1 => (), 2 => (), ..., _ => assert(false) }` 形式的 assert helper。对 `assert(a == 1 | a == 2 | ...)` 这类 one-of 约束，Isla 不会自动把 `a` 变成 concrete 参数；如果后续 primop 需要 concrete 宽度/次数，可以在 Sail 侧用 `match a { 1 => (), 2 => (), ..., _ => assert(false) }` 形式的 assert helper 显式拆出单值路径，再在 Rust primop 消费端复用 `proven_symbolic_i128` 证明当前路径下 `a` 是否唯一。
