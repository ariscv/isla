# Findings

- `isla-lib/src/isarch_exec.rs` 的 `run_symbolic_execute(...)` 当前通过 `executor::execute_ir_function_with_checkpoint(...)` 启动 `zexecute`，只把 `regs/lets` 注入 `LocalFrame`，没有注入 `Memory`。
- `isla-lib/src/executor/frame.rs` 的 `LocalFrame` 原生持有 `Memory<B>`，并提供 `set_memory(...)` 与 `task_with_checkpoint(...)`，适合按方案 A 新增一个可传入 `Memory` 的执行入口。
- `isla-lib/src/primop/memory.rs` 的 `read_mem(...)` / `write_mem(...)` 直接调用 `frame.memory().read/write`，因此只要把 `Memory` 注入到 `LocalFrame`，Sail 的访存 primop 就会自动走到底层内存模型。
- `isla-lib/src/memory.rs` 的 `Memory::read_symbolic(...)` / `write_symbolic(...)` 会分别产生 `Event::ReadMem` / `Event::WriteMem`，因此可以通过 `solver.trace()` 提取内存访问摘要作为 `isarch` 的可观测输出。
- `configs/riscv64.toml` 已配置 `[symbolic_addrs]` 区间，可直接作为 `isarch` 初始化 symbolic memory region 的来源。