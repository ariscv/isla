# Findings

本文档用于沉淀可跨主题复用的代码知识，内容应以稳定的模块职责、调用关系、数据流和调试结论为主。
不应记录强依赖单次任务上下文的表述，例如“这次实现中”“后续准备”“待排查”“当前验证结果”等会话态信息。

## `isarch` 的符号执行入口

- `isla-lib/src/isarch_exec.rs` 的 `run_symbolic_execute(...)` 是 `isarch` 执行单条指令语义的核心入口。它负责创建 solver、构造符号化指令参数、准备初始内存、创建 checkpoint，并调用 executor 执行 `zexecute`。
- `run_symbolic_execute(...)` 的结果收集逻辑也位于 `isarch_exec.rs`。collector 会读取执行后的寄存器状态、汇编字符串、返回值，以及 `solver.trace()` 中的内存事件，并将它们整理成 JSON 输出。
- `isarch_exec.rs` 更适合作为“指令级符号执行适配层”，负责输入准备、结果整形和对外输出；通用执行语义不宜继续下沉到这里。
- `src/isarch.rs` 在启用 `debug_exec` feature 时，会在子命令分发前直接调用 `isla_lib::isarch_exec::test_exec_main(shared_state, regs, lets, &isa_config)`；因此当执行`make run`时候 `test_exec_main(...)` 是当前 `isarch` 调试执行路径的直接入口之一。

## executor、frame 与 memory 的职责边界

- `isla-lib/src/executor/frame.rs` 的 `LocalFrame` 原生持有 `Memory<B>`，并暴露了 `memory()`、`memory_mut()`、`set_memory()`、`task_with_checkpoint()` 等接口。
- `LocalFrame::new(...)` 默认创建空 `Memory`；`LocalFrame::new_call(...)` 会沿调用链复制当前 frame 的 memory，因此内存状态会随函数调用继续传递。
- `isla-lib/src/executor.rs` 中同时存在两组 checkpoint 入口，它们拆分的是两条正交职责：
  - `*_and_memory(...)` 这一维负责在创建初始 `LocalFrame` 后调用 `set_memory(...)`，把显式构造的 `Memory` 注入执行上下文；不带 `and_memory` 的版本则保持默认 memory。
  - `*_multi_thread(...)` 这一维负责把已经构造好的 task 交给 `start_multi(...)` 调度；非 `multi_thread` 版本则交给 `start_single(...)`。
- 因此 `execute_ir_function_with_checkpoint_and_memory_multi_thread(...)` 的职责应是两者叠加：既要注入 memory，也要走 `start_multi(...)`，而不是退回单线程调度。
- 这说明“是否携带显式内存模型进入执行”和“执行调度是单线程还是多线程”都是 executor 入口层的选择，而不是 `LocalFrame` 本身能力不足。

## Sail 访存 primop 与底层内存事件链

- `isla-lib/src/primop/memory.rs` 的 `read_mem(...)` / `write_mem(...)` 通过 `frame.memory().read/write` 访问底层内存模型，因此只要 `LocalFrame` 持有正确初始化的 `Memory`，Sail 访存 primop 就会走到统一的 memory 子系统。
- `isla-lib/src/memory.rs` 中，`Memory::read_symbolic(...)` 会向 trace 添加 `Event::ReadMem`，`Memory::write_symbolic(...)` 会向 trace 添加 `Event::WriteMem`。
- 因此，`solver.trace()` 是 `isarch` 观察访存行为的统一出口；上层如果要生成 `memory-events`、访存摘要或额外约束，优先应基于 trace 做整理，而不是改写 executor 主链路。
- 看到指令被解码为 `LOAD(...)` / `STORE(...)` 只能说明指令语义分发成功，不能直接推出底层已经产生 `ReadMem` / `WriteMem` 事件；是否真的发生访存，仍应以 trace 中是否出现对应事件为准。

## `symbolic_addrs` 的语义

- `isla-lib/src/config.rs` 会从配置文件的 `[symbolic_addrs]` 读取 `base`、`top`、`stride`，并写入 `ISAConfig` 的 `symbolic_addr_base`、`symbolic_addr_top`、`symbolic_addr_stride`。
- `configs/riscv64.toml` 已提供这一段配置，因此 RISC-V 的 `isarch` 路径可以直接复用它来初始化和约束符号地址。
- `isla-lib/src/isarch_exec.rs` 的 `build_symbolic_memory(...)` 会根据 `symbolic_addr_base..symbolic_addr_top` 向 `Memory` 添加 symbolic region。
- 同文件中的 `constrain_trace_memory_addresses(...)` 会遍历 trace 里的非取指 `ReadMem` 和所有 `WriteMem`，对地址补充如下求解约束：
  - `base <= addr < top`
  - 当 `stride > 1` 时，`(addr - base) % stride == 0`
- 这说明 `[symbolic_addrs]` 在当前实现中同时承担两层语义：
  - 用于声明 symbolic memory region 的范围
  - 用于收缩求解时实际访存地址的取值空间

## `memory-events` 的组织位置

- `isla-lib/src/isarch_exec.rs` 中的 `collect_memory_events(...)` 负责把 trace 中的 `ReadMem` / `WriteMem` 转换为面向 JSON 的 `memory-events` 结构。
- 这一层会补充对上层输出有用但不属于底层执行引擎职责的信息，例如：
  - 访存方向（`read` / `write`）
  - region 名称
  - 字节数
  - 地址表达式和模型值
  - 写入布尔结果、写入数据、排他属性、是否取指
- 因此，输出格式相关逻辑应优先留在 `isarch_exec.rs` 的 collector 中；`executor` 和 `memory` 更适合只维护通用执行与事件生产能力。
- `isla-lib/src/smt.rs` 的 `Event::is_exclusive()` 已统一封装了 `ReadMem` / `WriteMem` 的排他访问判断；上层若只需要事件级别的排他属性，应优先调用该 accessor，而不要依赖 `WriteOpts` 的 `Debug` 字符串格式。

## `frame.forks` 的含义

- executor 中的 `frame.forks` 表示“某条执行路径累计经历过多少次 executor 级别的 fork”，不是“当前一共有多少条完成路径”。
- 该计数主要反映符号 `Jump` 分支和 `Monomorphize` case split 带来的路径分裂深度，因此更适合用来判断路径复杂度，而不是直接当作源码分支数或结果条数。

## `executor::start_multi` 的并发模型

- `isla-lib/src/executor.rs` 的 `start_multi(...)` 不是 `async`/future 运行时模型，而是基于 `std::thread::scope(...)` 的 OS 线程并行。
- 当前实现不再使用 `crossbeam::deque` 的 work-stealing 作为 `start_multi(...)` 的主调度模型；它改成了“fork 点内联 spawn + 共享待处理队列”的结构：
  - `run_loop(...)` 在遇到符号 `Jump` 或 `Monomorphize` 时，不再直接往当前 worker 本地队列 `push`
  - 它会通过统一的 fork sink 把 child `Task` 提交给 `start_multi(...)` 的运行时
  - 若当前活跃线程数未达到上限，则在 fork 当下立刻 `scope.spawn(...)` 新线程执行 child task
  - 若线程数已到上限，则 child task 会进入一个共享待处理队列，等某个刚结束 task 的线程统一批量补 spawn
- `Task` 自身保存了冻结后的执行帧 `Frame`、SMT `Checkpoint`、fork 条件和路径权重 `Fraction`；线程之间共享的不是一个可并发访问的 solver，而是可克隆的 checkpoint。
- 多线程路径上的每个 task 都会在自己的线程里创建新的 Z3 `Context`，再用 `Solver::from_checkpoint(...)` 重建该任务对应的 solver 状态后继续执行。这说明它的并行基础是：
  - OS 线程
  - fork 点直接创建线程
  - `Arc`/`Mutex`/`Condvar`/原子变量的线程同步
  - 基于 checkpoint 回放的“每任务独立 solver 实例”
- `start_multi(...)` 的外层不再维护 `Poke`/`Idle`/`Kill` 式的协调循环；它只负责：
  - 构造共享运行时
  - 提交初始 tasks
  - 等待 `pending_tasks == 0` 后收敛退出

## `start_multi(...)` 并行度偏低的结构性原因

- `start_multi(...)` 默认通常只接收一个初始 `Task`，因此在第一次路径分裂发生之前，天然只会有一个执行线程真正工作；这个阶段不可能靠调度器把单一路径强行拆成多核。
- executor 的并行粒度是“路径级 task”，不是“指令级”或“单次 SMT 调用级”。如果某条路径在进入第一个可分裂的 `Jump` / `Monomorphize` 之前要做大量解释执行、求值或 SAT 检查，那么这段时间只能由单个线程推进。
- 当前实现已经把“fork 后先入本地队列，再等 steal”这个延迟链路去掉了；因此 fork 之后的并行度主要取决于两件事：
  - fork 发生得是否足够早
  - fork 产生的 task 是否足够粗粒度，值得独立占一个线程
- 当 fork 非常频繁且线程数已满时，child task 会先进入共享待处理队列；这些任务会在已有线程完成一次 path 后被统一批量补 spawn，因此仍然存在“超过线程上限的 task 需要排队”的自然限制。

## RISC-V STORE 路径的排查重点

- 在 `../sail-riscv/model/extensions/I/base_insts.sail` 中，`execute STORE(...)` 本身是较薄的一层包装，主要负责计算参数并调用 `vmem_write(...)`。
- 因此，若 STORE 类指令在 Isla 中出现大量 fork，更应该优先检查 VMEM 与访存检查链路，而不是只盯顶层 `execute STORE(...)` clause。
- 这条链路的关键热点包括：
  - `model/sys/vmem_utils.sail::vmem_write_addr`
  - `model/sys/vmem.sail::translateAddr`、`translate`、`pt_walk`
  - `model/sys/vmem_pte.sail::check_PTE_permission`、`update_PTE_Bits`
  - `model/sys/mem.sail::phys_access_check`、`checked_mem_write`
- 这些位置之所以容易放大路径数，是因为它们叠加了对齐处理、跨页拆分、页表遍历、权限检查、A/D 位更新、PMP/PMA/MMIO 检查等控制流；在符号地址或符号页表状态下会迅速展开为大量 IR `jump`。

## 与当前仓库实现相关的调试判断

- 如果某条访存类指令已经完成语义执行，但 `memory-events` 为空，应优先确认两个问题：
  - 是否真的进入了 `isla-lib/src/primop/memory.rs` 的 `read_mem(...)` / `write_mem(...)`
  - trace 中的 `ReadMem` / `WriteMem` 是否在建模或约束阶段被过滤掉
- 如果 fork 值很高而 `memory-events` 仍然很少，优先怀疑爆炸发生在 VMEM、地址翻译或权限检查链路，而不是 `Memory::write_symbolic(...)` 之后的事件收集逻辑。

## 关于内存符号化参考的例子
参考`isla-testgen`仓库，可能的位置在`../../isla-testgen`，如果没有及时提醒用户，或者去GitHub自行下载

## `make run` 与 `zSTORE` 产物的当前关系

- `Makefile` 的 `run` 目标当前固定执行：
  `cargo run --bin isarch --release -- -A ./rv64d.ir -C ./configs/riscv64.toml --verbose --probe-all --trace-all list-instructions`
  因此它的显式子命令是 `list-instructions`，不是某个单独的 `zSTORE` 执行命令。
- 根包 `Cargo.toml` 的默认 feature 包含 `debug_exec`，所以 `src/isarch.rs` 会在处理子命令前先调用 `isla_lib::isarch_exec::test_exec_main(...)`。
- `isla-lib/src/isarch_exec.rs` 的 `run_symbolic_execute(...)` 在成功完成某条指令后，会调用 `to_json(Some(format!("output/{}_{}.json", ...)))`，并由 `ToJSON::to_json(...)` 自动创建 `output/` 目录。
- 因此，如果一次运行里真的执行到了 `run_symbolic_execute("zSTORE", ...)`，按当前实现应当直接得到 `output/rv64d_zSTORE.json`；若运行后连 `output/` 目录都没有，优先说明该指令根本没有被送进 `run_symbolic_execute(...)`。
- `test_exec_main(...)` 里虽然定义了多个候选指令表，包括含有 `zSTORE` 的 `todo_instruction_table` 和 `["zSTORE", "zLOAD"]` 的 `excute_through_instruction_table`，但这些 `instruction_table.extend(...)` 语句当前都被注释掉了。
- 由于 `instruction_table` 初始化为空且未被填充，`for ins_name in instruction_table { ... }` 当前不会执行任何指令；这会导致 `make run` 虽然进入了 `test_exec_main(...)`，但不会产出 `zSTORE` 或 `zLOAD` 的 JSON 文件。
