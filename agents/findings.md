# Findings

## isarch 符号执行

- `isarch_exec.rs` 的 `run_symbolic_execute(...)` 通过 `execute_ir_function_with_checkpoint(...)` 启动 `zexecute`，只注入 `regs/lets`，没有注入 `Memory`。
- `LocalFrame` 原生持有 `Memory<B>`，提供 `set_memory(...)` 与 `task_with_checkpoint(...)`，可新增传入 `Memory` 的执行入口。
- `read_mem`/`write_mem` primop 直接调 `frame.memory()`，注入 Memory 后 Sail 访存自动走底层模型。
- `Memory::read_symbolic`/`write_symbolic` 产生 `Event::ReadMem`/`WriteMem`，可通过 `solver.trace()` 提取。
- `configs/riscv64.toml` 的 `[symbolic_addrs]` 可作为 symbolic memory region 来源。

## 符号值 concrete 化

- 对需要 concrete 宽度/次数的 primop 参数，`assert(a==1|a==2|...)` 不会自动 fork 出单值路径。
- 需在 Sail 侧用 `match a { 1=>(), 2=>(), ..., _=>assert(false) }` 显式拆分，再在 Rust 端用 `proven_symbolic_i128` 验证。

## VLEN 配置

### 机制

- `const_primops` 只能覆盖 IR 中 extern 函数调用，对 `let` 绑定无效。isla 侧 `default_lets` 机制（`config.rs:get_default_lets` → `init.rs:apply_const_primop_let_override`）在每个 `Def::Let` 求值后立即覆盖 let 值。
- sail-riscv 暂存区改动：`let vlen = sizeof(vlen)` → `let vlen = 2 ^ vlen_exp`，使 IR 中 `zvlen = pow2(zvlen_exp)` 保留依赖链（不被折叠为字面量）。
- IR 审计：函数体内 `zvlen_exp`/`zvlen` 全部引用 let 绑定（各 24 处），无折叠遗漏。

### 为什么不能在 IR 层面做 vlen_exp 变量化

- Sail 的证明义务（pow2 非负性、`to_bits` 范围、`range(1,vlen)` 返回类型等）设计为**编译期常量假设**。
- 将 vlen_exp 改为 register/extern 后，TYPE vlen（编译期 256）与 LET vlen（运行时变量）的语义裂隙导致 Z3 无法消解非线性算术证明（含 `2^vlen_exp` 的指数表达式）。
- 试过 `register : nat`（pow2 过但 to_bits 不过）、`val -> range(3,16)`（VLENB 过但 `get_num_elem -> range(1,vlen)` 不过）等 8 种方案，均因 Z3 非线性算术限制失败。

### 最终方案：预编译多 VLEN IR（2026-06-28）

- **sail-riscv 零改动**，编译多个固定 VLEN 的 IR 放 `isla/ir/`，测试时 `cp` 切换。

| 文件 | vlen_exp | VLEN | ELEN |
|------|----------|------|------|
| `ir/rv64d_v128_e64.ir` | 7 | 128 | 64 |
| `ir/rv64d_v256_e64.ir` | 8 | 256 | 64 |
| `ir/rv64d_v512_e64.ir` | 9 | 512 | 64 |

- **编译方法**：改 `sail-riscv/model/CMakeLists.txt:225` 的 `v256` → `v128`/`v512`，`make -C build-symbolic-vtest generated_isla_rv64d`。必须走 cmake（直接调 isla-sail 脚本会因 `[$1=="-v"]` 语法 bug 丢失 `--isla-preserve` 参数）。
- **config**：从 `[const_primops]` 移除 vlen_exp/elen_exp 条目（IR 已内嵌正确值）。
- **验证**：220/220 通过。

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

## 多线程 limit 机制入口透传（2026-07-09，历史实现记录）

> 本节记录 2026-07-09 的中间实现。后续重构已将计数状态收敛到每个 `Frame` 的
> `ExecutionLimitPathState`；请以当前源码和 `configs/workarounds/vvtype.toml` 为准。

- **入口硬编码缺口**：`isla-lib/src/executor.rs` 的 `execute_ir_function_with_checkpoint_multi_thread`（原 ~:2608）原本在函数体内硬编码 `let task_state = TaskState::new();`（无 limits），导致 `exec.rs` 调用方配置的 `ExecutionLimits` 无法传入多线程执行路径。已改为增加 `task_state: &TaskState<B>` 参数，由 `exec.rs` 构造带 limits 的 `TaskState` 透传。
- **机制本身在多线程下本就可用**，无需改造计数器：`Task.state: &'task TaskState<B>` 是共享引用（fork 时新 Task 携带同一引用，executor.rs fork 点 ~:1504 `state: task_state`），`TaskState.limits_state: Arc<ExecutionLimitsState>` 内含 `Arc<Mutex<HashMap>>` + `AtomicU32`（task.rs ~:143-144），天然 `Send + Sync`；`start_multi` 用 `thread::scope`，所有线程 join 后才返回，故参数 `task_state` 引用生命周期安全。
- **当前计数粒度**：计数状态存于每个 `Frame` 的 `ExecutionLimitPathState`，fork 时随 frame
  clone；`max_forks_per_path`、`max_forks_per_branch` 与 `region_fork_limits` 均为路径局部。
  其中 `max_forks_per_branch` 的 key 是路径内 `ControlFlowScope`，不是跨 worker 的全局配额。
- **dev-multithread 合并遗留的测试破坏**：合并把 `run_loop` 的 fork_sink 参数从 `&Worker` 改为泛型 `S: ForkSink`（trait 仅 impl 于 `SingleForkSink`/`MultiForkSink`），但 `executor.rs` 测试模块里 4 个 helper（`shared_state_and_bindings_from_ir`/`run_all_with_bindings`/`run_with_limits`/`run_all_with_shared_state`）仍传 `&queue`，导致 `cargo test --lib` 不编译（`cargo check` 不编 test 未暴露）。已将 4 处改为 `&SingleForkSink { queue: &queue }`（与 `start_single` ~:1991 同法，行为等价：push 到同一 LIFO queue）。
- **预存无关失败**：`primop::tests::replicate_bits_rejects_unconstrained_symbolic_count`（primop.rs:4214）失败，属 V 扩展 primop 行为/测试不匹配，与 limit 机制无关，不在本次改动范围。

## execution limits 外置 TOML 与 IR 哈希绑定（2026-08-04）

- `--execution-limits-config <path>` 在 `src/isarch_main.rs` 解析，覆盖 `isa_config.execution_limits`；`configs/riscv64_difftest.toml` 不再携带 `[execution_limits]`，`solve_execution_limits`（`src/isarch/exec.rs`）也不再有代码内硬编码 region，无 TOML 时执行限制完全关闭。
- `ExecutionLimitsConfig.strict=true` 要求同时配置 `ir_sha256`，执行前用 `-A` 指定文件的 SHA-256 校验；`strict=false` 时跳过。
- 原 `ir_sha256 = c48050ef…` 对应 `../sail-riscv/build-symbolic-vtest-system-gmp/model/rv64d.ir`，但该产物使用 `rv64d_v256_e64.json`，不是 VLEN=128。现已从当前 `../sail-riscv` 源码使用 `rv64d_v128_e64.json`、`SYMBOLIC=true`、`SYMBOLIC_EXTRA_OPS=true` 重新生成 `ir/rv64d_v128_e64.ir`；它与默认入口 `./rv64d.ir` 的 SHA-256 均为 `7c626989…`。Makefile 默认加载后者，VVTYPE strict 哈希接受这两个逐字节相同的产物。
- `vvtype.toml` 的 gather region 是 VRGATHER `181:6-187:7`、VRGATHEREI16 `190:6-196:7`，比旧硬编码值整体前移 5 行，说明它绑定的是更新后的 sail-riscv 源码；换 IR 时 region 坐标和 `ir_sha256` 必须一起改。
- `branch_region_limits` 是比 `regions` 更窄的 per-region `max_forks_per_branch` 覆盖，多个命中取最小值（`max_forks_per_branch_for_scope`）；未命中任何 override 时回落到 `regions` 过滤后的通用预算。`Monomorphize` 的 fork 经 `on_monomorphize_fork_at` 也走同一套 scope 预算，不再只受 path fork 限制。

## execution limits 的两种预算粒度与抽样采样（2026-08-05 / 08-07，含历史实验）

> 下文的路径数、vtype 覆盖和超时数据均来自启用方向偏置与输出层 `case_quota` 之前的中间实验，
> 不代表当前 `vvtype.toml` 的最终产出。当前配置额外包含 gather 重叠判断的方向偏置，以及
> `[execution_limits.case_quota]` 的非法用例输出配额。

目标口径：**每条具体汇编指令**（vadd.vv、vrgather.vv……）最终生成的 path 不超过 100 条，
超出的部分靠局部限制抽样采样。为此需要区分两种预算粒度：

- **per-scope 预算 `max_forks_per_branch`**：计数 key 是"路径 × `ControlFlowScope`"，
  `ControlFlowScope = (function_name, pc, call_context, source_location)`。一条路径**第一次**到达
  某 scope 时 fork 只把路径数 ×2（线性），**重复**到达同一 scope（循环体逐 lane）才是 2^n，
  所以预算 1 的效果就是"把 2^n 压回 2，线性分支点不受影响"。
- **region 预算 `region_fork_limits.max_forks_per_region`**（2026-08-07 新增）：计数 key 是 region 序号，
  整段源码区间内的所有分支点共享一条路径的 fork 次数。**per-scope 预算压不住 `match` 链**：
  Sail 的 `match` 在 IR 里是一串 `jump @not(eq_int(..))`，每个 arm 判定是不同的 pc、即不同 scope，
  各自都能用掉自己的第一次 fork（实测 `assert_sew` 一条路径 fork 3 次展开 4 路 SEW、
  `assert_lmul_pow` fork 6 次展开 7 路 LMUL）。region 预算 N 才能把 match 链抽样成 N+1 个取值，
  也能把"一个循环体里有多个分支点"的 ×2^k 压成 ×2。

其它要点：

- **没有 Sail 源码位置的分支点选不中**：路径规模最大的分支点是 `zbool_bit_forwards`
  （`prelude.sail:103` 的 `bool_bit` mapping，被 `bool_to_bit` 在 `get_fixed_rounding_incr` 里逐 lane 调用），
  它在 IR 里的 jump 标注是 IR 内部编号 `` `1042 ``（`SourceLoc::unknown_unique`），
  `location_string` 打出来是 `1042:0 - 0:0`，**任何 `regions` / `region_fork_limits` 都选不中它**。
  实测一次运行里它 fork 1304 次，是 vssra/vssrl 路径数（315/261）的唯一来源。
  因此 per-scope 预算必须**不配 `regions`**、让它全局生效；`configs/workarounds/vvtype.toml` 就是这么做的。
- **具体化抽样原本不按路径分叉**：`branch_sample` 的偏好只由 `(seed, scope, 路径内序号)` 决定，
  兄弟路径在同一 scope 上算出同一个方向，于是"抽样"退化成"把这个分支钉死成一个取值" ——
  这就是旧配置下 64 条输出的 `vtype` 全是 `0x15` 的原因。已修：`ExecutionLimitPathState` 增加
  `path_signature`，executor 在两处 fork 点（`Instr::Jump` 与 `Instr::Monomorphize`）分别按 true/false
  推进父/子路径的签名，`branch_sample` 把签名混进哈希。签名只依赖本路径的分叉序列，
  与线程数、调度顺序无关，`path_local_sampling_is_stable_across_worker_counts` 仍成立。
- 因此 region 预算 0 是有意义的配置：**不 fork、只抽样**，只要该分支点在若干次 fork 之后才到达，
  不同路径就会抽到不同取值。预算 0 只有在"任何 fork 之前就到达"时才会退化成单一取值。
- **限制是否命中只在 itrace 里可见**：`executor.rs::record_execution_limit` 只在 `tracetool` feature 下写
  `frame.itrace_path.record_summary(...)`，普通日志（`--debug=f` 的 `[FORK]`）只记录真正发生的 fork。
  所以"某个分支点没有 [FORK] 记录"有两种可能：条件是具体值，或者被限制具体化了，必须用 `ITRACE=1` 区分。
- `masked_select`（`vext_control.sail:293`）在本仓库的 sail-riscv 里是**无分支**实现（用 mask 位运算），
  所以 VV_VADD 这类 arm 的逐 lane 处理本身不会 fork，只有显式写 `if mask[i] == 0b1` 的 arm 才可能。
- VVTYPE 逐指令 path 数实测（THREADS=64）：旧配置（SEW/LMUL 被 0 预算钉死）每条 ≤12 但 vtype 只有
  `0x15` 一个取值；完全放开线性分支点后 28 组 vtype、但 vrgatherei16/vrgather/vssrl/vssra 分别到
  455/449/292/280，总数 >2200 条、40min 跑不完；加上 region 预算与签名修复后回到每条 ≤100。
- **已知缺口：`Monomorphize` 的 case split 是线性的，但复用了同一套 branch 预算**。
  `on_monomorphize_fork_at` 与 `on_branch_fork` 共用 `branch_forks[scope]`，而 monomorphize 的 k 路展开是
  "同一个 scope、同一个 Sym 连续剥值"：父任务取一个 model 值，子任务带着 `v != value` 回到**同一个 pc**
  重新执行同一条 `Monomorphize`。因此 k 个取值需要 k-1 次 fork，预算 1 会把它压成 2 个取值 —— 这在
  "只到达一次"的 monomorphize 点上属于限制线性增长。要彻底区分需要按 scope 记住上一次 monomorphize 的
  `Sym`（同 Sym = 同一次剥值，不同 Sym = 循环下一轮）。VVTYPE 当前 0 次 monomorphize fork，暂未触发。
- `scripts/run.mk` 的 `SOLVE_TIMEOUT`（`isarch --timeout`）经 `executor::PathTimeout` 使用
  `PathTimeSnapshot.active_wall`，是**单条路径**的活跃墙上时钟预算，不是整次运行的上限；
  拦住整体运行的是 Makefile 外层的 `timeout $(OUTER_TIMEOUT)`（超时后 `status=124`，记 `status.timeout.log`）。
  路径预算的检查点在两条 IR 指令之间，所以实际 `active_wall` 会略微超过预算（单条指令不会被抢占）。

## 路径超时诊断：SMT 用时构成与原因判定（2026-08-08，历史测量）

- 三个受保护的 Z3 调用（`Z3_solver_check`、`Z3_solver_check_assumptions`、`Z3_model_eval`）现在都会把
  `(operation, SourceLoc, wall, 是否被中断)` 记进线程局部的 `timeout::SmtCallStats`。统计始终开启
  （只有几个标量，相对 Z3 调用可以忽略），与 `smtperf` feature 的"最慢/最快样本列表"是两套东西。
  `executor::run_loop` 在每条路径开始时 `smt::reset_path_smt_stats()`，所以线程局部 == 路径局部
  （一个 worker 线程同一时刻只推进一条路径）。
- `SourceLoc` 由 `Solver::check_sat{,_with}` 的调用点透传进 wrapper，`Model` 侧的 `ModelEval` 没有调用点
  信息，记为 `SourceLoc::unknown()`。因此"最慢单次"能直接定位到 Sail 源码行。
- 路径撞上 `--timeout` 时 `executor::report_path_timeout` 输出 `timeout::PathTimeoutDiagnostic`，
  判定规则见 `spec/smt_timeout.md`：被中断调用累计 ≥ 预算 50% ⇒ `SmtOperationTimeouts`（放宽
  `--timeout` 无效）；SMT 累计 ≥ active_wall 70% ⇒ `SlowSmtSolving`（确实需要更多预算）；否则
  ⇒ `ExecutorWork`（瓶颈在解释执行）。输出走 `log::SYM_EXEC`（`--debug` 里的 `s`），itrace 构建下
  同时写进 trace summary。诊断里还带**控制流步数**和**按调用点聚合的最热求解位置**，前者用来排除
  死循环（死循环会到百万级），后者用来定位是哪一行 Sail 在反复求解。

## VVTYPE 单路径超时的真正根因：`proven_symbolic_i128` 的候选枚举（2026-08-08，历史测量）

- 实测（`--timeout 60s`）：控制流步数只有 **484~555**，说明**不是死循环**；但同一次超时里
  **1034 次求解中的 1034 次都来自同一个 Sail 位置** `vext_arith_insts.sail 177:40-177:83`，也就是
  `VV_VMAX` 逐 lane 的 `max(signed(vs2_val[i]), signed(vs1_val[i]))`。另一条路径是 2068 次 —— 正好 2 倍。
- 原因在 `isla-lib/src/primop.rs::proven_symbolic_i128`：它判断"这个符号 int 是否已被路径约束证明为
  唯一常量"的方式是**逐个候选值问 solver `sym != candidate` 是否 unsat**，候选集是 72 个常用值
  **再链上 `0..=512` 里剩下的所有整数**，合计约 515 个。对向量元素这种永远证明不出唯一值的符号量，
  515 次查询全部落空。`max_int`/`min_int` 会对**两个**参数各做一次 `concretize_proven_i128`，
  所以**一次 `max()` ≈ 1030 次 check-sat-assuming**，与实测的 1034 完全对上。
- 于是 VMIN/VMINU/VMAX/VMAXU 这四条（`vext_arith_insts.sail` 165/169/173/177）成了唯一会超时的 arm：
  一个 lane 就要 ~1030 次求解，num_elem=32~128 时一条路径要 3.3 万~13 万次。30m 预算内只跑完
  5248~11456 次（约 5~11 个 lane）。它们在 JSON 里条目最少（vmax.vv 只有 2 条）也是这个原因。
- 而且**越往后越慢**：60s 内平均 45ms/次，30m 内平均 366ms/次（公式随 lane 累积增长），所以单纯放宽
  `--timeout` 收益是次线性的。
- **已修（2026-08-10）**：`proven_symbolic_i128` 改成模型法——先 `check_sat` 取一个模型值 `v`
  （`Model::get_var`，模型没给它赋值即 `ModelVal::Arbitrary` 时直接判定"不唯一"），再查
  `sym != v` 是否 unsat。判定固定 1 次 check-sat + 1 次模型求值 + 1 次 check-sat-assuming，
  且不再受候选集范围限制（70000、-4096 这类以前证不出来的值现在也能具体化）。
  实测 `make solve-VVTYPE`：**52m/29 条超时 → 6m27s/0 条超时**，路径数 423、逐指令 ≤100 不变，
  vmin/vmax/vminu/vmaxu 从 2~6 条恢复到各 8 条（原来都死在超时上）。
  `scripts/run.mk` 里给 VVTYPE 单独放宽的 `OUTER_TIMEOUT` 也随之删掉，回到默认 40m。
- **对其它 clause 是中性的**（同参数 A/B，新旧两个二进制各跑一遍）：`DIVW` 旧 47s / 新 49s，
  都是 26 条路径、都通过；`AES64IM` 在 620s 上限内旧 1179 条 / 新 1181 条，两边都跑不完。
  说明这两类慢是**本来就有的**，不是这次改动引入的：
  - `DIV`/`DIVW` 的 `quotient >= 2 ^ 31`（`mext_insts.sail:128`）单次查询要 ~50s，单跑能过，
    但 `make solve -j` 并行下墙上时钟会冲过 60s 的 `--smt-timeout` 而失败；
  - `AES64IM` 这类是路径数天然多（>1179 条），与具体化无关。

## 未约束枚举字段的取值会把非法用例全记到同一条子指令上（2026-08-11，方向偏置与配额前的历史测量）

- 在 funct6 dispatch 之前就 `return Illegal_Instruction()` 的路径根本没有约束过 funct6，
  collector 里 `model.get_val(&fun_args[0])` 每次都会拿到 Z3 给的同一个成员（枚举第一个），
  于是这些非法用例全被标注成同一条子指令。VVTYPE 实测 vadd.vv 因此被顶到 196 条，
  其它子指令一条非法用例都分不到。
- 修法在 `src/isarch/exec.rs::diversify_unconstrained_enums`：求最终 model 之前，按
  `frame.path_signature()`（executor 在每个 fork 点分叉的路径签名）给每个符号枚举字段挑一个
  候选成员，`check_sat_with` 能满足就 `Assert` 钉住；路径本身已经约束住的字段候选值会 Unsat、
  直接跳过，所以不改变任何路径的语义，只影响"任意值"的取法。
  实测 vadd.vv 196 → 58，394 条非法用例散布到各条子指令上。
- 同一个道理适用于寄存器号等其它未约束字段（现在仍然全是 Z3 默认值，用例里大量 `v0`）；
  要扩展的话把这个函数从"只处理枚举"放宽即可。

## sail-riscv 生成 VLEN=128 Isla IR 的方法（2026-08-05）

- `../sail-riscv/model/CMakeLists.txt:225` 把 IR/SMT/Coq 等 formal 目标的 config **写死**为 `config/rv${xlen}d_v256_e${xlen}.json`，所以 `cmake --build build --target generated_isla_rv64d` 产出的 `build/model/rv64d.ir` 恒为 **VLEN=256**（`vlen_exp=8`）。仓库根目录的 `rv64.ir` 就是这么来的。
- `config/CMakeLists.txt` 会为 XLEN∈{32,64} × ELEN_EXP∈{5,6} × VLEN_EXP∈{7,8,9} 生成 12 份 JSON 到 `build/config/`，其中 `rv64d_v128_e64.json` 即 `vlen_exp=7`(VLEN=128)、`elen_exp=6`(ELEN=64)、`support_level=Full`。改 VLEN 只需换 `--config`，**不必改 CMakeLists**。
- 绕过 CMake 直接调 isla-sail（`SR=<sail-riscv 绝对路径>`，工作目录必须是 `$SR/model`）：
  ```
  env PATH="<isla>/isla-sail:$PATH" isla-sail \
    --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.1 \
    --memo-z3-path "$SR/build/model/sail_smt_cache" \
    --isla-preserve encdec_compressed_forwards --isla-preserve encdec_compressed_forwards_matches \
    --isla-preserve encdec_compressed_backwards --isla-preserve encdec_compressed_backwards_matches \
    --isla-output-dir "$SR/build/model" -o rv64d_v128_e64 \
    --config "$SR/build/config/rv64d_v128_e64.json" --all-modules riscv.sail_project
  ```
  耗时约 12 分钟；`-o` 换名可避免覆盖 `build/model/rv64d.ir`。原始命令行可用 `grep isla-sail build/model/CMakeFiles/generated_isla_rv64d.dir/build.make` 取得。
- **构建是确定性的**：用上述命令重新生成的 IR 与 `isla/ir/rv64d_v128_e64.ir` **逐字节一致**（`7c626989…`），与 `configs/workarounds/vvtype.toml` 的 `ir_sha256` 相符。校验 IR 版本时可直接对比 SHA-256，不必重新生成。
- IR 里判断 VLEN/ELEN 的位置：`let (zvlen_exp: %i64)` 与 `let (zelen_exp: %i64)` 中的 `zz5i64zDzKz5i(N)`，VLEN=2^N。
