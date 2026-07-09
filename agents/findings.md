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
