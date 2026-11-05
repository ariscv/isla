# 路径合并：让分支臂支持函数调用（计划，未实施）

## 目标
合并分支臂时，臂内可以正常调用 Sail 函数（字段读取器、`currentlyEnabled`、`is_prefetch_access`、构造器等），语义与普通路径完全一致；不在 `simulate_diamond_arm` 里另写一份调用逻辑。

## 现状与依据（2026-11-05，单次 60 秒 Sv39 观测）
- 合并尝试 736 次、成功 0 次；臂内 `call` 被拒 336 次，另有 `impure_binary` 168（`range_subset`）。见 `agents/execution_stats/result-20261105-sv39-60s.md`。
- 根因：`simulate_diamond_arm`（executor.rs）是一个独立的小解释器，没有调用、返回、`have_exception` 边、限制记账。给它补调用等于第二次实现主循环语义。

## 技术路径（2026-11-05 修订：一步到位的区域合并，不分阶段）

参照 Veritesting 一类的成熟做法：在符号分支处把"到汇合点为止的整块区域"一次性在真实解释器里推演完，区域内部的分叉递归合并，汇合处用 ITE 合成；任何环节失败则整体回滚，退回普通分叉。

1. 汇合点：用函数内控制流图的直接后支配点（immediate post-dominator）取代 `detect_diamond_joins` 的"菱形/三角 + pc+64 窗口"。按函数惰性计算并缓存在 SharedState。OR 短路链里每个析取项的跳转共享同一个后支配点，因此无需窗口限制，也不再产生"三角候选"的伴随失败。
2. 区域执行：两臂都通过真实主循环 `run_loop_inner` 以"推演模式"执行，到达（入口栈深度，pc == 汇合点）停止。退休 `simulate_diamond_arm`。被调函数在栈上正常进出，所有深度共享一个步数预算。
3. 区域内分叉：推演模式下遇到符号 Jump 时，递归地对该分支做同样的区域合并（以其后支配点为界），递归深度有上限。求解器改为保存点栈（savepoint stack，替换 smt.rs 中禁止嵌套的单层事务）；内层失败只回滚到内层保存点并让外层整体失败。单边可行的跳转直接走可行的一边，不加断言（前提：可行性查询已包含当前事务条件）。
4. 其他一切会产生真实分叉的位置（Monomorphize、操作数重试、`symbolic_length`、限制处理器分叉）：在检查点和 fraction 变更之前拒绝，不能靠丢弃任务。
5. 副作用规则：内存访问原语、announce、不在纯函数白名单内的原语一律在执行前拒绝；白名单补齐 `lteq_bits_u` 并审计同族（lt/gt/gteq 有无符号）。被调函数内部禁止写寄存器和 let（含 `have_exception`）；入口深度允许写寄存器（与现状一致）。
6. 状态记录：入口作用域的 vars/lets 用执行前后差分；寄存器读写、写入顺序、重复写在共享赋值器和寄存器路径集中记录，保持合并后"补发 ReadReg/WriteReg 事件"的契约。
7. 区域内局部变量：在 `[起点, 汇合点)` 内声明、之后不再被引用的临时变量，在合并处丢弃，不再因"只存在于单臂"而拒绝（否则 `pte_is_invalid` 的 `&` 分支临时变量会让调用支持白做）。
8. 失败语义：任何拒绝（副作用、分叉、预算、递归深度、帧合并拒绝、事务失效）都回滚到最外层保存点，按普通分叉继续；拒绝原因沿用 `ISLA_STATS` 的标签并随之更新。
9. 需把 `tid/task_id/task_fraction(复制)/timeout/stop_conditions/task_state` 传入合并入口（调用点 executor.rs 约 2536 行已有）；`last_z3_reset` 在推演期间保持禁用。

代码改动面：executor.rs（区域执行、停止条件、推演模式规则）、smt.rs（保存点栈）、primop.rs（白名单）、新增后支配点分析（可放 ir.rs 或独立模块）。

实施顺序只是工作拆分，不是分阶段验收：先写测试（合成 IR：纯调用、`&` 短路带调用、被调函数写 `have_exception` 应拒绝、臂内读内存应拒绝、四项 OR 链合成 1 条、嵌套分叉、区域内局部变量），再实现，最后一并验收。

## 验收
1. 函数级 `pte_is_invalid`（可跑完）：不合并 N 条路径；合并后 1 条；Z3 证明合并返回值等价于各 fork 路径结果的析取；对 flag/ext 位暴力枚举核对。
2. 60 秒 Sv39：`successes > 0`（端到端确认，不作为主要证据）。
3. 现有 `stats`/`diamond`/`path_merging` 测试保持通过。
4. 已知 HEAD 即失败的 5 个 `merge` 测试（`internal_vector_init_after_merge`、`monomorphize_machine_integer_after_merge_does_not_crash`、`internal_vector_update_retries_merged_index`、`review21_merged_overflow_path`、`adversarial_merge_machine_index_width`）先写入 `agents/findings.md`，避免算到本改动头上。

## 未决
- 后支配点在含 `have_exception` 提前退出边的函数里的具体定义（退出边指向函数末尾，需确认纯调用后条件恒假时的处理）。
- `range_subset` 的 `lteq_bits_u` 在白名单中缺失，是遗漏还是有意排除（Codex 判断为遗漏，未证实）。
- 臂内 `have_exception` 边在纯函数调用后恒为假，需确认真实循环下不会被当作越界。
