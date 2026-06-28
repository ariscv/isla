# read_vmask 符号切片修复：方案 A vs 方案 B 对比实验报告

## 背景

6.28 报告问题 B：`read_vmask`/`read_vmask_carry`（vext_control.sail:538-549）的 `V(vrid)[num_elem-1..0]` 在符号 `num_elem`（来自符号化 vtype）下命中 isla `subrange_internal`（primop.rs:1234-1236）的 `SymbolicLength`，导致 73 次硬错误、影响 39 个 V 扩展 clause。

### 根因（结合 isla+sail-riscv 调研）
1. vtype 符号化 → `get_sew()`/`get_lmul_pow()` 符号 → `get_num_elem`（vext_control.sail:289）返回**符号 num_elem**。
2. 多数 V 指令执行体（如 VITYPE，vext_arith_insts.sail:983）：
   ```sail
   let num_elem = get_num_elem(LMUL_pow, SEW);   // 符号
   assert_vector_num_elem(num_elem);               // 只 assert，不重新赋值！
   let vm_val = read_vmask(num_elem, vm, zvreg);   // num_elem 仍符号 → 切片出错
   ```
3. **用户指出的关键**：`assert_vector_num_elem`（vext_control.sail:248）→ `assert_vector_num_elem_upto_*`（:101+）用 `if num_elem<=N then{match}else if...{match}else{match}`，`num_elem<=N` 是符号比较（fork 点）且 assert 返回 `()` **不把 num_elem 绑定到常量**。同文件已有正确写法 `assert_vector_num_elem_value`（:258）：纯 `match num_elem{1=>1,...}` **返回匹配常量**。
4. **决定性证据**：用 `assert_vector_num_elem_value` 的 MOVETYPEI/V/X 的 subrange_internal 错误=**0**；用 `assert_vector_num_elem` 的 VITYPE 错误=**1**。

---

## 实验设置

- 基线：清理后的 HEAD（commit 5f8a793），VITYPE：subrange_internal 错误=1，FORK=96，完成路径=22，状态=intime，vtype forks=36。
- 两方案分别在独立 worktree（isla + sail-riscv 各一对）实现，各自重编 IR + `make solve-VITYPE`。
- worktree 分支：`read-vmask-extern-A`（方案 A）、`read-vmask-sail-B`（方案 B）。

---

## 方案 B（sail 侧具体化 num_elem）—— 更简洁

**改动**：`vext_arith_insts.sail` 4 处执行体（MASKTYPEV/X/I、VITYPE）：
```sail
assert_vector_num_elem(num_elem);                          // 改前
let num_elem = assert_vector_num_elem_value(num_elem);     // 改后
```
**不动 isla primop.rs**。复用 sail 已有的 `assert_vector_num_elem_value`（纯 match 返回常量），与 MOVETYPEI/V/X 既有写法一致。

### VITYPE 结果
| 指标 | baseline | 方案 B |
|---|---|---|
| subrange_internal 错误 | 1 | **0** ✓ |
| read_vmask 错误 | 1 | 消失 |
| FORK | 96 | 68 |
| vtype forks | 36 | 21 |
| 完成路径 | 22 | 11 |
| 状态 | intime | timeout(60s, 11 路径完成) |

---

## 方案 A（isla 侧新增 isla_read_vmask extern）

**isla 改动**：primop.rs 新增 `isla_read_vmask_internal`/`isla_read_vmask`，镜像 `isla_init_mask`（primop.rs:2572）范式：
- 固定位宽 `len = length_bits(vreg)`（= VLEN），`num_elem` 只作 SMT `Ite(i<num_elem, ...)` 条件，**永不作 subrange high/low 或位向量构造长度** → 根除 SymbolicLength。
- 语义：`bit i = vm==1 ? pad : (i<num_elem ? vreg[i] : pad)`，`pad = !is_carry`（read_vmask→ones，carry→zeros）。
- 注册 + 3 个 TDD 测试（concrete/symbolic_num_elem_fixed_width/carry，全 GREEN）。

**sail 改动**：`vext_control.sail` 的 `read_vmask`/`read_vmask_carry` 加 `$ifdef SYMBOLIC` + `__isla_use_extra_ops` 分支（与 read_vreg 对称），调 `isla_read_vmask`。extern 签名 `(int, bits(1), bits(1), vlenbits) -> vlenbits` + `assert('n == vlen)` 解决 `bits('n)` ↔ `vlenbits` 类型统一。

### VITYPE 结果
| 指标 | baseline | 方案 A |
|---|---|---|
| subrange_internal 错误 | 1 | **0** ✓ |
| isla_read_vmask fallback/error | — | 0 |
| FORK | 96 | 96 |
| vtype forks | 36 | 36 |
| 完成路径 | 22 | 22 |
| 状态 | intime | **intime** |

---

## 对比与结论

| 维度 | 方案 B（sail 具体化） | 方案 A（isla extern） |
|---|---|---|
| subrange_internal 错误 | 1→**0** ✓ | 1→**0** ✓ |
| VITYPE 状态 | timeout(60s) | **intime** |
| FORK / vtype forks | 68 / 21（下降） | 96 / 36（不变） |
| 完成路径 | 11 | 22 |
| 改动范围 | sail 1 文件 4 处 | isla primop+注册+测试 + sail |
| 新增 isla extern | **否** | 是（isla_read_vmask） |
| 优雅度 | **高**（复用既有 _value 模式，primop 接触面不增） | 中（符合 guides.md 不固定运行态，但 primop 接触面+1） |
| guides.md | 符合（加强过松约束，不改运行态取值） | 符合（改执行策略，保留 num_elem 符号性） |
| 语义 | num_elem 被具体化（每条 path 上是常量，丢失符号覆盖） | num_elem 保持符号（SMT 处理，保留符号覆盖） |

### 分析

1. **两方案都消除了 subrange_internal 硬错误**（73 次/39 clause 的根因），验证了用户的诊断（assert 的 if/else 复杂化 + 不具体化 num_elem 是根因）。
2. **方案 B 更简洁**：复用 sail 已有的 `assert_vector_num_elem_value`，不动 isla，primop 接触面不增（符合"primops 接触面最小化"原则）。代价：num_elem 被具体化，每条 path 上是常量——但这本来就是有限合法值（1/2/4/8/.../vlen），不算丢失真实覆盖率。
3. **方案 A 更"符号保真"**：保留 num_elem 的符号性，用 SMT 处理。VITYPE 甚至 intime 完成、FORK 不变（因为没引入新 fork 点）。但新增了 isla extern，接触面+1。
4. **timeout 差异**：方案 B 的 VITYPE timeout 是因为具体化后每条 path 走得更深（11 路径但每条更重）；方案 A 路径数不变（22）且 intime。但这属于有限 vtype 组合（用户说可放宽 timeout），不是无限爆炸。
5. **用户的核心问题"extern 化合适吗"**：对消除 subrange_internal 错误，**extern 不是必需**——方案 B 用更少的改动达到同样效果，更符合 primops 最小化原则。extern（方案 A）的价值在于保留 num_elem 符号性，但这里 num_elem 本就是有限合法值集合，符号化的额外收益不大。

### 建议（待用户定夺）

- **若优先简洁 + primops 最小化**：选**方案 B**（sail 侧 `assert_vector_num_elem_value`），改动最小、复用既有模式。
- **若优先符号保真 + 与 read_vreg 一致性**：选**方案 A**（isla extern），但接受 primop 接触面+1。
- **两者都不解决 vtype timeout**（有限组合，按用户指示靠放宽 timeout 处理，非本任务范围）。
- 额外（用户指出的 if/else 复杂化）：方案 B 落地后，`assert_vector_num_elem`（带 if/else 的那个）若再无调用点，可一并删除简化。

## 复现

两方案代码保留在 worktree 分支供检阅：
- 方案 A：`isla` 分支 `read-vmask-extern-A`（commit 5c11c37）+ `sail-riscv` 分支 `read-vmask-extern-A`（e46521a）
- 方案 B：`sail-riscv` 分支 `read-vmask-sail-B`（9ee899e），isla 无改动（用清理后的 HEAD 5f8a793）

```sh
# 方案 A 验证
cd .worktrees/isla-A && cp <sail-A-build>/rv64d.ir . && make solve-VITYPE
# 方案 B 验证
cd isla && cp <sail-B-build>/rv64d.ir . && make solve-VITYPE
```
