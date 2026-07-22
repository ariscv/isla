# Isla V 扩展符号执行问题报告（6.28）

## 范围与来源

- 本报告针对 RISC-V **V 扩展** 指令在 isla 上的符号执行结果。
- 数据来源：当前分支 `dev-isarch-runall-ext`（HEAD `f18f3d4 "runall: 用 target pre-state 求解 ISA 状态并恢复 V 扩展寄存器符号化"`）执行：
  ```sh
  rm -rf output/ && make solve -j32
  ```
- 产出：`output/status.intime.log`、`output/status.timeout.log`、`output/log/*.log`（共 220 个 clause）。
- 全文所有 `file:line`、日志计数、错误分类均已通过 41 个并行调查/对抗式验证 agent 在实际代码与日志上交叉确认；标注为「已验证」的结论可直接据此行动，标注「uncertain」的需后续实验。
- 报告命名与前序报告一致（`reports/<日期>_<主题>/report.<日期>.md`，参考 `6.14_test_solve_all`、`6.16_test_solve_all`）。

## 运行概况

| 指标 | 数值 |
|---|---:|
| ACTIVE_ALL clause 总数 | 220 |
| intime | 157 |
| **timeout** | **63** |
| 含执行错误（`执行错误:`）的日志文件数 | 69 |
| 非 timeout 的硬执行错误总次数 | 73 |

### 与历史的对比（关键回归）

| 配置 | V 扩展 timeout | 总 timeout | 来源 |
|---|---:|---:|---|
| 干净 isla + 干净 IR + `vtype=0x10` 约束（2026-06-25 验证） | **0** | 4（全非 V） | MEMORY `solve-timeout-set-and-symbolic` |
| 当前分支 `dev-isarch-runall-ext`（本报告） | **~59** | 63 | 本次 `make solve -j32` |

V 扩展 timeout 从 0 暴涨到 ~59，是一次明确的**回归**。根因见下文问题 A。

### 错误类型分布（已验证，与 6.16 完全不同）

本轮扫描确认**没有** panic、没有 `LoopLimitReached`、没有 `AssertionFailure`（6.16 的高频问题在本轮均已消失或被 MEMORY 记录的 `__isla_use_extra_ops` 路线解决）。当前只剩两类：

| 错误 | 出现次数 | 影响日志数 | 性质 |
|---|---:|---:|---|
| `subrange_internal` `SymbolicLength` @ `vext_control.sail:541`（`read_vmask`） | 65 | 33 | 硬执行错误 |
| `subrange_internal` `SymbolicLength` @ `vext_control.sail:548`（`read_vmask_carry`） | 8 | 4 | 硬执行错误 |
| `Timeout(Timeout)` | 142 | 63 | 超时 |

> 说明：73 次 `subrange_internal` 硬错误分布在 39 个 clause（23 个同时 timeout、16 个 intime）。`Poison` 仅出现在 LPAD/MRET/JALR/ECALL/SRET/WFI 的**警告**中（非执行错误，与 6.18 修复 LPAD panic 一致），不计入问题表。

---

## 1. 问题总览表

| # | 问题 | 类型 | 影响 clause 数 | 根因摘要 | 优先级 |
|---|---|---|---:|---|---|
| **A** | **vtype 符号化导致 V 扩展组合爆炸** | 配置回归 | ~59（几乎全部 V 扩展/vector crypto timeout） | TOML `[registers.defaults]` 缺 `vtype` 条目 → `init.rs` 留 `Uninit` → 执行期惰性符号化 → `assert_sew`(4路)/`assert_lmul_pow`(7路) match 分叉 + `hartSupports` 散列函数 2^67 枚举 + 符号位宽穿透 | **最高** |
| **B** | **`read_vmask`/`read_vmask_carry` 缺 SYMBOLIC/extra-ops 分支** | 执行路径补漏 | 39（73 次 `subrange_internal` 硬错误，`vext_control.sail:541/:548`） | mask 读辅助函数被漏掉 extern 化，`V(vrid)[num_elem-1..0]` 在符号 `num_elem` 下命中 isla `subrange_internal` 的 `SymbolicLength` | **高**（与 A 同源；A 修好可缓解，根治需补 extern） |
| **C** | **AES64ESM / AES64DSM MixColumns 符号表达式爆炸** | 符号位运算嵌套 | 2 | `xt2`/`gfmul` 对符号字节 3 层嵌套 + `bit_to_bool(x[7])` 路径分叉；非 M 变体 ES/DS 不 timeout | 中 |
| **D** | **CSRImm / CSRReg CSR 地址符号化** | dispatch 路径爆炸 | 2 | `csr`(bv12) 符号化 → `read_CSR`/`write_CSR` 191 条 clause 对每个候选地址逐一 FORK + `cur_privilege` 符号化 | 中 |

> 63 个 timeout = 59 个 V 扩展/vector crypto（问题 A，含 MMTYPE/NITYPE/NXSTYPE/ZVKSHA2TYPE，均为 vtype 驱动）+ 4 个非 V（问题 C/D）。

---

## 2. 问题 A：vtype 符号化导致 V 扩展组合爆炸（最高优先）

### 现象（日志证据，已验证）

- `output/status.timeout.log` 63 行中 ~59 行为 V 扩展/vector crypto：`VITYPE`、`VXTYPE`、`VANDN_VV/VX`、`VAES*`、`VCLMUL*`、`MASKTYPE*`、`MOVETYPE*`、`MVV*`/`MVX*`、`NV*`、`RIVVTYPE`/`RMVVTYPE`、`VBREV*`、`VCLZ_V`/`VCPOP_V`/`VCTZ_V`、`VEXTTYPE`、`VGHSH_VV`/`VGMUL_VV`、`VICMPTYPE`、`VID_V`、`VIM*`、`VMS*_M`、`VMVRTYPE`、`VREV8_V`、`VROL_*`/`VROR_*`、`VSHA2MS_VV`/`VSM3C_VI`/`VSM3ME_VV`/`VSM4K_VI`，以及 `MMTYPE`/`NITYPE`/`NXSTYPE`/`ZVKSHA2TYPE`。
- 典型 `output/log/VITYPE.log`：
  - 全程 `[FORK] ... taints: ["vtype"]`（如行 9-28、132、681、1110），分叉点集中在 `vext_control.sail:29-35`（`assert_sew` 的 match）与 `:39-48`（`assert_lmul_pow` 的 match）。
  - `taints:["vtype"]` 是绝对主簇，远超 `vstart`/`vl`。
- 同样地 `NXSTYPE.log` 的 FORK（84 次）中 38 次为 `["vtype"]`，`ZVKSHA2TYPE.log` 的 FORK（266 次）中 77 次为 `["vtype"]`、25 次 `["vstart"]`、25 次 `["vl"]`——证明这 4 个被前序调查单列的 clause **同属 vtype 驱动**，不是独立类别。

### 根因（代码证据链，逐环已对抗式验证为 true）

```
TOML [registers.defaults] 缺 vtype 条目
  → isla-lib/src/init.rs:133-137 把 vtype 插为 UVal::Uninit
  → 执行器首次读 CSR vtype（get_sew_pow / get_lmul_pow）时惰性符号化
     （register.rs:120-123 read() 对 Uninit 调 symbolic()；
       executor.rs:79-101 get_and_initialize 同样把 Uninit 替换为 symbolic）
  → vtype 为自由符号值（vill / vsew[5:3] / vlmul[2:0] / vta / vma 全自由）
  → get_sew()     = 2^(unsigned(vtype[vsew])+3)  符号   (vext_regs.sail:338-350)
  → get_lmul_pow()= signed(vtype[vlmul])         符号   (vext_regs.sail:358-362)
  → assert_sew(SEW)      match 4 路  @vext_control.sail:28-36   FORK["vtype"]
  → assert_lmul_pow(LMUL) match 7 路 @vext_control.sail:38-49   FORK["vtype"]
  → SEW∈{8,16,32,64} × LMUL_pow∈{-3..3} = 28 组合，下游再叠加 vma/vta/vstart/vl
  → hartSupports/valid_vtype 散列函数在符号枚举下 2^67 爆炸
  → ~59 个 V 扩展/vector clause 超时
```

关键事实（全部已验证）：

1. **vtype 不在 `reg_list()` 白名单**（`src/isarch/target.rs:355-363`：仅 `x0-31`/`f0-31`/`vr0-31`/`PC`/`cur_privilege`/`mstatus`）。因此 `setup_pre_state`（`target.rs:69-110`）**不会主动符号化 vtype**——回归与 pre-state 符号化机制无直接因果。
2. **TOML 缺 vtype 条目**：`configs/riscv64_difftest.toml`（Makefile:7 实际加载）的 `[registers.defaults]` 仅有 `vr0-31`/`satp`/`misa`/`mstatus`/`__isla_*` 等；全仓 `grep vtype configs/*.toml` 零命中。IR 中 `zvtype`/`zvl`/`zvstart` 是真实寄存器（`rv64d.ir:34989/34685/34683`），TOML 本可约束但未约束。
3. **加载链**：`config.rs:732-767 get_default_registers` → `init.rs:119-132`（命中 `UVal::Init`）/ `133-136`（未命中 `UVal::Uninit`）。vtype 未命中 → Uninit → 执行期惰性符号化。
4. **`vtype=0x10` 解码**（bitfield 定义见 `vext_regs.sail:317-324`，`vill:xlen-1 / reserved / vma:7 / vta:6 / vsew:5..3 / vlmul:2..0`）：`0x10 = 0b00010000` → `vill=0, vma=0, vta=0, vsew=0b010 → SEW=32, vlmul=0b000 → LMUL_pow=0`。
5. **`assert_sew`/`assert_lmul_pow` 的 match 在符号值上必然 fork**：IR（`rv64d.ir:35273 zassert_sew`）中 `match SEW {8,16,32,64,_=>assert(false)}` 被编译成一串 `jump @not(zeq_int(SEW, const))` 条件分支；当 `SEW` 是符号 `Val::Symbolic` 时，`executor.rs` 的 `Instr::Jump` 对每个候选 `zeq_int` 用 `check_sat_with` 判定 true/false 可行性，SAT/UNSAT 两路都可行 → fork。`assert_lmul_pow` 同理（6 个 jump = 7 路）。
6. **历史对照（MEMORY `solve-timeout-set-and-symbolic`）**：干净 isla + 干净 IR + `vtype=0x10` → 216/220 通过、仅 4 个非 V timeout。当前分支丢失该约束 → 纯配置回归，非 executor/primop/IR 代码回退。

### 与已证伪断言的纠偏（避免误判）

- ❌ "符号 `num_elem` 驱动 `foreach(i from 0 to num_elem-1)` 边界符号化导致 timeout" —— **验证为 false**。符号 `LMUL_pow`/`SEW` 在 `get_num_elem` 内部就被 `assert_sew`/`assert_lmul_pow` 的 match 枚举收敛为具体值，foreach 边界在每条 path 上是具体值（定数展开、无回边）。符号 `num_elem` 的唯一可观察下游是 `read_vmask` 的 `subrange SymbolicLength`（位向量切片，非循环），属问题 B。
- ❌ "`f18f3d4` 把 vr0-31 加回 `reg_list` 是 V 扩展规模爆炸 pre-state 主因" —— **验证为 false**。机制属实（32 个 256bit vr 被符号化覆盖 TOML 全零默认），但因果归因错误：`vr0-31` 全程仅 1 次 taint，而非 V 扩展的 intime 日志带相同 vr 符号化却能正常完成。真正主因是 **vtype 符号化**。
- ❌ "本轮 `output/log` 是 stale run 产物" —— **验证为 false**。log 的实际 mtime 为 2026-06-28，比 `target.rs`（6/27）更新；日志 `ARCH_INFO` 含 `vr0-31`，是反映当前代码行为的有效日志。

### 建议（结合 `agents/guides.md`）

guides.md 原则（已验证，与 sail-riscv 类型定义一致）：
- **禁止** 把 `vl`/`vstart`/`vtype` 等运行态在 Isla 入口层固化为**单一代表值**（guides.md:5）。
- **允许** 固化 vlen/elen/xlen 等不可变配置参数（guides.md:7）。
- **鼓励** 加强 Sail 中已过松的约束，如 `SEW∈{8,16,32,64}`、`LMUL_pow∈-3..3` 排除保留编码（guides.md:9-10）——这与 `vext_regs.sail:328` `type LMUL_pow = range(-3,3)`、`:345` `type sew_bitsize = {8,16,32,64}` 完全吻合。

| 方案 | 做法 | guides.md 适配 | 收益 |
|---|---|---|---|
| **短期（保底）** | TOML `[registers.defaults]` 补 `vtype = "0x10"`（恢复历史验证过的 216/220 基线） | 字面上属"固定单一值"，与 guides.md:5 有字面张力；但作为"先恢复基线再提升覆盖率"的工程步骤可接受 | 立即消除绝大多数 V 扩展 timeout |
| **长期（推荐）** | 在 sail-riscv 侧给 vtype 加**合法域约束**而非单点；或按 SEW/LMUL 合法笛卡尔积（28 组合）切分多个 TOML profile / 多 IR 分别跑（findings.md 已有 `rv64d_v128/v256/v512_e64.ir` 多 VLEN 模式可类比） | 完全符合 guides.md | 保留符号覆盖率，治本 |

TOML 改动草图（短期，复刻历史成功方案）：

```toml
# [registers.defaults] 段内补充：
# vtype = vill(0) | vma(0) | vta(0) | vsew(0b010->SEW=32) | vlmul(0b000->LMUL_pow=0)
#        [vill=0][reserved][vma=0][vta=0][vsew=010][vlmul=000] = 0x10
vtype = "0x10"
```

> **重要**（findings.md 第 9-12 行已记）：`assert(a==1|a==2|...)` **不会自动 fork 出单值路径**——assert 只丢弃非法路径，不减少合法路径数。sail-riscv 当前 HEAD `0a6375a5 "V扩展assert限制取值范围"` 若只是加 `assert`，对 fork 无效。要真正减少合法路径数，必须把 vtype 固定/收窄（TOML 单值）或在 Sail 用 `match v { 0x10=>(), ... _=>assert(false) }` 显式拆分。
>
> **关键不动项**（用户明确选择，勿擅改）：`src/isarch/exec.rs:357` 的 `// model.set_complete_model(true);` 保持注释（MEMORY `prestate-target-symbolization` 记载：当前语义是"只输出 solver 真正约束的 pre-state 寄存器"）。

---

## 3. 问题 B：`read_vmask`/`read_vmask_carry` 缺 SYMBOLIC/extra-ops 分支

### 现象（已验证）

- 73 次 `subrange_internal` 的 `SymbolicLength` 错误，全部来自 `vext_control.sail:541`（65 次，`read_vmask`）或 `:548`（8 次，`read_vmask_carry`），调用栈 `zread_vmask`/`zread_vmask_carry`，FORK taints 含 `vtype`。
- 例：`output/log/VABS_V.log:47/:87` 报 `Symbolic (bit)vector length in subrange_internal ... [extensions/V/vext_control.sail 541:54 - 541:80]`，列 54-80 正是 `V(vrid)[num_elem - 1 .. 0]`。

### 根因（已验证为 true）

`read_vmask` / `read_vmask_carry`（`vext_control.sail:538-549`）是**纯 Sail 表达式，没有任何 `$ifdef SYMBOLIC` / `__isla_use_extra_ops` 分支**（vext_control.sail 的两处条件编译块分别止于 :409 覆盖 `read_vreg`、:535 覆盖 `write_vreg`；`read_vmask` 在 :535 之后，不在任何条件编译块内）：

```sail
function read_vmask(num_elem, vm, vrid) = {
  assert_vector_num_elem(num_elem);
  if vm == 0b1 then ones() else ones('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]
}
function read_vmask_carry(num_elem, vm, vrid) = {
  assert_vector_num_elem(num_elem);
  if vm == 0b1 then zeros() else zeros('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]
}
```

- `V(vrid)[num_elem - 1 .. 0]`：`low=0`（具体 `I128`），`high=num_elem-1`（符号）。在 isla `subrange_internal`（`isla-lib/src/primop.rs:1183-1241`）中，`(_, Val::Symbolic(_), _)` 分支（:1234-1236）命中 → 返回 `ExecError::SymbolicLength("subrange_internal")`。注意这不是"high/low 全符号"的证明分支（:1209-1233 才会尝试证明 `width=high-low+1`），**单边符号直接报错**。
- `ones('n - num_elem)` / `zeros('n - num_elem)`：长度表达式 `'n - num_elem` 也是符号的，同样无法构造符号长度的 bitvector。
- `num_elem` 符号化来源：`get_num_elem = (2^max(0,LMUL_pow))*vlen/SEW`（`vext_control.sail:289-294`），依赖符号化的 vtype。
- **设计遗漏**：`read_vreg`/`write_vreg`/`init_masked_result` 全部已加 SYMBOLIC + extra-ops 分支并接 isla extern（`isla_read_vreg`/`isla_pack_vreg`/`isla_init_mask`/`isla_vector_select`），唯独 `read_vmask`/`read_vmask_carry`/`write_vmask` 被漏掉。isla 侧 primops 注册表（`primop.rs:6019-6027`）无 `isla_read_vmask`。

### 与已证伪/纠偏断言的边界

- 断言"isla 侧注册表无 `isla_read_vmask` 是缺陷"——字面 true，但**隐含语义误导**：`read_vmask` 在 sail 是普通 `function`（编译为内联 `zread_vmask`，IR 中 inline 展开 124 次），不是已声明的 `pure "isla_..."` 外部 primop。不存在"名为 `isla_read_vmask` 的 primop 需要注册"，缺失本身不是已存在的 bug，而是**需要新增**的功能。
- 断言"`isla_init_mask` 用 `num_elem` 作 SMT active 条件"——**措辞不精确**：实际进入 SMT active 条件（`primop.rs:3576-3585`）的是 `args[3]=real_num_elem`，而非 `args[0]=num_elem`；`num_elem` 仅出现在具体校验块（:3536-3540），符号输入时被静默跳过。核心论点（位宽由 `length_bits(vm_val)` 固定为 `'n`、`num_elem` 不决定位宽）成立。
- 修复范式：最贴近的是 `isla_read_vreg_internal`（`primop.rs:3372-3423`，用 `expect_usize_or_symbolic_bound` 把符号 num_elem 具体化后逐元素构造，从不触发 `subrange_internal`）；`isla_init_mask` 是 mask bit 构造的辅助范式。

### 建议（结合 guides.md）

- **方向(a) 给 `read_vmask`/`read_vmask_carry` 加 SYMBOLIC + extra-ops 分支**（推荐）：与 `read_vreg` 完全对称，新增 `isla_read_vmask` extern。Rust 侧镜像 `isla_init_mask`/`isla_read_vreg` 范式：固定位宽 `len = length_bits(vreg_bits)`（= `'n`），`num_elem` 只作 SMT `Ite(i < num_elem, ...)` active 条件，永不作 subrange 的 high/low 或位向量构造长度。**不违反 guides.md**（只改执行策略，不固定运行态）。**根治**。
- **方向(b) 固定 vtype**：见问题 A，字面违反 guides.md，治标不治本（即便加 SEW/LMUL 枚举约束，num_elem 仍可能多值，`proven_symbolic_i128` 仍可能证不出唯一常量）。

sail 改动草图（read_vmask，与 read_vreg 对称；read_vmask_carry 同构，`is_carry` 语义不同）：

```sail
$ifndef SYMBOLIC
val read_vmask : forall 'n, 0 < 'n <= vlen . (int('n), bits(1), vregidx) -> bits('n)
function read_vmask(num_elem, vm, vrid) = {
  assert_vector_num_elem(num_elem);
  if vm == 0b1 then ones() else ones('n - num_elem) @ V(vrid)[num_elem - 1 .. 0]
}
$else
val isla_read_vmask = pure "isla_read_vmask" :
  forall 'n, 0 < 'n <= vlen . (int('n), bits(1), bits(1), vlenbits) -> bits('n)

val read_vmask_extra : forall 'n, 0 < 'n <= vlen . (int('n), bits(1), vregidx) -> bits('n)
function read_vmask_extra(num_elem, vm, vrid) = {
  assert_vector_num_elem(num_elem);
  isla_read_vmask(num_elem, vm, 0b0, V(vrid))   // is_carry=0: 高位填 ones
}

val read_vmask : forall 'n, 0 < 'n <= vlen . (int('n), bits(1), vregidx) -> bits('n)
function read_vmask(num_elem, vm, vrid) =
  if __isla_use_extra_ops then read_vmask_extra(num_elem, vm, vrid)
  else read_vmask_default(num_elem, vm, vrid)
$endif
```

isla 侧 `isla_read_vmask` 草图（参数 `num_elem, vm, is_carry, vreg_bits`）：固定位宽 `len = length_bits(&vreg_bits)`（= `'n`）；对每个位 `i ∈ [0..len)`，输出位 = `vm==1`（短路，read_vmask→1 / carry→0），否则 `i < num_elem ? vreg[i] : fill`（`fill = is_carry ? 0 : 1`）。`num_elem` 用 `int_exp_128` 转 SMT（允许符号），逐位构造 `Ite` 并 concat，完全镜像 `isla_init_mask_internal`（`primop.rs:3569-3593`）。

- **配套**：`write_vmask`（`vext_control.sail:552-562`，`[V(vrid) with (num_elem-1)..0 = v]` 同为符号 subrange 写）若日志出现其 SymbolicLength，按相同模式加 `isla_write_vmask`；当前先聚焦 :541/:548。

---

## 4. 问题 C：AES64ESM / AES64DSM MixColumns 符号表达式爆炸（非 V 扩展，历史遗留）

### 现象（日志证据，已验证）

- `output/log/AES64ESM.log`：仅 **8 次 FORK**、**0 次 PATH_RESULT**、**3 次 `Timeout(Timeout)`**，三次调用栈逐字一致：
  ```
  zexecute → zaes_mixcolumn_fwd → zxt3 → zxt2 → zbit_to_bool → zbool_bit_backwards
  ```
  `fun_args` 三个 `regidx`（rs1/rs2/rd）全符号化。
- `output/log/AES64DSM.log`：8 次 FORK、3 次 Timeout，调用栈 `zexecute → zaes_mixcolumn_inv → zgfmul → zxt2 → zbit_to_bool → zbool_bit_backwards`。
- **反证**：不带 MixColumns 的 `AES64ES`/`AES64DS`（只做 sbox+shiftrows，`zkn_insts.sail:367/384`）在 `status.intime.log` 中标记 intime，`timeout.log` 无 `AES64ES`/`AES64DS` 命中——佐证 MixColumns 的 `gfmul`/`xt2` 是瓶颈而非 sbox。

### 根因（已验证为 true，含两处措辞纠偏）

- `sail-riscv/model/extensions/K/types_kext.sail:20-22`：`xt2(x) = (x<<1) ^ (if bit_to_bool(x[7]) then 0x1b else 0x00)`；`gfmul`（:27-32）内 `xt2` 嵌套最多 3 层（`xt2(xt2(xt2(x)))`）。对符号字节，嵌套的 `bit_to_bool(x[7])` 在符号位上做条件 → 路径分叉。
- **纠偏 1**：调查报告称"拖死 SMT solver"。实际 `Timeout` 在**符号执行阶段**触发（`executor.rs:1112`），真正的放大器是嵌套 `xt2` 中 `bit_to_bool(x[7])` 在符号输入上的**路径分叉**，而非 SMT solver 求解本身。根因结论不变。
- **纠偏 2**（细微反驳）：纯 MixColumns 的 `AES64IM`（无 sbox，两次 `aes_mixcolumn_inv`）却 intime 完成——故"单独 MixColumns 即瓶颈"略过强。真正瓶颈是 sbox（256 项查表符号化扇出）与 MixColumns 的**复合**；ESM 栈崩在 mixcolumn 是因为 mixcolumn 在 sbox 已放大扇出之后触发了最终爆炸。字面事实（ES/DS 不 timeout、ESM/DSM timeout）成立。

### 建议（结合 guides.md）

- **短期（值得本轮做）**：参照已落地的 `isla_rev8`/`isla_brev8` primop 模式，把 `xt2`/`gfmul`/`aes_mixcolumn_fwd`/`aes_mixcolumn_inv` 拆出 `_default` 实现，在 `$ifdef SYMBOLIC` 且 `__isla_use_extra_ops` 为真时调用原生 primop（如 `isla_aes_xt2`、`isla_aes_gfmul`，8-bit→8-bit / 32-bit→32-bit），用查表/直接位运算取代逐位 `bit_to_bool` 条件展开。属执行路径补强，不固定运行态，符合 guides.md。
- **长期**：把 AES MixColumns 整列提升为单个 primop，避免符号字节级展开。

---

## 5. 问题 D：CSRImm / CSRReg CSR 地址符号化（非 V 扩展，历史遗留）

### 现象（日志证据，已验证）

- `output/log/CSRImm.log`：FORK 104（行数，实为 52 个独立 FORK 事件）、PATH_RESULT 264，FORK 高度集中在 `core/sys_regs.sail:127`（`function clause is_CSR_accessible(0x301,_,_)` / `read_CSR`/`write_CSR` 的 mapping/function clause 分发，占 ~60%）。
- `output/log/CSRReg.log`：FORK 152、PATH_RESULT 428，同样集中 `sys_regs.sail:127`，额外在 `:160`（`have_nominal_privLevel` 的 `match priv`）出现 `taints:["mstatus","mstatus"]` 的 FORK。
- 两者 `fun_args` 把 `bv12`（CSR 地址 `csr:csreg`）+ `bv5`（rd/rs1/uimm）+ `enum csrop` 全符号化；早期 FORK 带 `taints:["cur_privilege"]`。
- `doCSR`（`sail-riscv/model/extensions/Zicsr/zicsr_insts.sail:43`）调用 `check_CSR(csr,cur_privilege,access_type)` / `read_CSR(csr)` / `write_CSR(csr,new_val)`，CSR 地址与 `cur_privilege` 均符号化。
- IR 层 `zread_CSR`/`zwrite_CSR`（`rv64d.ir:375780/377605`）含数十条 `jump @not(zz4X) goto N` 条件 FORK，对 70+ 个 CSR 地址常量逐一 `zeq_bits` 比较（来自 191 条 read/write_CSR clause）。

### 与已证伪断言的纠偏

- 断言"CSRReg.log `sys_regs.sail:386` 出现 `taints:['mstatus','mstatus']` 的 FORK"——**验证为 false**。实测 `CSRReg.log` 中 386 处唯一的 FORK 其 taints **为空 `[]`**（Symbol 335），且源码 :386 实为 `legalize_xenvcfg_cbie`（private 辅助函数），`legalize_menvcfg` 起始于 :394。带 `mstatus,mstatus` 的 FORK 共 9 次：3 次在 :160，6 次在无源映射的 1442/1449/1456 匿名位置，386 占 0 次。

### 建议（结合 guides.md）

- **短期**：在 isarch pre-state 对 CSR 指令的 `csr`（12-bit 地址）字段做**约束化而非完全符号化**——只枚举模型已实现 CSR 集合（misa/mstatus/menvcfg 等），把 2^12 分发空间砍到几十。对 `mstatus` 在 CSR 写路径考虑位域级约束（只符号化必要位）。属"加强过松约束"，符合 guides.md。
- **长期**：为 CSR read/write dispatch 提供"按地址短路"的原生 primop（符号地址→值的 lookup table），避免逐 clause FORK。

> DIV/DIVW 已不在本轮 timeout 列表（验证为 true，与 MEMORY 一致——它们在 `MEMORY` 组被 `run.mk` 排除）。

---

## 6. 已验证结论与不确定结论的边界

**已验证为 true（高置信，可直接据此行动）**：
- 问题 A 全链：vtype 不在 `reg_list`/`setup_pre_state`、TOML 缺 vtype、`init.rs` Uninit 机制、`assert_sew`(4路)/`assert_lmul_pow`(7路) match fork、`vtype=0x10` 解码、SEW/LMUL 笛卡尔积=28、VITYPE.log 符号位宽错误、历史 216/220 对照、guides.md 原则表述。
- 问题 B 全链：`read_vmask` 无 extra-ops 分支、`subrange_internal` 的 SymbolicLength 分支路径、`isla_init_mask` 固定位宽机制、num_elem 符号来源。
- 问题 C：ESM/DSM 调用栈与 FORK 计数、ES/DS 不 timeout 的反证、`xt2`/`gfmul` 嵌套结构。
- 问题 D：CSR 地址符号化导致 dispatch 爆炸、`zicsr doCSR` 调用链。
- isla 架构：`reg_list` 内容、`setup_pre_state` 无条件覆盖、TOML 加载链、`set_complete_model` 注释是用户明确选择（勿擅改）。

**已验证为 false（已纠正）**：
- 符号 `num_elem` 驱动 foreach 边界符号化导致 timeout（foreach 实际定数展开）。
- `f18f3d4` vr 符号化是 V 扩展爆炸主因（真正主因是 vtype）。
- 本轮 log 是 stale run 产物（实际更新且含 vr）。
- CSRReg `:386` 出现 mstatus taint（实际 taint 为空、函数归属错误）。

**uncertain（需实验验证）**：
- 建议的 `isla_read_vmask` 草图能否编译通过并消除全部 39 个 clause 的 subrange 错误（属实现验证层面）。
- CSR 写路径 mstatus 位域符号化的具体收敛方案（需 isarch 层实验）。
- 方案 A 单值 `vtype=0x10` 与 guides.md:5 的字面张力，严格读法下应优先方案 B（合法域约束）。

---

## 7. 修复优先级建议

1. **最高优先 — 问题 A**：恢复 TOML `vtype` 约束（短期单值 `0x10` 恢复 216/220 基线 → 长期合法域约束 / 多 profile）。预计单独消除 ~59 个 V 扩展/vector timeout 中的绝大多数。**纯配置回归，改动最小、收益最大。**
2. **高优先 — 问题 B**：新增 `isla_read_vmask` extern 补齐 `read_vmask`/`read_vmask_carry` 的 extra-ops 分支。问题 A 修好后 subrange 错误可缓解（num_elem 具体），但根治需此改动，且保留符号覆盖率。
3. **中优先 — 问题 C**：拆 AES `xt2`/`gfmul`/`mixcolumn` 为原生 primop（可复用 rev8 primop 范式，单点修复；FORK 极小说明非路径问题而是 solver 表达式问题）。
4. **中优先 — 问题 D**：CSR 地址约束到已实现集合 + mstatus 位域约束。

**关键不动项**（用户明确选择，勿擅改）：`src/isarch/exec.rs:357 set_complete_model(true)` 保持注释（MEMORY 记载"只输出 solver 真正约束的 pre-state 寄存器"）。

---

## 附录 A：63 个 timeout clause 全表

V 扩展 / vector crypto（59 个，vtype 驱动，问题 A）：

```
MASKTYPEI MASKTYPEV MASKTYPEX MMTYPE MOVETYPEI MOVETYPEV MOVETYPEX
MVVMATYPE MVVTYPE MVXMATYPE NITYPE NVSTYPE NVTYPE NXSTYPE
RIVVTYPE RMVVTYPE VAESDF VAESDM VAESEF VAESEM VAESKF1_VI VAESKF2_VI VAESZ_VS
VANDN_VV VANDN_VX VBREV8_V VBREV_V VCLMULH_VV VCLMULH_VX VCLMUL_VV VCLMUL_VX
VCLZ_V VCPOP_V VCTZ_V VEXTTYPE VGHSH_VV VGMUL_VV VICMPTYPE VID_V
VIMCTYPE VIMSTYPE VIMTYPE VITYPE VMSBF_M VMSIF_M VMSOF_M VMVRTYPE
VREV8_V VROL_VV VROL_VX VROR_VI VROR_VV VROR_VX VSHA2MS_VV VSM3C_VI VSM3ME_VV VSM4K_VI
VXTYPE ZVKSHA2TYPE
```

非 V 扩展（4 个，历史遗留，问题 C/D）：

```
AES64ESM AES64DSM   （问题 C：MixColumns 符号表达式爆炸）
CSRImm   CSRReg     （问题 D：CSR 地址符号化 dispatch 爆炸）
```

## 附录 B：复现命令与统计口径

```sh
cd isla
rm -rf output/ && make solve -j32
# 统计
wc -l output/status.intime.log output/status.timeout.log
grep -rhoE '执行错误: [^[]+' output/log/*.log | sed -E 's/line1: [0-9]+, char1: [0-9]+, line2: [0-9]+, char2: [0-9]+//' | sort | uniq -c | sort -rn
```

- 非 timeout 硬错误口径：`grep '执行错误' output/log/*.log` 排除 `Timeout(Timeout)`/`执行错误: Timeout$`。
- timeout 口径：`status.timeout.log`（每个 clause 60s 超时上限，见 `scripts/run.mk:98`）。
