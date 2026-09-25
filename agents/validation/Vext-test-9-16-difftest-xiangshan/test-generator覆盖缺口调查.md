# Test Generator 覆盖缺口调查：为什么没触发 XiangShan 已知 bug

## 问题

两个假设：① isla 求解结果的覆盖面不全，导致无法生成对应 PoC；② isla 求出的东西本可能触发 bug，但 test generator（PoC 生成/重放）做得不好没触发到。本报告用 `make-solve-json/`（101 个 clause 原始 JSON）、`isla-solve-success-all.json`、`pipeline.py`、`configs/riscv64_difftest.toml`、`scripts/run.mk` 的实际数据逐项核验。

## 结论（先答）

**两个假设都成立，但各覆盖不同的 bug 类别；此外还有第三种归因（求解粒度），三者合计解释了绝大多数未覆盖面。**

| 归因 | 规模 | 对应 bug 类 |
|---|---|---|
| A. 求解侧结构性排除/钉死（覆盖面不全） | 最大 | 访存/浮点/未对齐/VS 初值/页表类，约 30 条 issue |
| B. 生成侧丢弃可用材料（PoC 不好） | 次之 | **非法编码类约 10 条 issue——材料已经求出来了，被整批扔掉** |
| C. 求解粒度（单指令） | — | 指令邻近性/异常链/微架构压力，约 10 条 |
| D. 求解 witness 不差异化（覆盖到了但没打中） | 精确 4 条 | #5829/#5830/#5840/#5928——最接近"本可能触发"的一类 |

## 链路与数据基线

```
make solve (101 clause, ACTIVE_ALL)
  → 101 JSON，共 19,908 条状态：
      Retire_Success 10,799 (54.2%)
      Illegal_Instruction 9,045 (45.4%)   ← 被 DiffTest 管线整批丢弃
      Memory_Exception 64 (0.3%)          ← 同上丢弃
  → isla-solve-success-all.json（只含 Retire_Success）
  → pipeline.py make_assembly → program.S → ELF → XiangShan DiffTest
```

## A. 求解侧结构性排除/钉死（假设 ① 主体）

### A1. 访存类 clause 被默认 solve 排除

`scripts/run.mk:70`：

```
# 内存符号化支持尚不完整，默认 solve 先跳过实际访存、缓存块、fence/TLB 类 clause。
MEMORY=... VLRETYPE VLSEGFFTYPE VLSEGTYPE VLSSEGTYPE VLXSEGTYPE VMTYPE VSRETYPE VSSEGTYPE VSSSEGTYPE VSXSEGTYPE ...
ACTIVE_ALL=$(filter-out $(FD_FLOAT) $(MEMORY),$(ALL))
```

实测成功集合里真正的向量访存指令只有 **vsm.v 6 条 + vlm.v 1 条**（来自 MASKTYPE 类 clause 的 encdec 附带），vle/vse/vlse/vsse/vlux/vsox/segment/FOF/whole-register-load **全部为 0**。

→ 无法覆盖：#5766/#5767（FOF）、#5930~#5934（segment/indexed/strided load 数据）、#6015/#6022（indexed load 挂死）、#6467（store 队列）、#6482/#6576（load fault 链）、#5765（vlm tail，仅 1 条且 `vlm.v v0,(x0)` 无内存数据）。

### A2. 浮点向量 clause 被排除

`FD_FLOAT` 列表 filter-out（VFMV/VFMERGE/VFMVFS/RFVVTYPE/FVFTYPE…）。

→ 无法覆盖：#5830（vfmv.f.s NaN-box，成功集合仅 3 条附带产物且无 vr）、#5768（frm 保留值，isa-state 根本没有 frm 字段）。

### A3. config 把关键 CSR/行为钉死

`configs/riscv64_difftest.toml` 的 `[registers.defaults]`：

| 钉死项 | 值 | 后果 | 对应 bug |
|---|---|---|---|
| `mstatus` | `0x600`（VS=Dirty） | 求解永远给不出 VS=Clean 初值路径 | #6561 需要 VS=Clean + vl=0 |
| `__isla_always_aligned` | `true` | 访存恒对齐，未对齐面消失 | #5931/#5933/#5934 的 base 未对齐触发条件 |
| `satp` | `0`（bare） | 无页表翻译 | #6540（S-mode 页 fault/stval） |
| `[symbolic_addrs]` | 0x80310000..0x80410000, stride 0x10 | 地址只能在固定窗口取值 | PMP deny 区/未映射物理地址（#6015/#6576）、I/O PMA（#6293） |

### A4. 无 S 模式

成功集合 cur_privilege：User 10,795 + Machine 4，**无 Supervisor**。（#6540 需要 S 模式。）

### A5. 单指令求解粒度

每条状态只有一条 test-ins，且模版单指令 + GOODTRAP 收尾。指令邻近性（#5739 `vsetvli→csrr vl`、#5766 `FOF→csrr vl`）、异常链（#6399/#6482/#6540 需要第二条 fault 指令 + handler）、微架构压力（#6467/#6015 长序列）在粒度上不可表达。这属于 isarch 执行模型的天然边界，不是参数问题。

## B. 生成侧丢弃了已求解出的材料（假设 ② 主体）

### B1. 9,045 条 Illegal_Instruction 状态被整批丢弃

`isla-solve-success-all.json` 只收 `Retire_Success(())`。"ISA 模型认为非法"的用例恰恰是非法编码类 bug 的打击面——RTL 若不 trap 即 bug。这些用例 **isla 已经造出来了**（非法路径还有 case_quota 输出配额和字段多样化支持），只是组装批量输入时被过滤，从未进过 DiffTest。

→ 直接对应：#5772（vmv4r misaligned）、#5809（VILL 后不 trap）、#5865（vd=v0 masked vmerge）、#5919、#6302（reserved vsew）、#6407、#6410、#6298（vstart 越界）。

佐证：成功集合里的 vtype 分布含 `0x8000000000000000`（VILL，24 条）和 `0x40~0xd8` 一批保留编码（约 200 条）——这些是"配置成非法状态后仍合法退休的指令"（如 vsetvl 自身）；而"非法状态 + 会检查 vtype 的指令"组合全部落在被丢弃的 9,045 条里。

### B2. mstatus 不重放（小头）

`make_assembly` 固定 `csrs mstatus, 0x600`；成功集合有 9 条带 mstatus 值（0x0800/0x1800 等非默认值，来自 mret/vsm.v 路径），被忽略。影响面小（#6561 主要卡在 A3）。

## C. witness 不差异化：覆盖到了但没打中（假设 ② 的深层形态）

isla 的求解目标是**路径可达性**：让一条 clause 产生 `Retire_Success` 的任意 witness。对"不改变路径的数据维度"，Z3 给默认模型值，不产生差异化样本。三个实测证据：

### C1. VR 哨兵不差异化

- `[registers.defaults]` 里 `__isla_vector_vpr = true`（vr 符号化开着），reg_list 含全部 vr0..vr31；
- 2,194 条带 vr 的成功状态**值全部相同**：抽样 3 条（vcompress/vmseq 类）每个 vrN 都是 `128'h...0001`——Z3 默认值，无符号位、无 per-lane 魔数；
- 关键：**bug 指令的成功状态 vr 字段数全为 0**（vmv.x.s 8 条、vzext 4 条、vsext 4 条、vfmv.f.s 3 条、vlm.v 1 条、vmv4r 4 条均无 vr）。原因：这些指令读 vr 的任意切片都不改变路径 → 符号值未被约束 → 模型 Arbitrary → collector 不写入 isa-state。

#5829（vmv.x.s 符号扩展）的精确打不中机制：成功集合有 8 条 vmv.x.s，其中 SEW=8/16/32<XLEN 的配置都在（vtype=0x1/0x9/0x11 大量存在）——**指令有了、SEW 配置有了，唯独源元素符号位=1 没有**（vr 全 0/缺省 → sign-extend ≡ zero-extend，DiffTest 无分歧）。#5830（NaN-box）、#5840/#5928（元素选择）同理。

### C2. 编码字段不差异化

成功集合里 vmv4r.v 全部是 `v0, v0`、vmv.s.x 的 vd 全部 v0、vmv.x.s 的 vs2 全部 v0——未约束的寄存器号字段 Z3 给同一默认值。现有 `diversify_unconstrained_finite_domains`（exec.rs）**只对 Illegal_Instruction 路径**做字段多样化，成功路径没有做。

### C3. 覆盖 ≠ 触发的正面佐证

- vstart≠0：1,197 条被求解且被 pipeline 重放（80 条 vmerge/vmv DiffTest 失败正是这批）——CSR 维度的"求解→重放→观察"通路是通的；
- vl=0：360 条已重放，但 vl=0 状态的指令 top 是 vmerge/vsetvl/vmv.v.x/vcompress/vred，**没有向量 load/store**（被 A1 排除），叠加模版 VS 恒 Dirty（B2/A3）——#6561 的组合面两侧各缺一角，哪边补上都不够，两边都要补。

## 归因汇总表（对 89 条 issue 的已确认 bug 面）

| bug 类 | 代表 issue | 归因 |
|---|---|---|
| 非法编码不 trap | #5772/#5809/#5865/#5919/#6302/#6407/#6410 | **B1**（材料已求出，被丢弃） |
| vstart 越界 | #6298 | B1 |
| 标量扩展/NaN-box/元素选择 | #5829/#5830/#5840/#5928 | **C1/C2**（状态在，witness 无数据差异化） |
| FOF/segment/indexed load | #5766/#5767/#5930~#5934 | A1+A5 |
| 访存异常地址/挂死 | #6015/#6022/#6262/#6576/#6543 | A1+A3（PMP/页表）+A5 |
| 异常链 mtval/stval | #6399/#6482/#6540 | A5（单指令粒度）+A4（无 S 模式） |
| VS Dirty 语义 | #6561 | A3（mstatus 钉死）+A1（vl=0 无访存指令） |
| frm 保留 | #5768 | A2+A3（frm 不在求解面） |
| 指令邻近性 | #5739/#5766(观察点) | A5 |
| 微架构压力 | #6467/#6015 | A5（原理上超出指令级） |
| mask tail | #5765 | A1（vlm 仅 1 条）+C1（无 v0 哨兵语义）+无读回观察点 |

## 行动建议（按代价从低到高）

1. **把 9,045 条非法用例纳入 DiffTest**（纯生成侧改动）：oracle = 两侧都 trap 且 mcause/mtval 一致；模板只需加 trap handler 记录 mcause/mtval。预期直接补上 B 类全部打击面。
2. **成功路径 witness 多样化**（求解侧小改）：把 `diversify_unconstrained_finite_domains` 扩展到 Retire_Success 路径的未约束字段（vr 切片、寄存器号），或对源操作数加定向约束（符号位=1、每 lane 唯一魔数）。预期命中 #5829/#5830/#5840/#5928 一类。
3. **解除 config 钉死**：`__isla_always_aligned` 关闭、mstatus 符号化（保留 VS 合法域约束）、satp/页表与 PMP deny 区建模——依赖内存符号化完善，代价最高，对应 run.mk 里 MEMORY 类 clause 恢复。
4. **指令对/短序列求解**（A5）：目标指令后追加观察指令（csrr vl / 读回比较）作为 oracle，工作量在 exec 管线。

## 对比个案：zhangkanqi 批次（5 条）

zhangkanqi 的 issue 全部来自 fuzzer 生成器（模版 4：随机指令流 + 通用跳过 handler + DiffTest 全状态比较当 oracle）。他的五条恰好横跨本报告的全部归因类别，且其 Commit Trace 直接暴露了 fuzzer 管线的两个关键机制，逐条对照如下。

### 逐条触发条件与归因

| Issue | 触发指令 | 触发要素 | 确认状态 | 我们的缺口归因 |
|---|---|---|---|---|
| #5772 | `vmv4r.v v12, v22` | **vs2=v22 未按 NF=4 对齐**的编码，应 illegal 未 illegal | confirmed | **B1**（misaligned 编码在 sail 走 Illegal 路径 → 落在被丢弃的 9,045 条里）+ C2（成功路径寄存器号不分化，我们的 4 条 vmv4r 全是 `v0,v0`） |
| #5769 | `vsuxseg4ei8.v v20, (a0), v16` | base=0xffffffffffffffff + **索引 v16[0]=0xb2 参与故障地址**，mtval 应=base+idx | reported | **A1**（VSXSEGTYPE 被排除）+ A3（地址域钉死 0x80310000 窗口）+ A5（mtval 观察） |
| #5770 | `vl2re32.v v18, (s4)` | base=0x7 首元素 fault；**v18 需有魔数初值** 0x4f1f…_6248…（断言"部分覆盖"必须旧值可辨识）+ vstart 断言 | reported | **A1**（VLRETYPE 被排除）+ A3 + **C1**（VR 魔数哨兵）+ 读回观察点缺失 |
| #5790 | `vssseg3e16.v v10, (a3), t0, v0.t` | **合法 base + 巨大 stride**（0x2652aaaaaaaaaaa9）溢出到 0x4ca5… 触发 PMA fault，mcause 方向错 | not_confirmed（作者自疑 NEMU bug） | A1 + A3（溢出地址在窗口外）+ C（stride 恶意值）|
| #5777 | `sc.w` → `vsuxei32` | indexed store 应 store access fault，XS 15000 周期无提交（疑似挂死） | not_confirmed | A1 + A5（活性 oracle）+ AMO 也在 MEMORY 排除表 |

### 他的管线里两个被我们缺位的机制（从 Commit Trace 直接可见）

1. **通用跳过 handler 让非法指令"跑完程序"**：#5790/#5777 的 trace 里都出现 `vsm4k.vi` 触发 cause=2 illegal → `csrr mepc / addi a3,4 / csrw mepc / mret` 跳过继续执行。fuzzer 的随机流必然产生非法编码，handler 把它们变成"跳过继续"，程序不终止；当遇到"该 illegal 而 XS 未 illegal"时（#5772），两侧 pc 立即分叉，DiffTest 报分歧。**这正是 B1 缺口的镜像解法**：我们的 9,045 条非法用例若进 DiffTest，同样需要这种"trap 也要被比较"的 oracle 设计（两侧 trap 行为/mcause/mtval 一致性），而非异常即终止。
2. **DiffTest 全架构状态逐条 commit 比较**：mcause/mtval/vstart/VR 任一字段分歧都自动报出（#5769 的 mtval、#5770 的 vstart+v18_low 都是 difftest 内建比较发现的，不需要程序自己断言）——oracle 零成本；代价是**确认率低**（5 条里 1 confirmed、2 reported、2 not_confirmed，#5790 连作者自己都怀疑是 NEMU bug）。

### 与我们管线的互补关系

- 他命中的面 = **A1（访存指令随机出现）× A3（地址随机必然出非法地址）× C1/C2（操作数/编码全随机）× handler（非法可续行）**——四个面恰好全是本报告 A/B/C 缺口的并集；
- 我们的管线在同样五条上：#5772 只差 B1（材料已在手）+C2；#5769/#5770/#5790/#5777 第一道墙都是 A1（访存 clause 未求解），即使解除 A1 还要依次过 A3（地址域）和 C1（#5770 的 VR 魔数初值）；
- 反向对比：我们的 vstart≠0 80 条失败全部是**精确的语义分歧**（可直接定性），而 fuzzer 的分歧需要人工判读（2/5 存疑）——符号求解的 witness 带路径语义，随机采样不带；两者是互补而非替代：fuzzer 适合"unknown-unknown 的广度"，符号求解适合"已知触发面的深度复刻"。

## 附：数据快照（2026-09-18 统计）

- vtype：56 种取值（0x0~0x1b 合法 22 种 ×约 1.05 万条、VILL 24 条、保留编码 0x40~0xd8 约 200 条）
- vl：60+ 种（含 0 共 360 条、1/3/2/0xf/0x7/0x1f 为大头）
- vstart：0 共 9,488 条、1 共 1,197 条、2/4/8/0xc/0x10/0x18 等小量、越界值 6 条
- cur_privilege：User 10,795 / Machine 4 / S 0
- vcsr：0（10,613）/ 2（103）/ 4（31）/ 6（52）
- 带 x1..x31：467 条；带 f0..f31：82 条；带 vr：2,194 条（值同质）；带 mstatus：9 条
- 指令种类：242 种成功退休；真实向量访存 vsm.v 6 + vlm.v 1
