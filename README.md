# Isla

![Ubuntu-20.04](https://github.com/rems-project/isla/actions/workflows/ubuntu_22_04.yml/badge.svg)

Isla is a symbolic execution engine for
[Sail](https://github.com/rems-project/sail), 
and a tool (sometimes known more specifically as `isla-axiomatic`) 
that uses that to evaluate the relaxed-memory behavior of instruction
set architectures (ISAs) specified in Sail, including Armv8-A and RISC-V, with respect to arbitrary axiomatic memory models
specified in a subset of the cat language used by the
[herd7](http://diy.inria.fr/doc/herd.html) tools. For example, for a classic message-passing test on Armv8-A, Isla finds the following candidate execution satisfying the final condition of the test, with the instruction behaviour taken from symbolic evaluation of the full Armv8-A ISA definition.


![Message passing example](doc/MP.png?raw=true)

There is an online web interface for `isla-axiomatic` here:

[https://isla-axiomatic.cl.cam.ac.uk](https://isla-axiomatic.cl.cam.ac.uk)

Isla has also been used for test generation, generating simplified
semantics (summaries) for concrete opcodes, and there are many other
possible use cases.

## Build

Get Rust and its dependencies, probably the easiest is with [rustup](https://rustup.rs/).

Then build isla and friends, currently tested with (stable) Rust 1.70:
```
cargo build --release
```

### Z3

By default we require that [z3](https://github.com/Z3Prover/z3)
is available as a shared library.

If running isla-axiomatic, `z3` must also be available on the `PATH`.

It should be available in the usual places, currently tested with Z3 4.12.6:
```
apt install libz3-dev  # on Ubuntu 20.04 LTS and later
opam install z3 # alterantively, opam usually has an up-to-date version
```

However the version of z3 that is available in older Ubuntu LTS versions
(and likely other linux distros) is quite old,
so you may experience link errors in that case.
The build.rs script is configured so it can use a `libz3.so` shared library
placed in the root directory of this repository.
If this is done then `LD_LIBRARY_PATH` must also be set when
executing so that the more recent z3 library is used.
In those cases a version of z3 can be obtained from the sources
[https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

## Model snapshots

Isla executes IR produced by Sail. To avoid having to generate this IR,
there are pre-compiled snapshots of our ISA models available in the
following repository:

[https://github.com/rems-project/isla-snapshots](https://github.com/rems-project/isla-snapshots)

To generate this IR in the correct format a tool is available in the
isla-sail directory. Building this requires various arcane OCaml
incantations, but mostly one can follow the Sail install guide
[here](https://github.com/rems-project/sail/blob/sail2/INSTALL.md),
followed by the instructions [here](isla-sail/README.md). It will only
work with the latest HEAD of the `sail2`branch in the Sail repository.

## Litmus test format conversion

For litmus tests in the `.litmus` format used by
[herd7](https://github.com/herd/herdtools7) and [rmem](http://www.cl.cam.ac.uk/users/pes20/rmem) there is another OCaml
tool based on parsing code from herd7 in the isla-litmus
directory, which translates that format into a simple
[TOML](https://github.com/toml-lang/toml) representation. This OCaml
program is standalone and does not depend on any libraries, and should
build with dune >= 1.2.


## Example

After compiling Isla, to compute the footprint of an add instruction
using the ARM 9.4 snapshot above, the following command can be used:

```
target/release/isla-footprint -A armv9p4.ir -C configs/armv9p4.toml -i "add x0, x1, #3" -s
```

The arguments are the compiled Sail model, a configuration file
controlling the initial state and other options, and the instruction
we want to run. The `-s` flag performs some basic dead-code
elimination to simplify the generated footprint. We get a trace
of the instruction as a mix of SMTLIB definitions of the semantics,
interspersed with statements describing the input and outputs of the
instruction, here `read-reg` and `write-reg`.

```
  (declare-const v3371 (_ BitVec 64))
  (read-reg |R1| nil v3371)
  (define-const v3457 (bvadd ((_ extract 63 0) ((_ zero_extend 64) v3371)) #x0000000000000003))
  (write-reg |R0| nil v3457))
```

## Example: Running isla-axiomatic

To run a relaxed litmus test,
first ensure an up-to-date snapshot is obtained from [isla-snapshots](https://github.com/rems-project/isla-snapshots)

A quick and simple test is just to run the Arm `MP+dmb.sy+ctrl` litmus test,
against the same model the web interface uses:

```
target/release/isla-axiomatic -A /path/to/isla-snapshots/armv8p5.ir -C configs/armv8p5.toml -m web/client/dist/aarch64.cat web/client/dist/aarch64/MP+dmb.sy+ctrl.toml
```

For more information, see the full [documentation](https://github.com/rems-project/isla/blob/master/doc/axiomatic.adoc).

## Manual

There is a guide to the various Isla command line options and features
[here](https://github.com/rems-project/isla/blob/master/doc/manual.adoc).

The `isla-axiomatic` tool has a seperate manual
[here](https://github.com/rems-project/isla/blob/master/doc/axiomatic.adoc),
and a guide to its support for virtual memory and address translation
[here](https://github.com/rems-project/isla/blob/master/doc/translation.adoc).

## solve-state 内存符号化模型（isarch）

`solve-state` 对符号内存的建模由环境变量 `ISLA_RISCV_MEMORY_MODEL` 控制：

* `array`（默认）：用 SMT 字节数组 `(Array (_ BitVec 64) (_ BitVec 8))` 建模
  内存（`src/isarch/memory_model.rs`）。同一条执行路径内同地址读写保持一致：
  读值逐字节等于数组内容（小端），符号写把数组逐字节 `Store` 后重定义为新
  常量；符号读写地址全域自由（见下方"语义分层"）。
* `fresh`：退回 `isla-lib` `Memory` 的默认行为，每次符号读新建独立的位向量
  变量，同地址读写之间没有一致性关系。

### 语义分层：内存层只管内容，可访问性交给模型 PMA/PMP

默认（W9 语义）**全符号化**：符号读写地址全域自由，读值/写效来自字节数组，
内存层不做任何可访问性判断。

* **Isla 内存层只管内容**：符号读写地址全域自由，读值/写效来自字节数组，
  内存层不做任何可访问性判断；
* **可访问性/trap 完全交给模型自身的 PMA/PMP**（PMA 地图：默认沿用 IR 固化
  的 `pma_regions`——ROM [0x1000,0x2000) 只读、MMIO [0x02000000,0x04000000)、
  RAM [0x80000000,0x100000000)；W10 起可经 `[[pma_regions]]` 配置替换，见
  下文专节）：可访问 → 正常访存（成功路径，带访存事件）；
  不可访问 → 访存 trap / access fault（`ret_val` 为异常类）。**fault 路径是
  合法且有价值的测试输出，不会被内存层抹掉**——两类路径在结果 JSON 中并存。

`[[memory_regions]]` 支持三种区域类型，语义各司其职：

| `region_type` | 语义 | 作用 |
| --- | --- | --- |
| `concrete` | 固定内容快照 | 具体地址命中时初值/读值来自快照，内容不进数组；沿用 `Memory` 的 `Concrete` 种类约定，不承诺作为统一可写 RAM |
| `symbolic` | **纯声明**元数据 | 只表示"这一段明确是 RAM、内容未知"（由字节数组提供内容），**不产生任何地址或内容约束**（W9 起降级为纯声明；W8 曾配合开关圈地址，该机制已删除） |
| `excluded` | **判死区域** | 声明"这一段不关心，遇到了是 unsat"，详见下节 |

`MemoryBuilder` 拒绝重叠区域（含判死区域之间、判死与 concrete/symbolic、
以及与内置 CLINT 的重叠），手工构造的重叠 `Region` 未纳入保证。

> 历史限制（W10 前版本适用，已被 `[[pma_regions]]` 修订）：曾认为"模型的
> PMA 地图固化在 IR，声明 sym_ram = [0x80000000,0x90000000) 只是模型 RAM
> 的子集，落在 [0x90000000,0x100000000) 的访问按模型 PMA 不 trap，要精确
> 边界需重新生成 IR"。W10 起用 `[[pma_regions]]` 把 `zpma_regions` 寄存器
> 替换为配置地图即可消除该限制，无需改 IR（见下节）。

### 判死区域：`region_type = "excluded"`

配置声明某些区域"**不关心**"：任何访问（读或写，判死对两者一视同仁）与
判死区域重叠——哪怕只有一个字节——该执行路径即判死（Unsat），不产生访存
事件：

* **符号地址**：数组内存模型回调追加 `NOT(与判死区域并集重叠)` 约束
  （`smt_excluded_constraint`，`isla-lib/src/memory.rs`），并沿用 W7 的
  "回调追加约束后立即 `check_sat`"机制——地址解进判死区域（含被路径既有
  断言如模型 PMA 分支钉进去）时立即以 `BadRead`/`BadWrite` 判死、尽早剪枝；
* **具体地址**：`Memory` 的具体地址分派识别判死区域，直接返回
  `BadRead`/`BadWrite`，不经 solver。

零判死区域 = 零约束零开销，与默认全符号化完全一致；concrete/symbolic
区域行为不受判死配置影响。判死语义是"路径过滤器"而非可访问性判断：判死
只删掉**落到这片区域**的路径，区域之外的 PMA trap/access fault 路径照常
与成功路径并存输出。

示例（`configs/riscv64_difftest_mem_excluded.toml`，把模型 PMA 的 MMIO 段
[0x02000000,0x04000000) 判死）：

```toml
[[memory_regions]]
name = "mmio_hole"
base = "0x02000000"
size = "0x02000000"          # [0x02000000, 0x04000000)
region_type = "excluded"

# mmio_hole 包住默认 CLINT [0x02000000,0x020c0000)，区域不允许重叠，须关闭：
clint_enabled = false
```

### 配置化 PMA 地图：`[[pma_regions]]`（W10）

把模型 PMA 地图写入 IR 顶层寄存器 `zpma_regions`（`%list(%struct zPMA_Region)`，
模型的 `zpmaCheck`/`zmatching_pma` 逐项遍历）——启动时按配置构造
list-of-records 值注入 `default_registers`，模型逻辑与 IR **零改动**。
region 布局与 IR record 对齐：**base+size（非 base+end）**；配置列表按 base
降序注入（与 IR 固化列表次序一致）。与 `[[memory_regions]]` 的关系是**正交
两层**：

| 层 | 配置 | 管什么 |
| --- | --- | --- |
| 内容层 | `[[memory_regions]]`（concrete/symbolic/excluded） | "存什么、哪些不关心"：字节数组内容、判死过滤 |
| 属性层 | `[[pma_regions]]` | "哪里可访问、属性、trap 边界"：模型 PMA 逻辑自身执行 |

字段：`base`、`size`（必填，size>0 且 base+size 不溢出）；属性二选一——
`attr` 别名，或明细字段（可覆盖别名/基线的个别位）：

| 字段 | 取值 | 无 attr 时的基线 |
| --- | --- | --- |
| `attr` | `"ram"` / `"rom"` / `"mmio"` / `"hole"` | — |
| `readable`/`writable`/`executable`/`cacheable`/`coherent`/`read_idempotent`/`write_idempotent`/`supports_cbo_zero`/`include_in_device_tree` | bool | 全 false，唯 `include_in_device_tree=true` |
| `misaligned` | `"no_fault"` / `"access_fault"` / `"alignment_fault"` | `no_fault` |
| `reservability` | `"eventual"` / `"non_eventual"` / `"none"` | `none` |

注意 `supports_cbo_zero` 是单个 z（IR 里 `zsupports_cbo_zzero` 的双 z 是
Sail zencode）。别名映射（ram/mmio 镜像 IR 固化默认 region 属性）：

| attr | r/w/x | cacheable | idempotent(r/w) | cbo_zzero | misaligned | reservability | in_dev_tree |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ram` | T/T/T | T | T/T | T | no_fault | eventual | T |
| `rom` | T/F/F | T | T/T | F | no_fault | none | F |
| `mmio` | T/T/F | F | F/F | F | alignment_fault | none | F |
| `hole` | F/F/F | F | F/F | F | no_fault | none | F |

自校验（对齐 MemoryBuilder 硬失败风格，isarch 不经过模型 `zcheck_mem_layout`，
排序/重叠须在配置解析做）：size=0、base+size 溢出、任意两区域重叠（与 TOML
书写顺序无关）都会在配置加载时报错退出；既无 `attr` 也无任何明细字段同样
报错。**未配置 `[[pma_regions]]` 时不注入任何值**，`zpma_regions` 沿用 IR
固化默认（ROM/MMIO/RAM 三段），行为与 W9 及之前逐项一致。

示例（`configs/riscv64_difftest_mem_excluded_pma.toml`，RAM-only 地图，
W14 起对齐重放 emu 实际有效 RAM [0x80000000,0x80000000000) 8TB）：

```toml
[[pma_regions]]
name = "ram"
base = "0x80000000"
size = "0x7FF80000000"        # [0x80000000, 0x80000000000)，=2^43-2^31
attr = "ram"
```

> **W14 修订注记**：W10 初版示例 size=0x10000000（[0x80000000,0x90000000)），
> 依据是"重放环境 DRAM 256MB（emu 默认）"。W13 对账证伪：所借用 emu
> （isla-xiangshanv2 @f86f50b83）源码 SoC.scala:335 `memRange`、
> Parameters.scala:568 `SimMemSize=8190GB "same as PMA (0x80000000,
> 0x80000000000)"，探针实测 0x90000000..0x1000000000 放行、0x80000000000
> 顶界 fault——**"DRAM 256MB"结论对该 emu 不适用**（该宏属 difftest csrc
> 侧），地图 size 以 SimMemSize/实测为准。语义后果：旧地图把 @0x90000000
> 等（8TB 内、256MB 外）的合法写判成 fault，与 emu 退休行为错位。
>
> **W15 勘误**：W13/W14 写下的 size=0x7FFF80000000（12 位十六进制）多一个
> F，base+size=2^47，实际地图成了 [0x80000000,2^47)（128TB），并非声称的
> 8TB 顶界——8TB 顶界对应 11 位值 0x7FF80000000（=SimMemSize 8190GiB=
> 2^43−2^31）。W14 报的"高址非单调 fault/放行"异常（如 2^47 fault 而
> 2^43+ε 放行）全因于此（当时 top_exact 等探针钉的是 2^47，被误读为
> 2^43）；对 Sail `range_subset` 环绕语义逐条手算，W15 复测全部探针
> （含 2^43±ε、2^44、2^46、2^47−1、2^63）实测与手算一致，Isla 求值无误。

配置后地图外的访存按 `zpmaCheck` 走 access-fault 路径而非成功路径；
写事件地址全部落入配置区域，成功与 fault 两类路径仍并存输出。

### PMA 边界符号化：`size = "symbolic"`（W17/S2）

把单个 region 的 `size` 声明为符号边界：注入时对 IR 字段 `zsizze` 声明
64 位符号常量，`zrange_subset` 的无符号比较随边界取值分叉——同一钉址
访存可同时产出"界内→Retire_Success+写事件"与"界外→AccessFault"两类
路径，各路径 JSON 的 pre-state 以 `pma_regions.<name>.size` 键输出该路径
模型下的边界具体值（未约束该符号的路径不输出，与 pre-state 过滤规则一致）。

```toml
[[pma_regions]]
name = "ram"
base = "0x80000000"          # base 保持具体（地图列表按 base 降序遍历）
size = "symbolic"            # 或具体十六进制（W10 行为不变）
size_bounds = ["0x1000", "0x80000000000"]   # 可选：闭区间取值域
attr = "ram"
```

- `size_bounds` 可省略，默认闭区间 `[0x1000, 0x80000000000)`（4KiB..
  2^43，上界锚定 W13 实测的 emu RAM 顶界），防全 64 位空间稀释求解。
- 自校验：`size_bounds` 必须二元/下界>0/下界≤上界/base+上界不溢出；
  具体尺寸搭配 `size_bounds` 报错。属性字段（attr 等）本期不做符号化。
- 重叠检查按符号域上界保守处理：任意模型取值下相邻 region 都不重叠。
- 注入时机与具体路径不同：符号常量必须活在本次求解的 solver 里（配置
  期无 solver），故不走 `default_registers`，而是在 solve-state 启动、
  checkpoint 之前把整张地图赋给执行帧的 `zpma_regions`（镜像符号 PMP
  的装配方式），取值域约束（bvule）对全部路径生效。
- 全具体配置（不含 `size = "symbolic"`）时走 W10 配置期注入，行为与
  既有版本逐项一致。

示例配置：`configs/riscv64_difftest_mem_excluded_pma_sym.toml`。

> **Oracle 提醒（S4 未来职责）**：符号边界路径输出的"地图假设"（某地址
> 在该模型的边界取值下界内/界外）与固定平台（emu 实际 RAM）重放的匹配，
> 属 pipeline 预分类/重放阶段的职责，本仓库当前不处理。

### CSR 符号化：`[symbolic_registers]`（W21）

原则：**所有 CSR 原则上都应符号化，只有无探索意义的 bitfield 可钉死**。
`[registers.defaults]` 的具体值对 CSR 的效果是双重的：执行帧初值被钉死，
且 encdec/assembly 物化门（`try_get_assembly_*` 用独立 solver + 原始
寄存器表执行 `zencdec/zassembly`）读到的是这个具体值——这正是 G8 判定
的 FD 物化全灭根因（`mstatus=0x600` 令 `currentlyEnabled(Ext_Zcd)` 的
`mstatus[FS]≠0` 守卫具体假，C_FLD/C_FSD/C_FLDSP/C_FSDSP 已执行完的路径
被 encdec=None 整批丢弃）。

`[symbolic_registers]` 把 CSR 从 defaults 摘除、改挂符号声明，注入时机
镜像 W17 符号 PMA：solve-state 启动、`setup_pre_state` 之后、checkpoint
之前，对每个声明的 CSR 按其 IR 类型（`bits(w)` 或单 `bits(w)` 字段的
struct，如 mstatus `struct zMstatus { zbits: %bv64 }`，w≤64）声明 solver
符号常量，附加位级钉死与位组域约束断言，覆盖执行帧并同步 pre_state
记录（输出走 pre_state 主通道，模型值直接出现在 isa-state）。物化门则
按当前路径模型把符号 CSR 具象化后评估（`concretize_symbolic_csrs`），
守卫的真实性由路径模型承载。

```toml
[symbolic_registers]
satp = "symbolic"              # 字符串形式：整寄存器符号化，无位约束

[symbolic_registers.mstatus]   # 表形式：可选位级钉死 + 位组域约束
pin_mask  = "0x8000003000000000"   # SD(63)|MBE(37)|SBE(36)
pin_value = "0x0"                  # 钉死为小端 + 初始非脏
nonzero_groups = [[13, 14]]        # FS[14:13] != Off
```

- `pin_mask/pin_value`：注入后断言 `(sym & mask) == value`，钉死位不产生
  探索分支。选择"符号后 Assert"而非"构造期混具体段（MixedBits）"的理由：
  `Val::Symbolic` 是执行器最普适的值形状（执行期 CSR 写回、subrange、
  比较路径零风险；MixedBits 在部分 primop 无显式臂且 primop 层本轮禁改），
  且与 W17（符号声明 + bvule 断言）机制同构。
- `nonzero_groups`：每组断言"组内位按位或 ≠ 0"。用于表达"该位组有探索
  意义的取值域"——solve-state 绕过 decode，clause execute 本体不读 FS，
  纯符号时模型任意值取 0 会让 encdec 守卫恒假；FS≠0 域约束是 decode
  守卫语义的最小复刻（FS=Off 的路径本就会被 encdec 物化门丢弃，合法）。
- 钉死位选择（mstatus/RV64）：SD=只读状态镜像（dirty 投影）、MBE/SBE=
  大小端必须小端（模型与 emu 重放均 LE）；FS/VS/MPP/SPP/MPIE/MIE/SPIE/
  SIE/TVM/MXR/SUM/MPRV/TSR/TW/UXL/SXL 等保持符号。
- 冲突硬失败（防歧义）：与 `[registers.defaults]` 同名（解析期）、与
  `[pmp]` 规则注入的 pmpcfg/pmpaddr（isarch_main 复查）、与 CLI
  `--prestate` 同名（启动期）；未知寄存器名（不在 symtab）解析期报错。
- 未声明任何符号 CSR 时全链路零开销（门直接用原寄存器表）。

验收（FD 恢复）：`configs/riscv64_difftest_mem_excluded_pma_csr_sym.toml`
下 C_FLD/C_FLDSP 各 gen=32（24 AccessFault+8 Retire_Success）、
C_FSD/C_FSDSP 各 gen=24（16+8），与 G8 日志"已执行但被物化丢弃"的分布
逐项一致；isa-state 的 mstatus 模型值全部 FS≠0 且钉死位全 0。对照观察：
zSTORE（非 FD clause）新旧配置 gen=128（104 AF+24 RS）、fork 数 514、
耗时 6s 逐项一致——符号化声明对不读 FS 门的 clause 无分布影响。

全 CSR 逐项审计（misa/satp/mcountinhibit/mcyclecfg/minstretcfg/
mtimecmp/stimecmp/PMP 族：符号化/部分钉死/保持钉死三档建议 + PMP 与
satp 两个两难）见 W21 验收产物目录中的 `csr-audit.md`（路径登记于
议题状态文档，见上仓 `agents/` 对应议题）。

### 钉死 PMP 寄存器：`[registers.defaults]`（W14）

solve-state 中未给默认值的寄存器初值为符号变量。PMP 族寄存器
（IR：`register zpmpcfg_n : %fvec(64, %struct zPmpcfg_ent)`、
`register zpmpaddr_n : %fvec(64, %bv64)`，注意是 fvec 族寄存器、
不存在独立 `pmpcfg0` 等符号）符号化时，`pmpCheck` 的"PMP 拒绝"分支
可满足，图内对齐写会产出假 AccessFault（W13：定向 92 fault/120 路径，
green 全量 107/2479）。

不能只钉 A=OFF：IR 里 `let sys_pmp_count = 16`（Sail `config
memory.pmp.count`，非 primop，`[const_primops]` 的 `sys_pmp_count=0`
是死配置），`pmpCheck` 循环结构性生效，全 OFF 空匹配后 U/S 态
fallthrough 必产 AccessFault（pmp_control.sail 循环尾部）。正确钉法＝
全 64 项 NAPOT-全1-RWX（entry0 匹配全地址空间且 RWX，pmpCheck 恒
None），与 emu 重放侧自配的 `pmpaddr0=-1/pmpcfg0=0x1f` 语义一致：

```toml
[registers.defaults]
# PMP 关闭态：NAPOT 全地址空间 RWX（cfg 字节 0x1f = L0|A=11|RWX）
"pmpcfg_n" = "[ { bits = 0x1f } ; 64 ]"
"pmpaddr_n" = "[ 0xffffffffffffffff ; 64 ]"
```

值语法：`[ v ; n ]` 复制向量（Val 解析器）；位向量字面量按十六进制
位数×4 定宽，`0x1f`=8bit、16 位十六进制=64bit，`plausible` 要求精确
位宽。验证口径：图内对齐写（如 sd@0x840b3200）重解为 Retire_Success，
地图外（<0x80000000 或 ≥8TB）仍全 fault。

零配置（未声明 `[[memory_regions]]`）的语义是彻底全符号化：符号读写的
地址全域自由、数组内容全部符号化，不隐式补任何默认区域。若需要声明常规
RAM 区域（如 difftest 重放兜底），两种显式方式二选一：

* 配置 `[[memory_regions]]` 的 `symbolic` 区域（纯声明，参考
  `configs/riscv64_difftest_mem.toml` 的 `sym_ram`）；
* 或设置环境变量 `ISLA_RISCV_DEFAULT_SYM_RAM=1`，在未配置任何 symbolic
  区域时自动补 `0x80000000` 起 256MB 的符号 RAM（与 `sym_ram` 对齐）。
  默认关闭——隐式区域会改变"零配置 = 全符号化"的设计语义，因此只在
  用户显式要求时生效。

路径结果 JSON（`output/<arch>_<clause>.json`）中的内存相关字段：

* `memory-events`：本路径的 ReadMem/WriteMem 访存事件，按**真实执行顺序**排列
  （轨迹本身是逆时间序，收集层已整体反转）。地址/数值经 model 物化为
  `N'hHEX` 字符串，查不到模型值的分量输出 null。
* `pre-memory` / `post-memory`：按事件顺序重放得到的稀疏内存快照，元素为
  `{address, bytes, value}` 连续段（段长不超过 8 字节，`value` 是段内字节按
  小端拼成位向量的十六进制）。规则：
  * `pre-memory`：每个被触碰字节在**首次被触碰时**的内容——首触是读则取该
    读值对应字节；首触是写则初值自由，`value` 为 null（不编造）。
  * `post-memory`：重放结束后的最终字节内容；只读未写的字节取最后一次读值
    （数组模型下与写数据一致）。
  * 地址或数值分量查不到模型值时输出 null 并在日志中计数。

`WriteMem` 的 `value` 是返回布尔值，`data` 才是写入位串，`exclusive`
标明独占写。普通写发出事件即更新数组，与布尔值无关；独占写仅在布尔值
为 true 时更新，false 时不更新，未知时 `post-memory` 对相关字节输出 null。
异常路径上的 `post-memory` 描述这些事件的重放结果，不单独证明硬件提交。

路径终值物化（最终 `check_sat` + 取模型）的两层策略（W6）：

* 若路径最后一次 `check_sat` 已返回 Sat 且其后没有新增断言，直接复用
  solver 中仍持有的那次模型，跳过重复求解（数组模型的读写约束是在最后
  一次 check 之后直接 Assert 的，重解代价可能远高于执行期查询）。
* 否则按时间盒重解：环境变量 `ISLA_RISCV_MODEL_TIMEOUT_MS`（毫秒，默认
  30000）。超时路径不卡死整个 clause，而是降级输出 JSON——`ret_val` 等
  无需模型的结果字段照常，`test-ins`/`isa-state`/`memory-events`/
  `pre-memory`/`post-memory` 等模型物化字段置空，日志汇总降级路径数。
  真正中断 Z3 需要 `smt-thread-interrupt` feature（`make solve-%` 默认
  启用）；未启用该 feature 的构建无法中断，行为退化为普通 `check_sat`。

历史问题（W6/W7 已定位，W8 落定分层，W9 移除白名单机制）：配置显式
`symbolic` 区域（如 `riscv64_difftest_mem.toml` 的 `sym_ram`）且无条件
生成"地址圈进 Symbolic 并集"的区域地址约束时，约束链与模型内 PMA/PMP
路径约束联立会把带真实访存事件的完成路径判成 Unsat（根因：PMA 首析取
分支把地址钉进 ROM [0x1000,0x2000)，与 sym_ram OR 链不相交）。W8 曾以
`ISLA_RISCV_CONSTRAIN_ADDR_TO_REGIONS` 开关（定向重放档）承载该机制；
W9 按新语义整体删除该开关与白名单链——symbolic 区域降级为纯声明，需要
"路径过滤"的场景改用 excluded 判死区域（NOT 链 + W7 立即判死，
BadRead/BadWrite 尽早剪枝）。排查残留 Unsat 可设
`ISLA_RISCV_DUMP_UNSAT_DIR=<目录>`，被丢弃的 Unsat 完成路径会导出求解器
断言集（`<目录>/unsat_<clause>_t<tid>.smt2`）。

压缩指令（如 C_LD/C_SD）的 clause 返回 `ExecuteAs(转换后的指令)` 后，
`solve-state` 参照模型外层模式（`postlude/step.sail` 的
`ExecuteAs(other_inst) => execute(other_inst)`）继续执行转换后的指令：收集阶段
把（转换后的指令、该路径 solver 的 checkpoint）入队，本轮全部路径完成后由外层
循环统一用多线程池执行下一轮（转换出的 LOAD/STORE 自身会大量 fork，须并行；
嵌套或串行执行都会显著变慢）。续执行以 checkpoint 重放重建 Z3 会话，数组内存
模型的状态链（DefineConst 序列）随轨迹重放延续；调用帧用初始符号寄存器/初始
内存重建（模型中 ExecuteAs 仅由解码 clause 产生，返回前无访存/寄存器副作用），
访存事件进入同一条路径的轨迹并一起物化。

## Project structure

* __isla-lib__ Is a Rust library which contains the core symbolic
  execution engine and an API to interact with it.

* __isla-axiomatic__ Contains rust code to handle various aspects
  which are specific to checking axiomatic concurrency models on top
  of isla-lib, such as parsing litmus tests, analysing instruction
  footprints, and defining a high-level interface to run litmus tests.

* __isla-cat__ Is a translator from (a fragment of) the cat memory
  models used by herdtools into SMTLIB definitions. It has its own
  README [here](isla-cat/README.md).

* __isla-litmus__ Is an (optional) OCaml utility that maps the
  `.litmus` files that herdtools uses into a format we can read.

* __isla-sail__ Is an (optional) OCaml utility that maps Sail
  specifications into the IR we can symbolically execute.

* __web__ Contains a server and client for a web interface to the
  axiomatic concurrency tool

* __src__ Defines multiple small executable utilities based on
  isla-lib


## People

- [Alasdair Armstrong](http://alasdair.io/") (University of Cambridge)
- [Brian Campbell](http://homepages.inf.ed.ac.uk/bcampbe2/) (University of Edinburgh)
- [Ben Simner](https://www.cl.cam.ac.uk/~bs630/) (University of Cambridge)
- [Thibaut Perami](https://www.cst.cam.ac.uk/people/tp496) (University of Cambridge)
- [Peter Sewell](https://www.cl.cam.ac.uk/~pes20/) (University of Cambridge)

## Funding

This software was developed by the University of Cambridge Computer
Laboratory (Department of Computer Science and Technology), in part
under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), in part funded by
EPSRC Programme Grant EP/K008528/1 "REMS: Rigorous Engineering for
Mainstream Systems", in part funded from the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation
programme (grant agreement No 789108, "ELVER"), in part supported by
the UK Government Industrial Strategy Challenge Fund (ISCF) under the
Digital Security by Design (DSbD) Programme, to deliver a DSbDtech
enabled digital platform (grant 105694), in part funded by an Arm
iCASE doctoral studentship (18000005, Simner), and in part funded by
Google.
