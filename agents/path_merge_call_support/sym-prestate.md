# 符号特权前态：ecfg4b Sv39 LOAD 测量（2026-11-08）

**结论：将 cur_privilege、SUM/MXR 放入同一次符号求解可行，收益明确，开销在本轮预算内。E2 比固定前态多 631 类、64 个形状，耗时约 1.72 倍。再放开 MPRV/MPP 的 E3 多出大量模型接纳的状态，但形状没有再增加，耗时增至 E0 的约 3.85 倍；其中 1461 个代表设置 MPRV=1，正常 xRET 进入 U/S 的回放入口不能这样设置。**

建议把 U/S、SUM/MXR 作为带合法性约束的符号前态；MPRV 的硬件行为应后续在当前 M 态、MPP=U/S 的域中测量。无需手工拆特权网格，但必须明确输入域与回放入口；不能把符号输入任意组合当作可从复位到达的状态。

## E0–E3 数字

| 实验 | 放开的维度 | 类数 | 形状数 | 路径数 | 导出秒 | 耗时/E0 | 较 E0 新增类／形状 | 全量成员检查 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| E0 | 无（S、SUM=1、MXR=MPRV=0） | 728 | 136 | 26 | 171.11 | 1.00× | +0／+0 | 728/728 |
| E1 | cur_privilege∈{U,S} | 1086 | 156 | 26 | 237.55 | 1.39× | +358／+20 | 1086/1086 |
| E2 | E1＋SUM、MXR | 1359 | 200 | 26 | 294.79 | 1.72× | +631／+64 | 1359/1359 |
| E3 | E2＋MPRV、MPP∈{U,S} | 2820 | 200 | 26 | 659.41 | 3.85× | +2092／+64 | 2820/2820 |

四组均在 900 秒内自然结束，枚举未按路径预算截断，执行/SMT/终值查询超时、未完成路径和待处理批次均为 0。结束路径数一直是 26；新增行为主要出现在路径内部合并的权限条件中，所以类数和形状会增长，而结束路径数不变。

**保留原始状态：四次导出的退出码均为 1、`status=partial/errors=5`。** 日志均记录 `Bad read symbolic address falls in excluded memory region`。本轮计时导出没有加载额外观察器，也没有为这 20 项导出错误分别保存查询证明；不能将它们直接改写为 `finished`，也不能据此签收排除域以外的模型行为全集。表中统计的是实际完成路径的完整守卫类枚举与每类一个 corpus entry。

## 全量 `--check-samples`

全部 **5993/5993** 个 corpus entry 各满足 `(accepted_paths,consistent_paths,inconsistent_paths)=(1,1,0)`。逐组校验原始 sample_id 集合、报告分母和唯一性；没有抽样或只检查可解码子集。

| 实验 | 检查条数 | 检查秒 | 原始 errors | 独立证明为排除域的错误 |
| --- | ---: | ---: | ---: | ---: |
| E0 | 728 | 82.66 | 5 | 5 |
| E1 | 1086 | 114.80 | 5 | 5 |
| E2 | 1359 | 141.29 | 5 | 5 |
| E3 | 2820 | 269.50 | 5 | 5 |

成员检查使用各自相同的 IR/config/固定输入，关闭导出枚举，单独逐路径检查具体输入。检查运行的原始退出码 1、partial、errors 和样本报告的 `completed=false` 同样保留；该全局标志受执行错误影响，逐条的接纳计数与一致性另行核对。每次检查用 ecfg4b 的只读 `observe.so` 保存失败查询，再用其 `check_badread` 验证：原查询 UNSAT；仅去除当前 excluded 条件、保留历史断言和读值一致性后 SAT；harness 重叠仍 UNSAT。E1–E3 的快照另触发 Z3 文本导出的枚举命名冲突：构造子声明为 k!00/k!10 等，使用处却写成 k!0/k!1 等，且与数组 k!0 重名。只在产物副本中依据枚举变量的类型把这些构造子引用对应到声明名；原查询完整保留，全部断言、类型和数组引用保留。每份副本都有逐项 normalization.json，修正脚本为 `output/sym-prestate/normalize_query.py`。全部 20 项检查错误均通过，零超时和未完成路径。这些证明绑定检查运行，不冒充计时导出时逐查询取证。

完整证据：[check-summary.json](../../output/sym-prestate/check-summary.json)、各 `E*-check/check.json`、`badread/query-*.proof.json`。此处 PASS 只指具体输入的唯一接纳和后态一致，不表示硬件重放通过。

## 实验范围与复现材料

本次是测量实验，没有修改 Isla/Sail 源码，没有 Git 写操作。工作树是 `feat/isla-sym-prestate`，HEAD `78b04e3df9876315ab07d32e5d8a6c5f2bb9383d`。只写 `output/sym-prestate/` 和本文；没有更新全仓状态表或其他议题文件。

只读来源为 `../replay-p0/output/ecfg4b/`（路径相对本工作树根目录）：

- 原 IR：`rv64d.ir`，沿用 ecfg4b 香山专用配置生成的新模型。来源模型提交及构建过程见 [ecfg4b 记录](../../../replay-p0/agents/p0_replay/ecfg4b-results.md)。
- 求解器入口：`bin/isarch`，直接复用 ecfg4b 已用二进制；未重编。四项测量都用它，避免换工具造成差异。
- 配置基础：`config-xs.toml`；枚举配置：`enumeration.toml`，`class_cap=1`、`path_cap=1000000`、`sample_stride=1`。
- 原完整命令：`sv39-load/done.json`。本轮每次精确 argv、开始时间、墙上耗时和退出状态在各 `E*/done.json`，成员检查在 `E*-check/done.json`。

公共设置为 Sv39、`LOAD`、指令 `0x0000b103`（`ld x2,0(x1)`）、`x1=0x20000000`、`satp=0x8000000000080200`、`menvcfg=senvcfg=mseccfg=0`。保持原 PMA、PMP、内存内容区和设备排除区。正式 E1、E2、E3 及成员检查串行运行，各 `-T 64`；`--smt-timeout 5 --timeout 890`，每次进程外限 900 秒，未加时。

E0 恢复过程中误判旧进程已停，启动了一次重复测量。旧运行实际也完成了 728/136/26，179.27 秒，产物保留在 `E0-interrupted/`（名称反映当时判断，不能据名字认定被中断）。两次 E0 重叠约 6.7 秒；表中采用第二次 E0 的 171.11 秒，其余正式导出没有相互重叠。因此表中的耗时是共享机器上的单次观测，不能视为稳定性能分布。第一次 E1 在译码阶段失败，保留于 `E1-decode-failed/`，不计入正式数据。

完整产物入口：[运行脚本](../../output/sym-prestate/run.py)、[配置与 IR 副本生成脚本](../../output/sym-prestate/prepare.py)、[串行调度记录](../../output/sym-prestate/sequence.log)、[解码分析](../../output/sym-prestate/analysis.json)、[形状差异](../../output/sym-prestate/comparison.json)。脚本拒绝覆盖已有运行目录；复跑须使用新的产物目录。没有手工重算来源文件或二进制哈希；isarch 自带的 provenance 字段原样保留。

## 如何限定符号前态

`parse_fixed_prestate` 只接受完整顶层寄存器赋值；不能写 `mstatus.SUM=...`。`setup_pre_state` 会把 `reg_list` 中未通过 `--prestate` 固定的寄存器重新创建为符号值，其中包括 `cur_privilege` 和 `mstatus`。`[symbolic_registers]` 支持位向量或单 bits 字段结构体，以 `(bits & pin_mask) == pin_value` 施加位约束，并非只能整寄存器无约束。与 `registers.defaults` 或 `--prestate` 同名冲突会硬失败。

| 配置副本 | 执行前态的变化 |
| --- | --- |
| `output/sym-prestate/E0.toml` | 原配置逐字复制，保留原全部 `--prestate` |
| `output/sym-prestate/E1.toml` | 去掉 `--prestate cur_privilege=Supervisor`；入口约束 U/S；mstatus 仍固定 `0x0000000a00040000` |
| `output/sym-prestate/E2.toml` | 再去掉 mstatus 的 `--prestate` 和配置默认值；`pin_mask=0xfffffffffff3ffff`、`pin_value=0x0000000a00000000`；仅 SUM[18]/MXR[19] 自由 |
| `output/sym-prestate/E3.toml` | `pin_mask=0xfffffffffff1f7ff`、`pin_value=0x0000000a00000000`；再放开 MPRV[17] 和 MPP[11]；MPP[12] 仍钉 0，因此 MPP∈{00,01}，即 U/S |

E1–E3 另在 `registers.defaults` 增加 `cur_privilege="Supervisor"`，仅用于固定机器字的独立译码。没有它，CFI 译码会读取未确定的权限，报 `ext_decode 返回依赖符号状态的值，不能跨solver复用`。执行阶段 `setup_pre_state` 会覆盖该默认值。实际导出的 U、S 两种前态证明执行没有被钉回 S。E2/E3 的 mstatus 配置默认值已删除，没有与 `[symbolic_registers]` 冲突。

### IR 副本：唯一新增的语义是 U/S 输入约束

用户明确允许在 `output/` 的 IR 副本上加入口约束。原 IR 未改。副本是 [output/sym-prestate/rv64d-us.ir](../../output/sym-prestate/rv64d-us.ir)，来源是上述 ecfg4b `rv64d.ir`；E0 使用原 IR，E1–E3 使用此副本。

[精确差异](../../output/sym-prestate/rv64d-us.diff)只有两处：原 IR 第 58568 行的 `val zexecute` 附近增加原函数体的新名字和 `assume` 原语声明；原第 288186 行 `fn zexecute` 入口改为下面的包装调用。副本中包装函数从第 288190 行开始，原函数体从第 288197 行开始：

```text
val zsym_prestate_execute_body : (%union zinstruction) -> %union zExecutionResult
val zsym_prestate_assume = "assume" : (%bool) -> %unit

fn zexecute(zmergez3var) {
  zsym_prestate_constraint : %unit;
  zsym_prestate_constraint = zsym_prestate_assume(@or(@eq(zcur_privilege, zUser), @eq(zcur_privilege, zSupervisor)));
  return = zsym_prestate_execute_body(zmergez3var);
  end;
}
```

原 `zexecute` 函数体仅改函数名为 `zsym_prestate_execute_body`，内部每一条指令、原语调用、源位置和数字跳转目标逐字不变。包装方式避免在原函数体前插指令后重排所有数字跳转。`prepare.py` 用可逆替换确认：删除新增声明和包装函数并恢复原函数名后，全文逐字等于原 IR。没有改权限检查或页表遍历行为。

这条 `assume` 在当前路径求解器中断言 `cur_privilege=User ∨ cur_privilege=Supervisor`。它排除 M、VU、VS，不选择 U/S 中的某一个；也不分别运行两个特权配置。包装增加的调用与约束开销包含在 E1–E3 的测量时间里，未单独拆出。

`[symbolic_registers]` 的执行实现不支持枚举寄存器。`[initial_state]` 的位约束也不能限定枚举；`--reset-constraint` 只在模型调用 `reset_registers` 时执行，本次 `solve-state` 直调 `execute` 不经过该调用。因此没有把未执行的 reset 约束当成已经生效。

## 新行为与代表输入

形状采用既有 `pt_decode.shape_key`：包括访问类型、页表级数、逐级 PTE 类型及 R/W/X/U、叶级别、结果和失败原因。它不直接把 cur_privilege、SUM/MXR、MPRV/MPP 全部放进键。数字是本轮每类一个代表得到的形状集合，不是所有具体位组合的数量。

- E1 比 E0 多 20 个形状，原 136 个均保留。新增都是 U 态遇到 U=0 叶 PTE 的 `privilege_permission` 页异常，覆盖 4KiB、2MiB、1GiB 和合法 64KiB NAPOT 的不同权限格式。
- E2 比 E1 多 44 个形状：20 个是 SUM=0 的 S 态遇到 U=1 叶 PTE；另外 24 个是 MXR=1 时 X-only（R=0、X=1）页通过读取权限检查，随后出现成功、A=0 页异常或数据地址的 PMA 访问异常，各 8 个形状。相对 E0 合计新增 64 个形状，原形状均保留。
- E3 比 E2 多 1461 类，耗时约 2.24 倍；200 个形状的键集合与 E2 完全相同。它新增 `effectivePrivilege` 的 MPRV 条件和 `privLevel_bits_forwards` 的 MPP 条件。现有形状键不包含 MPRV/MPP，因此不能把“形状没增加”说成“没有新增条件组合”。
- 新维度确实进入已有条件图：E1 新增 `check_PTE_permission` 第 147/155 行对应的守卫位置；E2 再新增第 150 行的 SUM 条件。MXR 通过原第 155 行读取权限条件参与求解，不要求每一位都对应新结束路径。

[抽查记录](../../output/sym-prestate/examples.json)保留 sample_id、path_signature、class_id、完整逐级 PTE 与地址。每个 sample_id 只在其所属导出文件中解释。

| 导出／sample_id | 前态与关键叶 PTE | 模型结果与核对 |
| --- | --- | --- |
| E1／386 | U；SUM=1/MXR=0；根叶 `0xb`，U=0/R=1/X=1 | 页异常；根读取地址 `0x80200000` 在 DRAM，先在 U 权限检查终止 |
| E2／480 | S；SUM=0/MXR=0；根叶 `0x1b`，U=1/R=1/X=1 | 页异常；SUM 不允许 S 访问该 U 页，未实际读取叶目标 |
| E2／266 | U；MXR=1；根叶 `0x200000d9`，U=1/R=0/X=1/A=1，PPN=`0x80000` | 成功；1GiB 对齐成立，PA=`0x80000000+0x20000000=0xa0000000`，位于 DRAM，读值 0 与 x2 后态一致 |
| E2／168 | U；MXR=1；L1 叶 `0x99`，U=1/R=0/X=1/A=0 | 读取权限通过后，Svade 因 A=0 报页异常 |
| E2／512 | S；SUM=1/MXR=1；L0 叶 `0x0e400cd9`，U=1/R=0/X=1/A=1 | 权限通过，PA=`0x39003000` 落在平台 hole `[0x39002000,0x3a000000)`，报访问异常；没有伪造该地址的实际内存读取 |

E3／318 另展示了新增条件组合：当前 U、`mstatus=0xa00020800`（MPRV=1、MPP=S、SUM=MXR=0），L1 叶 `0x200800cb`，U=0/R=1/X=1/A=1。模型按有效 S 权限成功读取 PA=`0x80200000`（位于 DRAM），与正常当前 U、MPRV=0 应被拒绝的行为不同。该例通过模型检查，但不能经普通 mret 入口恢复此 U/MPRV 组合。

前两例的 A 也为 0；模型按顺序先检查权限，所以抽查证明其记录与执行顺序一致，不把这些单例当成已隔离 A 位的对照实验。全部实际 PTE/数据读地址另做了 DRAM 范围检查。权限已失败时叶 PPN 可以为 0，因为执行没有继续访问该目标；不能把这种未发生的访问误判成设备样本。

## 前态合法性与覆盖边界

全量 [state-audit.json](../../output/sym-prestate/state-audit.json) 确认 5993 条输入都满足各自的特权域和完整 mstatus 掩码，违反数为 0。E3 中 MPRV=0 有 1359 条、MPRV=1 有 1461 条；后者的代表全部选择了当前 U，MPP 为 U 或 S。未观察到 MPP=2、虚拟特权级、保留位任意取值、SXL/UXL 不一致或 SD 与扩展状态位不一致的样本。约束分别为：

1. `cur_privilege ∈ {User,Supervisor}`，排除未测的 M 态与模型不支持的虚拟特权级。
2. mstatus 除目标位外保持原值，包括 `SXL=UXL=2`、FS/VS/XS/SD=0 和其余保留位。
3. E3 的 MPP[12]=0，排除保留值 2 及本轮未纳入的 M 编码 3。若以后开放 FS/VS/XS，还需 `SD ⇔ (FS=Dirty ∨ VS=Dirty ∨ XS=Dirty)`；本轮这些位全为 0，无需额外派生位约束。

Sail 的 `legalize_mstatus` 接受本轮 SUM/MXR/MPRV 和合法 U/S MPP 编码，但直接写 `--prestate` 或符号输入不等于执行 CSR 写入合法化，也不自动证明状态可从复位到达。

尤其是 E3：模型 `effectivePrivilege` 对数据访问在 MPRV=1 时使用 MPP，允许 U/S 与 MPRV=1 的直接组合；正常 `mret`/`sret` 转入 U/S 则会清 MPRV，`mret` 还把 MPP 重置到最低支持权限（本配置为 U）。因此它们是模型接纳的直接前态，不能据此声称当前普通入口可以逐位恢复这些状态。若 corpus 要求由正常 xRET 进入低特权级，须约束 `cur_privilege∈{U,S} ⇒ MPRV=0`。若具体采用 mret 入口，还须按被测指令前态要求 MPP=U；MPIE 会被入口置 1，不能假定整个 mstatus 逐位保留写入值。若目标是测 MPRV 的真实数据访问行为，应后续把当前执行特权设为 M、有效权限由 MPP∈{U,S} 给出。本轮按请求保留 E3，不静默改其输入域。

守卫类也不等于状态网格。例如 E2 的 U 态代表只出现 SUM=0：SUM 对 U 态访问权限无影响，求解器没有义务为每个类再导出 SUM=1。更早发生的无效 PTE 错误也可能尚未读取相关权限位。这是按模型行为覆盖的结果；不能用 `class_cap=1` 宣称所有前态位组合已逐个见证。

## 回放链支持 U 态：只读调查

本节仅列需要改的点，没有修改 `paging_replay.py`、`paging_fuzz.py`、设计文档或硬件代码，也没有运行新的硬件回放。调查入口是 `../replay-p0/difftest-xiangshan/` 及 [design.md](../../../replay-p0/agents/p0_replay/design.md) §6。

| 位置 | 需要调整的内容 |
| --- | --- |
| `paging_replay.py::platform_case`，约第 95–99 行 | R1 当前硬拒绝非 Supervisor。允许经同配置成员检查的 U/S 样本；继续保留固定指令、VA、SATP、空 TLB、地址范围等检查 |
| `paging_replay.py::paging_assembly`，约第 410–466 行 | 现有 MPRV 路径已把 U→MPP=0、S→MPP=1，不需要给 U 另造一套物理页表布局。保留 SUM/MXR，写 MPRV=1，并清 MIE；完成初始化后才启用 MPRV。对 E3 按解码后的有效权限处理，不能一律从 cur_privilege 覆盖掉原 MPP 而声称与原输入等价 |
| 同函数的成功与异常出口 | MPRV 方案始终在 M 态取指；成功后清 MPRV，异常 handler 也先清 MPRV，然后物理回读。仍检查 cause=13/5、tval=VA、mepc=payload_ins、x2 和内存；用 Isla 的结果作期望值 |
| `directed_probe_case` 与 `paging_assembly` 的真 S 模式 | 若需要真 U 执行，新增 U 入口模式，设置 mepc、MPP=U 后 `mret`。取指代码岛须有 U=1 的 RX/A 页表映射，并与样本使用的页表槽和内存不重叠。现有 S 取指叶 flags=`0xcb` 不能直接给 U 用；相同映射需至少加 U 位（变为 `0xdb`） |
| 真 U 的返回与 CSR 位 | MRET 会清 MPRV 并重置 MPP，恢复代码不能假定这些位仍是 mret 前写值。成功后 U 执行 `ecall`；保持 medeleg=0，异常进入 M handler，核对 mcause=8、mepc=U 返回标签、mtval=0。现有真 S 成功出口检查 cause=9，需要按入口区分。被测 LOAD 的异常仍检查 13/5，不能混成出口 ecall |
| `paging_fuzz.py::predict_sample`，约第 124–165 行 | 去掉 S-only 断言；按有效权限区分 U 要求 PTE.U=1、S 访问 U 页要求 SUM=1；LOAD 权限继续用 R∨(MXR∧X)。MPRV=1 时按 MPP 求有效权限；还须保持页表格式、A/D、PMA 与内存足迹检查 |
| `paging_fuzz.py::check_batch/check_command`，约第 435–497 行 | 模板来自原固定 S 场景，须换成本轮实际 IR/config 与约束；不能把新 U 或符号 mstatus 的样本又送回旧固定前态命令。逐条要求唯一接纳与后态一致，保留排除域错误的证明规则 |
| fuzz 的覆盖键、元数据和设计说明 | 记录有效权限、SUM/MXR，必要时记录 MPRV/MPP，避免只看旧形状键而吞掉权限行为差异；记录实际符号配置、入口方式和成员检查结果。来源哈希是记录，不能代替语义重验；本轮未改变平台锁 |

MPRV+MPP=U 足以先支持本轮 U 态 LOAD 的数据访问重放；它不证明 U 态取指、CSR 指令或陷阱后完整 mstatus 与真 U 执行等价。真 U 模式应补一次成功和一次页异常的对照，再扩大范围。现有真实 U 支持与硬件结果均未在本轮验证。
