# Isla → XiangShan DiffTest PoC 详细报告

## 结论

本报告复核了先前 `make solve` 导出的 10,799 条 `Retire_Success(())` 状态，并以 VLEN=128 的 XiangShan emulator 与其匹配的 NEMU DiffTest 动态库运行 PoC。

- 89 个状态触发 DiffTest 失败，涉及 27 条完整汇编、7 个 opcode。
- 80 个状态（`vmerge.vim/.vvm/.vxm`、`vmv.s.x`、`vmv4r.v`、`vmv8r.v`）均为 `vstart=1` 的“继续执行 vs 非法指令”差异。RVV 规范允许实现对自己不可能由中断产生的非零 `vstart` 抛非法指令，因此不构成 RISC-V ISA 违例；它们是 DiffTest 参考模型能力与 DUT 能力不一致造成的误报。
- 9 个 `vsetvl` 状态在完整标量上下文重放后 30 秒超时。它们没有非零 `vstart` 豁免，规范不允许实现无穷不退休；标为“疑似标准违例 / 活性问题”。尚须用 trap handler、`--no-diff` 与 Spike 三方复核，才能确定归属 XiangShan RTL、NEMU 或测试入口。

## 验证方法与产物

输入 PoC：`../difftest-xiangshan/inputs/isla-solve-success-all.json`。全部正常退休状态中，467 条携带通用寄存器初值，已单独用修正后的生成器重放；结果为 458 通过、9 超时失败。

生成器已修正为在 payload 前重放 `x1..x31`，并将首轮或 trace 超时持久化成 failure，不再中断批处理；其 9 项回归测试均通过。

日志字段中的 `right` 是 NEMU 参考模型，`wrong` 是 XiangShan。80 个非 `vsetvl` 项的典型日志是：NEMU 抛 `mcause=2`/ `mtval=指令编码`，XiangShan 继续执行并把 `vstart` 清零。

## RISC-V 规范判定

RVV 1.0 的 [`vstart` 章节](https://docs.riscv.org/reference/isa/unpriv/v-st-ext)允许实现：当某个 `vstart` 值不可能由该实现、该 `vtype` 下执行同一指令产生时，执行该指令可抛非法指令。规范还以“实现不会在向量算术中断”为示例。这直接覆盖本批次 80 个 `vstart=1` 的差异；[`vmerge` 章节](https://docs.riscv.org/reference/isa/unpriv/v-st-ext)同时明确按从 `vstart` 到 `vl` 的 body elements 操作，XiangShan 的继续执行也符合正常语义。

`vsetvl` 的 9 个样本均为 `vstart=0`，其失败形态为 emulator 30 秒超时而非一个已定义的架构异常。因此本报告将其标成疑似违例，但不把“超时”直接等同于 RTL 缺陷。

## GitHub 同类问题检索

- [XiangShan #5725](https://github.com/OpenXiangShan/XiangShan/issues/5725)：`vsetvl x0, x0, rs2` 路径的 XiangShan/Spike 行为不一致，状态为已修复。与本报告的 `vsetvl` 超时高度相关，但寄存器组合不同。
- [XiangShan #5772](https://github.com/OpenXiangShan/XiangShan/issues/5772)：`vmv4r.v` 寄存器对齐非法编码未触发非法指令，已确认。与本报告的 `vmv4r.v` 同指令族，但本批次 `vd=v0` 对齐，根因不同。
- [NEMU #952](https://github.com/OpenXiangShan/NEMU/issues/952)：`vsetvli/vsetivli/vsetvl` 解码掩码错误，已关闭。说明该指令族的 NEMU 解码曾有已知问题，但本批次编码 `funct3=111`，不能直接归因于该 issue。
- [NEMU #1078](https://github.com/OpenXiangShan/NEMU/issues/1078)：NEMU 对保留 RVV 编码解码过宽导致 DiffTest 不一致，仍开放；其描述还引用 `vmv<nr>r.v` 的相关解码校验问题。该 issue 与本次“参考模型/DUT 边界语义不一致”的现象相似，但不是本次非零 `vstart` 差异的直接根因。

## 每个失败 PoC

表中状态列依次为 `vstart / vl / vtype`。目录同时包含 `program.S`、`program.elf`、`case.json` 和 `difftest.log`。对于 9 条 `vsetvl`，完成标量重放后的对应 PoC 和 timeout 日志位于 `../difftest-xiangshan/work/isla-solve-success-scalar-contexts/elf/`（见后表）。

| 原始序号 | 指令 | 编码 | 状态 | PoC 目录 | 判定 |
|---:|---|---|---|---|---|
| `1` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0046` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-001` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `2` | `vmerge.vim v8, v0, 0x0, v0` | `32'h5c00_3457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_004b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-002` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3` | `vmerge.vim v2, v0, 0x0, v0` | `32'h5c00_3157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0051` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-003` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `5` | `vmerge.vim v16, v0, 0x0, v0` | `32'h5c00_3857` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_001b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-005` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `6` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0040` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-006` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `7` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-007` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `9` | `vmerge.vim v4, v0, 0x0, v0` | `32'h5c00_3257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0042` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-009` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `10` | `vmerge.vim v2, v0, 0x0, v0` | `32'h5c00_3157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0041` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0010` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `11` | `vmerge.vim v8, v0, 0x0, v0` | `32'h5c00_3457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_000b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0011` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `12` | `vmerge.vim v2, v0, 0x0, v0` | `32'h5c00_3157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0049` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0012` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `17` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0045` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0017` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `24` | `vmerge.vim v8, v0, 0x0, v0` | `32'h5c00_3457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_001a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0024` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `25` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0007` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0025` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `27` | `vmerge.vim v4, v0, 0x0, v0` | `32'h5c00_3257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0027` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `30` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0008` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0030` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `33` | `vmerge.vim v8, v0, 0x0, v0` | `32'h5c00_3457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0043` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0033` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `34` | `vmerge.vim v31, v0, 0x0, v0` | `32'h5c00_3fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_004f` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0034` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `38` | `vmerge.vim v16, v0, 0x0, v0` | `32'h5c00_3857` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0012` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0038` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `43` | `vmerge.vim v8, v0, 0x0, v0` | `32'h5c00_3457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0001` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0043` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `45` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0017` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0045` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `48` | `vmerge.vvm v8, v0, v0, v0` | `32'h5c00_0457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_001b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0048` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `49` | `vmerge.vvm v2, v0, v0, v0` | `32'h5c00_0157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0051` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0049` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `50` | `vmerge.vvm v2, v0, v0, v0` | `32'h5c00_0157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0049` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0050` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `51` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_004f` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0051` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `52` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_004e` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0052` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `53` | `vmerge.vvm v4, v0, v0, v0` | `32'h5c00_0257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_001a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0053` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `55` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0050` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0055` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `59` | `vmerge.vvm v4, v0, v0, v0` | `32'h5c00_0257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0012` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0059` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `60` | `vmerge.vvm v8, v0, v0, v0` | `32'h5c00_0457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_000b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0060` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `64` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0040` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0064` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `65` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0005` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0065` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `66` | `vmerge.vvm v8, v0, v0, v0` | `32'h5c00_0457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0043` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0066` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `67` | `vmerge.vvm v2, v0, v0, v0` | `32'h5c00_0157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0011` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0067` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `71` | `vmerge.vvm v2, v0, v0, v0` | `32'h5c00_0157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0059` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0071` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `72` | `vmerge.vvm v8, v0, v0, v0` | `32'h5c00_0457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0013` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0072` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `75` | `vmerge.vvm v4, v0, v0, v0` | `32'h5c00_0257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_005a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0075` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `77` | `vmerge.vvm v2, v0, v0, v0` | `32'h5c00_0157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0001` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0077` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `80` | `vmerge.vvm v31, v0, v0, v0` | `32'h5c00_0fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0007` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0080` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `81` | `vmerge.vvm v4, v0, v0, v0` | `32'h5c00_0257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0052` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0081` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `88` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_000e` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0088` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `92` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_000f` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0092` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `95` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_004f` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0095` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `98` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0007` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0098` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `101` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0046` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0101` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `102` | `vmerge.vxm v16, v0, x0, v0` | `32'h5c00_4857` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_001b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0102` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `104` | `vmerge.vxm v4, v0, x31, v0` | `32'h5c0f_c257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_001a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0104` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `108` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_001a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0108` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `109` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0045` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0109` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `115` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0005` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0115` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `116` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_004e` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0116` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `120` | `vmerge.vxm v4, v0, x0, v0` | `32'h5c00_4257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0012` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0120` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `126` | `vmerge.vxm v4, v0, x31, v0` | `32'h5c0f_c257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_004a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0126` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `127` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0053` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0127` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `128` | `vmerge.vxm v4, v0, x0, v0` | `32'h5c00_4257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0042` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0128` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `130` | `vmerge.vxm v2, v0, x31, v0` | `32'h5c0f_c157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0001` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0130` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `131` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0048` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0131` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `135` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0043` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0135` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `136` | `vmerge.vxm v2, v0, x0, v0` | `32'h5c00_4157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0011` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0136` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `137` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0137` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `140` | `vmerge.vxm v4, v0, x0, v0` | `32'h5c00_4257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_004a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0140` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `142` | `vmerge.vxm v2, v0, x31, v0` | `32'h5c0f_c157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0041` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0142` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `146` | `vmerge.vxm v4, v0, x31, v0` | `32'h5c0f_c257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0052` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0146` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `147` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_005b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0147` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `149` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0048` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0149` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `150` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0040` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0150` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `154` | `vmerge.vxm v2, v0, x31, v0` | `32'h5c0f_c157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0019` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0154` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `157` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0017` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0157` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `160` | `vmerge.vxm v4, v0, x0, v0` | `32'h5c00_4257` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0052` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0160` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `163` | `vmerge.vxm v2, v0, x31, v0` | `32'h5c0f_c157` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0051` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0163` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `165` | `vmerge.vxm v31, v0, x0, v0` | `32'h5c00_4fd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0165` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `167` | `vmerge.vxm v31, v0, x31, v0` | `32'h5c0f_cfd7` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0047` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0167` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `168` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_0003` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0168` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `173` | `vmerge.vxm v8, v0, x31, v0` | `32'h5c0f_c457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0002` / `64'h0000_0000_0000_000a` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0173` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `175` | `vmerge.vxm v8, v0, x0, v0` | `32'h5c00_4457` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_004b` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-0175` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3294` | `vmv8r.v v0, v0` | `32'h9e03_b057` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0024` / `64'h0000_0000_0000_0003` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3294` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3300` | `vmv4r.v v0, v0` | `32'h9e01_b057` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0011` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3300` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3302` | `vmv4r.v v0, v0` | `32'h9e01_b057` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0018` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3302` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3306` | `vmv8r.v v0, v0` | `32'h9e03_b057` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0011` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3306` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3318` | `vmv.s.x v0, x31` | `32'h420f_e057` | `64'h0000_0000_0000_0001` / `64'h0000_0000_0000_000f` / `64'h0000_0000_0000_0052` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3318` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3335` | `vmv.s.x v0, x0` | `32'h4200_6057` | `64'h0000_0000_0000_0004` / `64'h0000_0000_0000_001f` / `64'h0000_0000_0000_0041` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3335` | 允许差异：vstart 非零，参考模型可合法抛非法指令 |
| `3715` | `vsetvl x0, x31, x0` | `32'h800f_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3715` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3718` | `vsetvl x0, x26, x1` | `32'h801d_7057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0010` / `64'h0000_0000_0000_0040` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3718` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3719` | `vsetvl x0, x31, x31` | `32'h81ff_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3719` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3722` | `vsetvl x0, x8, x1` | `32'h8014_7057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3722` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3724` | `vsetvl x0, x2, x1` | `32'h8011_7057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3724` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3731` | `vsetvl x0, x31, x0` | `32'h800f_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0003` / `64'h0000_0000_0000_0010` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3731` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3736` | `vsetvl x0, x31, x31` | `32'h81ff_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3736` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3739` | `vsetvl x0, x31, x0` | `32'h800f_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h8000_0000_0000_0000` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3739` | 疑似：完整标量重放后超时；无 vstart 许可 |
| `3747` | `vsetvl x0, x31, x31` | `32'h81ff_f057` | `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0000` / `64'h0000_0000_0000_0018` | `../difftest-xiangshan/work/isla-solve-success-all/elf/case-3747` | 疑似：完整标量重放后超时；无 vstart 许可 |

## vsetvl 完整标量重放位置

| 指令 | 修正后 PoC 目录 | 结果 |
|---|---|---|
| `vsetvl x0, x31, x0`（3 条） | `case-086`、`case-099`、`case-107` | 30 秒 execution timeout |
| `vsetvl x0, x26, x1` | `case-088` | 30 秒 execution timeout |
| `vsetvl x0, x31, x31`（3 条） | `case-089`、`case-104`、`case-115` | 30 秒 execution timeout |
| `vsetvl x0, x8, x1` | `case-091` | 30 秒 execution timeout |
| `vsetvl x0, x2, x1` | `case-092` | 30 秒 execution timeout |

修正后目录前缀：`../difftest-xiangshan/work/isla-solve-success-scalar-contexts/elf/`。

## 下一步建议

1. 对 9 条 `vsetvl` 用独立的 Machine-mode trap handler 与 `--no-diff` 运行，记录是否退休、是否陷入、`mcause/mepc/mtval`，再与 Spike 比较。
2. 将非零 `vstart` 的“非法指令允许集”编码到 DiffTest 过滤规则，或只在被测实现可产生的 `vstart` 值上做锁步比较，避免将规范许可的选择误报为 bug。
3. 若 `vsetvl` 在无 DiffTest 时仍不退休，以最小化的 `case-086` 报告 XiangShan issue，并引用 #5725；若仅 NEMU/DiffTest 时失败，则向 NEMU/ready-to-run 报告。
