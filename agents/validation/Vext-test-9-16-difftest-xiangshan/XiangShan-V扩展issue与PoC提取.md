# XiangShan V 扩展 Issue 与 PoC 提取

本文从 `XiangShan-V扩展issue与mutation策略.md`（89 条去重 issue 的核验报告）与 `V扩展issue核验与PoC数据.json` 中，把 issue 清单和 PoC 触发材料单独提取成册，供后续测试生成直接引用。

口径沿用源文档：确认状态 confirmed/fixed/partial/not_confirmed/reported 相互独立；"关闭"不等于"确认"。PoC 代码均为原帖保真节选，不宣称独立可运行；无材料的条目只登记不展开。第三部分归纳 issue 报告者使用的四种固定模版、其承载的上下文构造机制，以及模版之外的方式。

## 一、89 条 Issue 全量简表

| Issue | 确认 | 范围 | PoC材料 |
|---|---|---|---|
| #2890 | partial | 历史混合 | 原始C/汇编workload |
| #3012 | not_confirmed | 工具/历史修复 | 无 |
| #3200 | not_confirmed | 预期/无效 | 无 |
| #3488 | not_confirmed | 预期/无效 | 无 |
| #3962 | not_confirmed | 预期/无效 | 无 |
| #4017 | not_confirmed | 预期/无效 | 无 |
| #4190 | confirmed | 性能/假依赖 | 完整benchmark |
| #4368 | not_confirmed | 预期/无效 | 无 |
| #5279 | confirmed | 工具/差分测试 | 日志/附件 |
| #5288 | not_confirmed | 预期/无效 | 无 |
| #5424 | not_confirmed | 工具/重复映射 | 无 |
| #5425 | not_confirmed | 预期/无效 | 无 |
| #5426 | fixed | 工具/参考模型 | 日志 |
| #5449 | not_confirmed | 预期/无效 | 无 |
| #5702 | not_confirmed | 预期/无效 | 无 |
| #5725 | fixed | 行为对齐 | 日志 |
| #5739 | fixed | RTL/配置CSR | 触发代码节选 |
| #5765 | confirmed | RTL/mask-tail | 触发代码节选 |
| #5766 | confirmed | RTL/FOF | 触发代码节选 |
| #5767 | confirmed | RTL/FOF | 触发代码节选 |
| #5768 | confirmed | RTL/非法编码 | 仅RTL译码条件 |
| #5769 | reported | 未明 | 无 |
| #5770 | reported | 未明 | 无 |
| #5772 | confirmed | RTL/非法编码 | 附件完整汇编 |
| #5777 | not_confirmed | 预期/无效 | 无 |
| #5790 | not_confirmed | 预期/无效 | 无 |
| #5808 | reported | 未明 | 无 |
| #5809 | fixed | RTL/非法编码 | 触发代码节选 |
| #5829 | confirmed | RTL/标量扩展 | 触发代码节选 |
| #5830 | confirmed | RTL/标量扩展 | 触发代码节选 |
| #5831 | confirmed | RTL/合法内存 | 触发代码节选 |
| #5832 | confirmed | RTL/合法内存 | 触发代码节选 |
| #5840 | confirmed | RTL/标量扩展 | 触发代码节选 |
| #5845 | reported | 未明 | 无 |
| #5865 | confirmed | RTL/非法编码 | 触发代码节选 |
| #5919 | reported | 未明 | 无 |
| #5921 | reported | 未明 | 无 |
| #5922 | not_confirmed | 重复 | 无 |
| #5927 | not_confirmed | 重复 | 无 |
| #5928 | confirmed | RTL/标量扩展 | 触发代码节选 |
| #5929 | not_confirmed | 预期/无效 | 无 |
| #5930 | confirmed | RTL/FOF | 触发代码节选 |
| #5931 | confirmed | RTL/FOF | 触发代码节选 |
| #5932 | confirmed | RTL/合法内存 | 触发代码节选 |
| #5933 | confirmed | RTL/合法内存 | 触发代码节选 |
| #5934 | confirmed | RTL/合法内存 | 触发代码节选 |
| #5943 | confirmed | RTL/异常链 | 触发代码节选 |
| #5958 | reported | 未明 | 无 |
| #6015 | confirmed | RTL/访存活性 | HTML反汇编+ELF |
| #6022 | confirmed | RTL/重复根因 | 映射#6015 |
| #6034 | not_confirmed | 维护者否认 | 无 |
| #6035 | reported | 未明 | 无 |
| #6036 | not_confirmed | 预期/无效 | 无 |
| #6037 | not_confirmed | 预期/无效 | 无 |
| #6039 | reported | 未明 | （本项目已复现，见验证报告.md） |
| #6042 | reported | 未明 | 无 |
| #6063 | not_confirmed | 格式问题 | 无 |
| #6064 | reported | 未明 | 无 |
| #6065 | reported | 未明 | 无 |
| #6066 | not_confirmed | 预期/无效 | 无 |
| #6079 | reported | 未明 | 无 |
| #6085 | reported | 未明 | 无 |
| #6093 | not_confirmed | 预期/无效 | 无 |
| #6151 | not_confirmed | 预期/无效 | 无 |
| #6152 | reported | 未明 | 无 |
| #6168 | confirmed | RTL/调试触发器 | 静态RTL分析 |
| #6262 | reported | 未明 | 无 |
| #6289 | reported | 未明 | 无 |
| #6292 | reported | 未明 | 无 |
| #6293 | reported | 未明 | 无 |
| #6295 | reported | 未明 | 无 |
| #6296 | reported | 未明 | 无 |
| #6298 | not_confirmed | 维护者否认 | 无 |
| #6302 | reported | 未明 | 无 |
| #6399 | confirmed | RTL/异常链 | 触发代码节选 |
| #6407 | not_confirmed | 预期/无效 | 无 |
| #6410 | not_confirmed | 预期/无效 | 无 |
| #6467 | confirmed | RTL/流水队列 | 指令+附件ELF/波形 |
| #6475 | reported | 未明 | 无 |
| #6482 | confirmed | RTL/异常链 | 指令列表+98个ELF |
| #6486 | reported | 未明 | 无 |
| #6536 | reported | 未明 | 无 |
| #6540 | confirmed | RTL/异常链 | 触发代码节选 |
| #6543 | reported | 未明 | 无 |
| #6544 | reported | 未明 | 无 |
| #6545 | reported | 未明 | 无 |
| #6555 | not_confirmed | 报告者撤回 | 无 |
| #6561 | confirmed | RTL/配置CSR | 触发代码节选 |
| #6576 | partial | RTL/分支线索 | 日志+汇编+命令 |

## 二、逐条 PoC 与触发上下文

以下 31 条有实际材料。"触发上下文"一列是从 PoC 代码中拆出的初始状态要素，即为了命中该 bug 需要构造出来的 ISA 上下文，供第三部分归纳与后续生成器设计引用。

### 配置 CSR（#5739、#6561）

**#5739 `csrr vl` reads stale zero immediately after `vsetvli`**（fixed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5739)）

```asm
li t6, 0x600
csrs mstatus, t6
li a0, 16
vsetvli t1, a0, e8, m1, ta, ma
csrr t2, vl
```

- 触发上下文：mstatus.VS 置位；avl=16、e8/m1/ta/ma；**vsetvli 与 csrr vl 时序紧邻**。
- 期望 t1=t2=16；原始故障 t2=0（VL 写透时序）。修复 PR #5743。

**#6561 Incorrect `mstatus.VS` Dirty update for `vl=0` vector memory instructions**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6561)）

```asm
main:
  csrwi vcsr, 4
  csrwi vstart, 0
  vsetivli zero, 0, e64, m1, tu, ma

  fmv.x.d s7, fa0
  csrrw t2, sstatus, s7
  vsseg4e32.v v13, (t6), v0.t
```

- 触发上下文：vstart=0、**vl=0**；fa0 初值 0xffffffffbf361d42 经 fmv+csrrw 精确写入 sstatus，使 **VS=Clean**；masked segment store。
- 期望：vl=0 时 VS 不应变 Dirty；原始故障 VS 被错误置 Dirty。修复 PR #6570。

### mask-tail（#5765）

**#5765 Difftest mismatch on tail bits of v0 after `vlm.v`**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5765)）

```asm
li a0, 16
vsetvli t0, a0, e8, m1, tu, mu
vmv.v.i v0, 0

li a0, 10
vsetvli t0, a0, e8, m1, tu, mu
la a1, mask_data
vlm.v v0, (a1)
la a2, out_data
vsm.v v0, (a2)
```

- 触发上下文：**两次 vsetvli**（先 16 后 10，tu/mu）；v0 先整寄存器清零哨兵；.data 段 mask_data = `0x80, 0x03`；vlm 读回后逐字节比较**全部位含 tail 位**（vl=10 时高 6 位是 tail）。

### FOF（#5766、#5767、#5930、#5931）

**#5766 `vle8ff` 后立即 `csrr vl` 返回 0**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5766)）

```asm
li a0, 8
vsetvli t3, a0, e8, m1, tu, mu
vmv.v.i v8, 0

la a1, deny_start
addi a1, a1, -7

vle8ff.v v8, (a1)
csrr t4, vl
la t0, observed_vl
sw t4, 0(t0)
```

- 触发上下文：avl=8；v8 清零；**PMP deny 区边界 + 地址偏移 -7**，使前 7 字节合法、第 8 字节 fault（fault 元素序号=8 由偏移量控制）；FOF 与 csrr vl 紧邻。
- 期望 vl=7；原始故障 vl=0。

**#5767 `vlseg2e8ff.v` 后元素 fault 触发内部 critical error**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5767)）

```asm
li a0, 8
vsetvli t3, a0, e8, m1, tu, mu
vmv.v.i v16, 0
vmv.v.i v17, 0

la a2, deny_start
addi a2, a2, -12

vlseg2e8ff.v v16, (a2)
csrr t4, vl
```

- 触发上下文：nf=2（v16/v17 两组目的寄存器清零）；偏移 -12 使 fault 落在**后续 field/元素**而非首元素；PMP deny 区。
- 期望按 FOF 语义截断；原始故障触发 XiangShan 内部 critical error。

**#5930 `vle8ff.v` corrupts active loaded byte value**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5930)）

```asm
li x8, 2415919058
vle8ff.v v14, (x8), v0.t
```

- 触发上下文：魔数地址 2415919058（0x90001012 附近，PMA 边界族）；**v0.t masked FOF**。节选仅触发指令，前置配置见原帖。

**#5931 `vlseg2e32ff.v` misaligned FOF segment load field0 数据错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5931)）

```asm
li x12, 2415919058
vlseg2e32ff.v v20, (x12)
```

- 触发上下文：同一魔数地址族；EEW=32 与 nf=2 的**地址未对齐**组合。

### 非法编码（#5768、#5772、#5809、#5865）

**#5768 FP move/merge 缺 frm 保留值检查**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5768)）——无可执行 PoC，仅 RTL 译码条件：

```scala
(decodedInst.needFrm.vectorNeedFrm || FuType.isVectorNeedFrm(decodedInst.fuType)) && io.fromCSR.illegalInst.frm
```

- 触发上下文（推导）：**frm CSR 写入保留值（5..7）后执行任意 vectorNeedFrm 指令**，应 illegal 而未 illegal。

**#5772 `vmv4r.v` misaligned registers 不抛 illegal**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5772)）——附件含完整汇编 `vmv4r_illInstr.S`，核心：

```asm
vmv4r.v v12, v22
```

- 触发上下文：编码字段本身（EMUL 分数配置下寄存器组未对齐的 vd/vs2 组合）；预期 mcause=2。

**#5809 vill=1 后 `vmv.x.s` 仍执行**（fixed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5809)）

```asm
vsetvli x21, x21, 992
csrr x23, vl
csrr x22, vtype
vmv.x.s x21, v16
```

- 触发上下文：vsetvli 的 vtype 立即数 992（0x3e0）为**保留编码 → vill=1**；随后任意向量指令应 illegal（mcause=2、mtval=指令编码 0x43002ad7）；原始故障提交了 x21 写回。
- 与本项目 poc/case-086 用 `.4byte 0x40037057` 建立 VILL 是同一手法。

**#5865 reserved masked `vmerge.vvm` vd=v0 不抛 illegal**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5865)）

```asm
vsetvli x8, x0, e16, m4
vmv.v.i v4, 1
vmv.v.i v24, 0
vmv.v.i v0, -1
vmerge.vvm v0, v24, v4, v0
```

- 触发上下文：e16/m4；**三组向量寄存器哨兵**（v4=1、v24=0、v0=全1）；编码上 vd=v0 且 vm=1（reserved 组合）应 illegal。

### 数据/标量扩展（#5829、#5830、#5840、#5928）

**#5829 `vmv.x.s` SEW<XLEN 不符号扩展**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5829)）

```asm
vsetivli x0, 2, e64, m1, ta, ma
vmv.v.i  v9, 0

vsetivli x0, 1, e32, m1, tu, mu
la       x10, data_word
vle32.v  v9, (x10)
vmv.x.s  x15, v9

li       x16, 0xffffffffe01d7b92
li       gp, 1
beq      x15, x16, exit
li       gp, 2
```

- 触发上下文：**两次 vsetivli 制造 SEW 错配**（先 e64 清零 v9，再 e32）；data_word=0xe01d7b92（最高位为 1，专为符号扩展）；比较期 gp 编号 + beq 分支做 pass/fail 上报。

**#5830 `vfmv.f.s` 不 NaN-box**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5830)）

```asm
user_code:
    vsetivli x0, 2, e64, m1, ta, ma
    vmv.v.i  v21, 0
    vsetivli x0, 1, e32, m1, tu, mu
    la       x10, data_word
    vle32.v  v21, (x10)
    vfmv.f.s f23, v21
    fmv.x.d  x15, f23
    li       x16, -1
    slli     x16, x16, 32
    li       x17, 0x55555555
    or       x16, x16, x17       # expected 0xffffffff55555555
    li       gp, 1
    beq      x15, x16, exit
```

- 触发上下文：同 #5829 布局；data_word=0x55555555；期望 f23 高 32 位为全 1（NaN-box）；经 fmv.x.d 读出到标量比较。

**#5840 `vzext.vf8` active destination 元素算错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5840)）

```asm
    j       user_code
user_code:
    li x9, 0xa04f
    vsetivli x8, 1, e16, mf4
    vmv.s.x v28, x9
    vsetivli x8, 27, e64, m1
    vzext.vf8 v14, v28
    j exit
exit:
    li      t0, 1
    la      t1, tohost
    sd      t0, 0(t1)
1:
    j       1b
```

- 触发上下文：**窄 SEW+分数 LMUL（e16/mf4）写入 v28 单元素，再切 e64/m1 vl=27 做 vzext.vf8**；退出走 tohost 写（riscv-tests 风格）。

**#5928 `vsext` 源元素选择错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5928)）

```asm
vsetivli x0, 4, e32, m1, ta, ma
...
vsext.vf4 v21, v16
```

- 触发上下文：e32/m1/vl=4；源 v16 每元素不同哨兵（见原帖）；vzext/vsext 源-目的元素索引错位。

### 合法内存（#5831、#5832、#5932、#5933、#5934）

**#5831 `vlse32.v` SEW=64/LMUL=8 混合 EEW 数据错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5831)）

```asm
vsetvli x8, x0, e64, m8
li x9, 2415919032
li x13, 4
vlse32.v v24, (x9), x13
```

- 触发上下文：SEW=64/LMUL=8；base=魔数 2415919032；stride=4（x13）；EEW=32 与 SEW=64 错配的 strided load。

**#5832 `vl8re64.v` 整寄存器组 load 高 64 位截断**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5832)）

```asm
vsetivli x8, 10, e8, m8
li x10, 2415919032
vl8re64.v v8, (x10)
```

- 触发上下文：NF=8 整寄存器组 load，目的组 v8..v15；LMUL=8；魔数 base。

**#5932 `vluxseg5ei32.v` indexed segment 目的数据错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5932)）

```asm
li x11, 0x8fffffde
vluxseg5ei32.v v18, (x11), v14
```

- 触发上下文：NF=5 indexed segment；base=0x8fffffde（未对齐）；索引向量 v14 内容见原帖（每 lane 唯一偏移）。

**#5933 零 stride segment load 数据错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5933)）

```asm
li      x9, 0x8fffffb8
li      x10, 0x3803444b2551a2ae
sd      x10, 16(x9)
li      x10, 0x1000
sd      x10, 24(x9)

# ... original intervening instructions omitted ...

li      x8, 0x8fffffcd
vlsseg3e64.v v18, (x8), x19
```

- 触发上下文：**先 li+sd 在魔数地址造内存数据**；base=0x8fffffcd（未对齐，跨已造数据）；x19=0（**零 stride**）；NF=3；SEW=64/LMUL=1。

**#5934 masked segment load 目的 lane 数据错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5934)）

```asm
li x9, 0x8fffffca
vlseg2e16.v v13, (x9), v0.t
```

- 触发上下文：base 未对齐；masked（v0.t）；NF=2；逐 field 比较 active lane。

### 异常链/故障地址（#5943、#6399、#6482、#6540）

**#5943 faulting `vsse16.v` 的 mtval 错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/5943)）

```asm
vsse16.v v20, (s3), t4
```

- 触发上下文：s3 指向 fault 地址；观察第一次异常的 mtval 是否为故障元素地址（节选仅触发指令，完整前序见原帖）。

**#6399 向量 store fault 后标量 store 的 mtval 残留**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6399)）

```asm
vsetivli x0, 4, e32, m1, ta, ma
vsse32.v v11, (t4), s1
li a5, 0x0000020000000000
li t2, 0x917af882bf50788e
srl t6, t2, a5
sb sp, -1918(t6)
```

- 触发上下文：**两条 store 依次 fault**——先向量 strided store 触发 access fault，handler 恢复后，标量 `srl` 算出一个大偏移地址再触发 `sb` fault；断言第二次 mtval 为本次地址而非残留。
- 关键：需要 trap handler + mret 推进，上下文是"第一次异常后的 CSR 残留"。

**#6482 连续同方向 RVV 访存 fault 后 mtval stale**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6482)）

```asm
vle8.v   vlse8.v   vluxei8.v   vloxei8.v   vle8ff.v   vl1re8.v   vlm.v
```

- 触发上下文：同一程序内**连续多条 e8 族 load 依次 fault**（同方向），第二次以后的 mtval 不更新；附件 98 个 ELF。

**#6540 S-mode 下向量页 fault 后标量页 fault 的 stval 错**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6540)）

```asm
80002688: ... (setup)
800026d8: vse32.v  v26,(t1)     ; t1 = 0x10020 (VA of symbol d_0_0) -> STORE page-faults here
...
800026f4: addi     t3,t3,2      ; t3 = 0x60112
800026f6: fsd      fs10,-24(t3) ; scalar STORE, target = t3-24 = 0x600fa -> STORE page-faults here
```

- 触发上下文：**S-mode + 页表布局**使 0x10020 与 0x600fa 两个 VA 不可写；向量页 fault → 恢复 → 标量页 fault；断言 stval。

### 访存活性（#6015、#6022）

**#6015 未映射物理地址上的 indexed load 挂死**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6015)）

```asm
80001234:  fcvt.d.l    fa7, a7
80001238:  sha256sum0  s7, a7
8000123c:  aes64ds     sp, s6, s7
80001240:  vluxei32.v  v25, (a1), v17
80001244:  aes64ks2    s4, s4, a4
```

- 触发上下文：a1=0x4ff0b1eb，VL=4、SEW=32、LMUL=1，**各索引地址均落入未映射物理区域**；oracle 是"15000 周期无提交"的活性检查；附件为 ELF（fuzz 产物）。
- **#6022**（confirmed）为同一根因的 `vlse64.v` 映射，修复同 PR #6020。

### 流水队列/压力序列（#6467）

**#6467 StoreQueue `deqPtr > rdataPtr` 断言失败**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6467)）

```asm
vse16.v v10, (t1)
```

- 触发上下文：故障指令本身平凡（t1=0x80060050）；**上下文是前置大量跨 cache line 的 store 压力**（Sbuffer L1 miss eviction + 队列 wrap），完整前序见附件 ELF/源码/波形。oracle 为 RTL 内部不变量断言。
- 属于微体系结构状态类上下文，ISA 级单指令模板无法表达。

### 调试触发器（#6168）

**#6168 FOF 非首元素 fault 时 watchpoint trigger 丢失**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6168)）——无可执行 PoC，静态 RTL 证据：

```scala
when(!entry.fof || vstart === 0.U){
  entry.vstart       := vstart
  entry.exceptionVec := selExceptionVec
  entry.uop.trigger  := selPort.trigger   // trigger only saved here
  entry.vaddr        := vaddr
  ...
}.otherwise{
  entry.vl           := Mux(entry.vl < vstart, entry.vl, vstart)  // trigger lost
}
```

- 触发上下文（推导）：**debug 触发器 CSR（watchpoint）+ FOF 且 vstart!=0 的后元素 fault** 组合；需要独立 debug oracle。

### 性能（#4190）

**#4190 向量指令不能双发射（假依赖）**（confirmed，[issue](https://github.com/OpenXiangShan/XiangShan/issues/4190)）

```asm
vsetvli t0, x0, e32, m2, ta, ma
        li a0, LOOP
        csrr a1, cycle
1:
.rept UNROLL
vadd.vv v8,v16,v24
vadd.vv v10,v18,v26
vadd.vv v12,v20,v28
vadd.vv v14,v22,v30
.endr
        addi a0, a0, -1
        bnez a0, 1b
        fence.i
        csrr a0, cycle
        sub a0, a0, a1
```

- 触发上下文：LMUL=2、四条互不依赖的 vadd（vd=v8/v10/v12/v14 故意跳开）；oracle 是 **cycle 计数**而非功能差分。原始测得 LMUL2 3136 cycles vs LMUL1 4244。

### 历史混合（#2890）

**#2890 长时间运行的向量程序仿真挂死**（partial，[issue](https://github.com/OpenXiangShan/XiangShan/issues/2890)）——真实 C workload：

```asm
// ascii_to_utf16 循环体
1:
	vsetvli t0, a2, e8, m1, ta, ma
	vle8.v v0, (a1)
	vsetvli x0, x0, e16, m2, ta, ma
	vzext.vf2 v8, v0
	vse16.v v8, (a0)
	add a1, a1, t0
	sub a2, a2, t0
	slli t0, t0, 1
	add a0, a0, t0
	bnez a2, 1b
	ret
```

- 触发上下文：am-klib C 程序 + 循环跨多次 vsetvli 的真实负载；根因混合（RTL 修复 PR3140 + 环境配置问题）。

### 访存异常/分支线索（#6576）

**#6576 `vlse32.v` load access fault 不写 mtval**（partial，[issue](https://github.com/OpenXiangShan/XiangShan/issues/6576)）——原始材料含日志、汇编与复现命令：

```asm
        li      t0, MSTATUS_VS
        csrs    mstatus, t0             # enable the vector unit
        li      t0, -1
        csrw    pmpaddr0, t0            # pmp0: NAPOT over the whole address space,
        li      t0, 0x1c
        csrw    pmpcfg0, t0             #   X only -> in U-mode fetch is allowed, loads/stores fault
        la      s2, target
        li      t4, 4
        li      t0, MSTATUS_MPP
        csrc    mstatus, t0             # MPP = U
        la      t0, umode
        csrw    mepc, t0
        mret
umode:
        vsetivli t0, 4, e32, m1, tu, mu
        vlse32.v v3, (s2), t4           # load access fault (5); mtval must be s2
```

```
[31] exception pc 000000008000016c inst 0bd96187 cause 0000000000000005 <--
  mtval different at pc = ..., right = 0x0000000080002000, wrong = 0xffffffffffffffff
```

- 触发上下文：**PMP NAPOT 全地址空间 + pmpcfg0=X-only**（U 模式取指放行、load/store fault）构造精确的权限地图；MPP=U 经 mret 降权执行；stride=4 strided load 触发 cause=5；断言 mtval=s2。
- 这是"用 PMP 把 fault 注入到指定地址"的最完整样例。

## 三、issue 中使用的固定模版

89 条 issue 的作者实际上只用四种固定模版（外加一套验证方法）来构造 ISA 上下文。以下骨架均提取自 GitHub 缓存中的原始程序（`/tmp/vext-ppt-research-20260917/github-cache`）。

### 模版 1：KnightGOKU 手写最小复现骨架（#5739/#5765/#5766/#5767/#5809/#5865/#5928~#5934 等）

以 #5766 完整程序为样本（早期 #5739 是其简化版：pass/bug 自旋代替 ebreak+落盘）：

```asm
.section .text.init
.globl _start
_start:
  la t0, trap_handler
  csrw mtvec, t0              # ① 装 trap handler
  li t6, 0x600
  csrs mstatus, t6            # ② 只开 mstatus.VS
  la t0, deny_start           # ③ PMP deny 区：两个 pmpaddr 用 TOR 划界，
  srli t0, t0, 2              #    pmpcfg0=0x8800（entry1: A=TOR, L=1，
  csrw pmpaddr0, t0           #    无 R/W/X——L 位使 M 模式也受约束）
  la t1, deny_end
  srli t1, t1, 2
  csrw pmpaddr1, t1
  li t2, 0x8800
  csrw pmpcfg0, t2
  li a0, 8                    # ④ 向量配置 + 哨兵
  vsetvli t3, a0, e8, m1, tu, mu
  vmv.v.i v8, 0
  la a1, deny_start           # ⑤ 目标指令 + 观察点
  addi a1, a1, -7             #    偏移量控制 fault 落在第几个元素
  vle8ff.v v8, (a1)
  csrr t4, vl
  la t0, observed_vl          # ⑥ 观察值落盘到内存
  sw t4, 0(t0)
pass:
  li gp, 1
  ebreak                      # ⑦ 正常出口 = ebreak 进 handler
trap_handler:
  csrr t0, mcause
  li t1, 3
  bne t0, t1, unexpected_trap # 只接受 breakpoint(3)，其余视为意外
  la t2, result_code
  sw gp, 0(t2)                # gp 写入 result_code 作为结论
  la t3, done
  csrw mepc, t3
  mret
unexpected_trap:
  ...                         # 写 0xdead 到 result_code 后同样 mret 到 done
done:
  fence
1:  j 1b
.section .data
.align 3
result_code: .word 0          # 结论落盘：1=pass, 0xdead=意外 trap
observed_vl:  .word 0         # 观察值落盘
pre_deny:     .byte 0x10, 0x11, ...   # deny 边界前的合法数据
deny_start:   .byte 0xde, 0xad, ...   # deny 区（魔数可查证是否被读过）
deny_end:
```

要点：程序在 M 模式跑完，靠 PMP 的 **L 位** 让 M 模式也 fault；`ebreak` 被复用为"正常结束"信号，handler 里用 mcause==3 区分正常结束与意外异常。

### 模版 2：jimmymtest 的 gp 自校验 + tohost + 通用跳过 handler 骨架（#5829~#5840）

以 #5829 完整程序为样本：

```asm
.section .text
.globl _start
_start:
    la      t0, trap_handler
    csrw    mtvec, t0
    csrr    t0, mstatus
    li      t1, 0x00003600    # ② FS+VS 同时置 Dirty（比模版1多开 FS）
    or      t0, t0, t1
    csrw    mstatus, t0
    csrw    fcsr, x0          # ③ 清 fcsr
    j       user_code
user_code:                    # ④ 哨兵 + 两次 vsetivli 错配 + 目标指令
    vsetivli x0, 2, e64, m1, ta, ma
    vmv.v.i  v9, 0
    vsetivli x0, 1, e32, m1, tu, mu
    la       x10, data_word
    vle32.v  v9, (x10)
    vmv.x.s  x15, v9
    li       x16, 0xffffffffe01d7b92   # ⑤ 自校验：期望值 + gp 编号
    li       gp, 1
    beq      x15, x16, exit
    li       gp, 2
exit:
    la      t1, tohost
    sd      gp, 0(t1)         # ⑥ tohost 退出（riscv-tests 机制）
    li      t0, 0
    .insn   i 0x6b, 0, x0, t0, 0   # ⑦ DiffTest GOODTRAP 自陷
1:  j 1b
trap_handler:                 # ⑧ 通用"跳过故障指令"handler：
    csrr    t0, mepc          #    读 mepc/mcause/mtval，按 mcause 分类，
    csrr    t1, mcause        #    译码故障指令是 16 还是 32 位，
    csrr    t4, mtval         #    mepc += 长度，清 mcause/mtval 后 mret
    ...                       #    （支持压缩指令的程序无需norvc）
    .section .tohost,"aw",@progbits
tohost:   .dword 0
fromhost: .dword 0
    .section .data
data_word: .word 0xe01d7b92   # 内存哨兵（符号位=1）
```

要点：gp 编号 + tohost 是 riscv-tests 血统；GOODTRAP 自陷让 DiffTest 干净收尾；handler 是通用的（按 mcause 译码长度跳过），为异常链类用例预留了续行能力。

### 模版 3：riscv-tests 官方 env-p 框架（#6576）

原帖自述 "a plain riscv-tests env-p program: standard `RVTEST_CODE_BEGIN` reset sequence"。标准复位序列之后，手工追加特权级/权限构造（完整代码见第二部分 #6576 条目）：

```asm
        li      t0, MSTATUS_VS
        csrs    mstatus, t0
        li      t0, -1
        csrw    pmpaddr0, t0      # NAPOT 覆盖全地址空间
        li      t0, 0x1c
        csrw    pmpcfg0, t0       # X-only：U 模式取指放行、load/store fault
        la      s2, target
        li      t4, 4
        li      t0, MSTATUS_MPP
        csrc    mstatus, t0       # MPP = U
        la      t0, umode
        csrw    mepc, t0
        mret                     # 降权到 U 模式执行 payload
umode:
        vsetivli t0, 4, e32, m1, tu, mu
        vlse32.v v3, (s2), t4    # U 模式下触发 load access fault
```

要点：直接复用官方框架的复位/退出/宏体系，只插入权限构造段；**pmpcfg 的编码在这里被用来做权限地图**（X-only 让程序还能跑、访存必 fault）。

### 模版 4：fuzzer 生成器的运行时骨架（zhangkanqi #5769/#5770/#5772、lhb-sec 全部、wndmll643 #6540）

#5772 附件 `vmv4r_illInstr.S` 是完整样本（程序结构为生成器固定运行时 + 随机指令流）：

```asm
_start:
trap_vec_init:
  la x13, other_exp
  csrw 0x305, x13            # ① mtvec → 通用跳过 handler
  la x13, other_exp_s
  csrw 0x105, x13            # ② stvec → S 态跳过 handler
mepc_setup:
  la x13, init
  csrw 0x341, x13            # ③ mepc 指向 init
init_env:
  li x26, 0x00000069001d6aa8
  csrw 0x300, x26            # ④ 整字写 MSTATUS（含模式位/中断位）
  li x16, 0x2fffffff
  csrw 0x3b0, x16            # ⑤ pmpaddr0/pmpcfg0=0xf 全开
  li x16, 0xf
  csrw 0x3a0, x16
  sfence.vma x0, x0
  li x26, 0x0
  csrw 0x304, x26            # mie=0
  mret                       # ⑥ 切到目标模式进 init
init:
  fsrmi 2                    # ⑦ frm
  li x0, 0xdb7d548a56e8beda  # ⑧ 全量魔数哨兵：
  fmv.h.x f0, x0             #    li + fmv.h/w/d.x 三种宽度交错
  li x1, 0x492bf97bfac3d9cc  #    装载 f0..f31（x0..x15 同法）
  fmv.w.x f1, x1
  ...                        #    （标量寄存器由随机指令流自然写脏）
  la t6, mem_region          # ⑨ 预留内存区
  j main
other_exp:                   # ⑩ 通用 handler：mepc+=4 直接跳过
  csrr x13, 0x341
  addi x13, x13, 4
  csrw 0x341, x13
  mret
main:
  li x27, 0x600
  csrrs x0, mstatus, x27     # 开 VS
  vsetivli s3, 25, e8, m1, ta, ma
  ...                        # ⑪ 随机混合指令流（含 vsm4r/vghsh/vaesem 等），
  vmv4r.v v12, v22           #    目标指令夹在中间
  ...
```

lhb-sec 系列（#6399/#6482/#6561 等）是同一血统再加一道工序：**seed.elf → DiffTest 报错 → t_min 最小化** 后报 issue；#6561 正文里的 `csrwi vcsr` / `csrwi vstart` / `csrrw sstatus` 即生成器 CSR 指令池的一部分。

### 方法模版：验证三件套

四个模版的作者共用同一套验证方法（issue 的 To Reproduce 段）：

1. **Spike（或 NEMU）独立跑**得到参考行为；
2. **XiangShan `--diff`** 跑同一 ELF，DiffTest 报出 `right=REF / wrong=XS` 的分歧点（pc + 寄存器/CSR）；
3. **XiangShan `--no-diff`** 复跑，区分"真 RTL 行为差异"与"差分器/参考模型问题"（#5766 靠这一步发现内部 assertion；#5426/#5279 反向证明问题在 NEMU/DiffTest）。

### 模版承载的上下文构造能力对比

| 上下文段 | 模版1 KnightGOKU | 模版2 jimmymtest | 模版3 env-p | 模版4 fuzzer |
|---|---|---|---|---|
| 标量哨兵 | 按需 li | 按需 li | riscv-tests 宏 | li 全量魔数（x0..x15 显式） |
| 浮点哨兵 | — | fcsr=0 | — | li + fmv.h/w/d.x 全量 f0..f31 |
| 向量 CSR | vsetvli + 观察 | vsetivli×2 错配 | vsetivli | vsetivli / csrwi vstart/vcsr |
| mstatus/sstatus | csrs 0x600（只 VS） | 0x3600（FS+VS） | csrs MSTATUS_VS | 整字 csrw（含模式）/csrrw 精确值（#6561） |
| PMP | TOR+L deny 区 | — | NAPOT X-only 权限地图 | 全开 |
| 特权级 | M | M | M→U（mret） | M→S/U（mret） |
| trap handler | ebreak 出口专用 | 通用跳过（16/32 位长度译码） | env-p 标准 | 通用跳过（mepc+=4） |
| 结果上报 | result_code 落盘 + ebreak | gp 编号 + tohost + GOODTRAP | env-p 机制 | 自旋（靠 DiffTest 分歧点） |
| 内存哨兵 | .data 魔数 + deny 边界 | .data 魔数 | 符号地址（target） | mem_region 预留区 |
| 指令形态 | 手写最小序列 + 观察点 | 手写序列 + 自校验 | 手写序列 | 随机长指令流（目标夹在其中） |

### 固定模版之外的方式

以上模版覆盖不了的，issue 里出现的其它手段：

- **真实 workload**（#2890）：am-klib C 程序编译，跨多次 vsetvli 的循环负载——上下文由真实程序自然产生，无模版；
- **静态 RTL 分析**（#5768/#6168/LeeHaofeng 系列 #6064/#6065）：不构造执行上下文，直接读 Scala/Chisel 源码找译码条件、Mux 笔误，PoC 只是"RTL 条件引用"；
- **维护者内部复现**（#5943）：issue 只给现象和指令，复现程序在维护者手里；
- **fuzz 本身对模版 1/2/3 作者而言是"另一条路线"**：模版 4 的运行时骨架固定，但指令流、CSR 指令池、寄存器哨兵全部随机——"固定模版构造上下文"与"随机生成上下文"在 lhb-sec/zhangkanqi 两批 issue 里实际是同一条管线的两层。

### 固定模版内的上下文构造机制（8 个）

四个模版能命中各自的 bug，靠的是模版里反复出现的上下文构造段。把这些段拆开，是跨模版通用的 8 个机制——也是想复刻这些触发条件时的配方清单：

#### 机制 1：前导指令自构造（prologue self-setup）

上下文不由外部装载，而由被测指令前的一小段指令**在执行中建立**：

- `vsetvli/vsetivli` 配置向量状态——所有 PoC 共有；进阶用法是**两次配置制造错配**（#5829/#5830 先 e64 后 e32、#5840 先 e16/mf4 后 e64/m1）；
- `vmv.v.i / vmv.s.x` 给向量寄存器铺哨兵（#5765 v0 清零、#5865 三组不同哨兵 1/0/-1）——**向量寄存器内容本身是触发条件**（tail 位保留、masked lane 检查都依赖"旧值可分辨"）；
- `li + sd` 在魔数地址现造内存数据（#5933），让 load 读到已知模式。

对生成器的含义：pre-state 不必全部来自外部装载，可以生成一小段**可复用的前导指令序列**来塑造向量寄存器/内存，这与 isla 执行"目标指令"前先跑 setup 序列的管线天然兼容。

#### 机制 2：CSR 定向写（把 CSR 当一等输入）

手写模版 1/2 对 CSR 只做"开 VS"这一件事；而命中 CSR 相关 bug 的用例都把 CSR 当精确输入：

- **vstart != 0**：#6561 的判定条件直接围绕 vstart=0 与 !=0 两个分支（本项目 difftest 80 条 vmerge 失败也正是落在 vstart!=0 语义分歧上）；
- **VS/FS 初值精确到 Clean**：#6561 用 `fmv.x.d s7, fa0` + `csrrw t2, sstatus, s7` 把浮点寄存器搬运来的字样写入 sstatus——CSR 观察点（Dirty 迁移）类 bug 需要初值非默认；
- **frm 保留值 5..7**（#5768）、vcsr/vxrm/vxsat 组合（#6561 `csrwi vcsr, 4`）；
- mepc/MPP + mret 做特权级切换（#6576 U 模式、#6540 S 模式）——特权级本身是上下文维度。

#### 机制 3：内存权限地图（PMP/PMA/页表注入 fault）

模版 4 的 pmp 全开、永远不会 fault；FOF/异常链类 bug 的核心手法则是**用权限边界精确控制 fault 落点**（模版 1/3 的专职手段）：

- **PMP deny 区 + 地址偏移量控制 fault 元素序号**（#5766：`la deny_start; addi a1, a1, -7` 使 fault 恰落在第 8 个元素；#5767：-12 落在后续 field）——把"第几个元素 fault"变成一个可参数化的整数；
- **pmpcfg0=X-only NAPOT**（#6576）：U 模式取指放行、load/store fault，程序还能继续跑；
- 未映射物理地址（#6015）、I/O PMA 区（#6293）、S-mode 页表不可写页（#6540）——同一思想的页表版。

#### 机制 4：异常链与 trap handler 作为状态推进器

- 上下文是"第一次异常后的 CSR 残留"：#6399/#6482/#6540 都需要 handler 接住第一次 fault、mret 跳过故障指令、再触发第二次 fault，断言 mtval/stval 不残留；
- handler + mret 序列本身是模版的一部分，而非可选附件。FOP 后 vstart>0 的续行（#6168）同理。

#### 机制 5：指令间时序邻近性（多指令序列）

单指令 + GOODTRAP 检不出这类问题，触发条件是**特定指令对的紧邻关系**：

- `vsetvli → csrr vl`（#5739）、`vle8ff → csrr vl`（#5766）：配置/截断结果向后一条指令的写透时序；
- 混合序列 `vmsbf.m → vl1re64.v → vlseg4e8.v`（#5845）；
- 向量 fault → AMO（#6289）等跨类组合。
- 生成器含义：需要生成**指令对/短序列**并保持相邻，而不是孤立单指令。

#### 机制 6：数据与地址布局哨兵

- .data 段魔数（mask_data=0x80,0x03；data_word=0xe01d7b92/0x55555555）——符号位、NaN-box 检查都要求特定位模式；
- **base 地址故意未对齐**（#5931/#5932/#5933/#5934 的 0x8fffffde/0x8fffffcd/0x8fffffca）与 stride=0（#5933）——访存类 bug 的触发面在"地址布局 × EEW/NF/mask"的组合上；
- 期望值经 `li + beq + gp` 或 tohost 写出，形成自校验程序（#5829/#5830/#5840）。

#### 机制 7：微体系结构状态（超出 ISA 级，但可由指令序列间接建立）

- #6467 的上下文是"前置大量跨 cache line store 造成 Sbuffer 挤压 + 队列 wrap"；#6015 是索引全落未映射区的活性挂死。oracle 分别是内部断言与 commit progress，不是 ISA 差分。这类只能靠**长指令序列压力**逼近，ISA 单指令模板原理上无法表达。

#### 机制 8：生成策略层面（程序外的三种来源）

- **符号执行求解 pre-state**：让 solver 产出"能命中某类检查点"的上下文（标量、向量 CSR、向量寄存器、内存初值均可作为符号化目标），替代手工模版枚举；
- **随机 fuzz + 差分筛选**：#6015/#6467/#6482 的 ELF 附件均为 fuzzer 长序列产物——上下文由随机长程序自然累积；
- **真实 workload**：#2890 用 C 编译程序触发，适合暴露跨配置循环类问题。

四种模版与 8 个机制的关系：模版 1/2/3 是"手工挑机制组合"的最小化骨架（每种各用 3~5 个机制）；模版 4 把机制 1/2 的前导段换成随机指令流，靠 DiffTest 分歧点当 oracle。机制 7（微架构压力）四个模版都只能靠长序列间接逼近；机制 8 则完全脱离模版。

### 触发维度与出处模版对照表

| 触发维度 | PoC 例 | 出处模版 |
|---|---|---|
| 向量配置 vtype/vl | 全部 | 模版 1/2/3/4 共有 |
| 向量寄存器哨兵 | #5765/#5865/#5840/#5933 | 模版 1/2（vmv.v.i），模版 4 靠随机流 |
| vstart != 0 | #6561/#6168 | 模版 4（csrwi vstart）；模版 1/2 未用 |
| CSR 精确初值（VS=Clean、frm 保留） | #6561/#5768 | 模版 4（csrrw 整字/精确字段）；fsrmi 设 frm |
| 内存数据哨兵 | #5765/#5829/#5933 | 模版 1/2（.data 魔数 + deny 边界） |
| 地址未对齐/stride=0 | #5931~#5934 | 模版 4 随机流自然覆盖 |
| PMP deny/权限地图 | #5766/#5767/#6576 | 模版 1（TOR+L）、模版 3（NAPOT X-only） |
| 页表/S 模式 | #6540 | 模版 4（整字 MSTATUS 含模式位） |
| trap handler 异常链 | #6399/#6482/#6540 | 模版 2/4 的通用跳过 handler |
| 指令对时序邻近 | #5739/#5766/#5845 | 模版 1（观察点紧邻目标指令） |
| 微架构压力/活性 | #6467/#6015 | 无模版（fuzz 长序列 + 活性/断言 oracle） |

一句话结论：issue 侧的"固定模版"是**手工最小化骨架**（mtvec + mstatus 开 VS + 哨兵 + 目标序列 + 出口），真正的触发能力来自模版里参数化的上下文段——PMP 权限地图、CSR 定向值、内存哨兵、通用跳过 handler、观察点紧邻性；这些段在四种模版间的取舍差异，就是各作者命中不同 bug 类别的原因。

### 对本项目 difftest 管线的含义

- 本目录当前的模版重放（`poc/case-086` 一类，由 `../difftest-xiangshan/pipeline.py` 生成）覆盖的是"合法配置下单指令功能正确性"一角；对照 8 个机制，可落地的四个扩展自由度：
  1. **vstart≠0 / CSR 定向值**（机制 2）：本目录 difftest 80 条 vmerge/vmv 失败正是落在 vstart≠0 的语义分歧上（见验证报告.md），与 #6561 的判定分支同一面；
  2. **PMP 权限地图**（机制 3）：deny 区 + 偏移量把"第几个元素 fault"参数化，是 FOF/异常链类 bug 的触发前提；
  3. **异常链 handler**（机制 4）：通用跳过 handler + 第二次 fault 断言 mtval/stval；
  4. **观察点紧邻性**（机制 5）：目标指令后紧跟 csrr vl/vtype 或读回比较。
- 微架构压力类（机制 7，#6467/#6015）与真实 workload（#2890）超出指令级重放管线的能力范围，只能靠序列生成或 fuzz 补充。
- 复刻顺序建议：以上下文"配方"形式落地——把 CSR 组、PMP/数据段组、handler 组、观察点组各自参数化后组合，前两类改动最小（仍是 CSR 写入段），后两类需要扩展模版的收尾结构。
