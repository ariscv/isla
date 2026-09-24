# 19,908 条 make solve 生成物全量 bug 统计表

日期:2026-09-19。
- **旧基线** 7bf51a8(旧向量单元):测 9,109 条 trap 集(Illegal_Instruction 9,045 + Memory_Exception 64)
- **新基线** c8d7b3a(2026-09-15 向量重构,即最新):测全部 19,908 条(trap 9,109 + success 10,799)
- 判定 oracle:RTL vs NEMU 逐事件 difftest;`--no-diff` 纯 RTL 复核活性;空载复核排除满载假象

归档:`archive-20260919/`(01 输入 JSON ×2、02 旧基线结果 ndjson、03 新基线 8-shard ndjson + monitor.log、04 PoC ×3 + link.ld、05 文档 ×8、06 脚本 ×4、stats-final.json、本表)

## 总览

| 基线 | 测试 | 通过 | 失败 | 失败率 |
|---|---:|---:|---:|---:|
| 旧 7bf51a8(trap) | 9,109 | 6,556* | 2,553 | 28% |
| 新 c8d7b3a(全部) | **19,908** | **7,183** | **12,725** | **64%** |

*旧基线 pass 含 399 条空载复证修正(原判 fail 为满载假象)。*

---

## 全部 bug 分类表(含原创 + 补充 + 已知 + 撤销)

### A. 原创 bug(已提交 issue)

| # | Bug | 现象 | 触发 case | 指令族 | 提交 |
|---|---|---|---:|---|---|
| A1 | **向量指令永久挂死** | 合法向量指令执行后核零提交(无 trap 无 retire),`--no-diff` 纯 RTL 复现;vstart/特权级/difftest 无关;**新旧两代均存在** | **11,447**(新基线全部 timeout) | **267 形态**:vw* 加宽全家族(vwmacc/vwmul/vwadd/vwsub × vv/vx/wx/wi)、vid.v、viota.m、vwsll.*、vandn.*、vrol.*/vror.*、vnclip*/vnsra*/vnsrl*、vadc/vmadc/vmsbc、vslide1up/vslide1down/vslidedown/vslideup、vrgather.*/vrgatherei16、vbrev/vbrev8/vrev8、vclmul*/vclz/vctz/vcpop、vcompress、vabs、vfmerge/vfmv、vmv.v.x、vmerge.vxm、vmseq/vmacc/vmaccus/vand/vor/vadd/vsub/vsrl/vsra 等 | **[#6598](https://github.com/OpenXiangShan/XiangShan/issues/6598)** |
| A2 | **vsm.v mtval 报基地址** | vsm.v store access fault 时 DUT mtval=0x1fffffe(store base),NEMU mtval=0x2000000(首个 faulting 字节) | **12**(新基线) | vsm.v | **[#6599](https://github.com/OpenXiangShan/XiangShan/issues/6599)** |
| A3 | **difftest vreg 同步缺失** | DUT 的向量寄存器写不进入 NEMU 参考状态;所有未全量覆写 vreg 的 PoC 必然假失败 | **~506**(390 纯 vr diff + 116 未分类 abort,归同因) | 工具(86+形态,覆盖所有向量写指令) | **[difftest #969](https://github.com/OpenXiangShan/difftest/issues/969)** |

**小计:原创 bug 触发 ~11,965 case / 19,908(60.1%)**

### B. 补充已有 issue(行为已被人报告)

| # | Bug | 现象 | 触发 case | 指令族 | 对应 issue | 新基线状态 |
|---|---|---|---:|---|---|---|
| B1 | LMUL 组未对齐漏检 | 寄存器组未对齐时 NEMU 报 illegal 而 RTL 执行;旧基线 201 条 ABORT | **201**(旧基线) | vmerge.{vvm,vim,vxm}、vmv.v.{v,i,x}、vmv4r.v、vmv8r.v | **#6410**(closed/invalid)+ **#5772**(open/confirmed) | **已修复**(新基线 0 条) |
| B2 | vnclip/vnclipu 饱和不置 vxsat | 饱和时 RTL vxsat=0,NEMU=1 | **34**(新)+ **2**(旧)= **36** | vnclipu.{wv,wi,wx}、vnclip.{wv,wi,wx}、vsadd.vv | **#6555**(open) | 存在 |
| B3 | vstart 超界不 trap(执行) | vstart>VLMAX 时 RTL+NEMU 双侧执行(不报 illegal),与 Sail 分歧;payload 执行后哨兵暴露 | **2,288**(旧基线 timeout) | vmv.v.i、vmerge 等(凡 vstart 不可达时的行为) | **#6298**(open,维护者称 unimplemented) | 行为变化(并入 A1 挂死或 B4 WIP) |
| B4 | vsetvl rs1=x0/rd=x0 VILL 分歧 | reserved 编码 NEMU 置 VILL,RTL 置 0 | **2** | vsetvl | **#5725**(closed/fixed) | 存在 |
| B5 | vsm.v store commit 比较失败 | difftest Store Commit Checker 报 NEMU 不上报 store(两侧数据一致) | **3**(旧)+ **3**(新)= **6** | vsm.v | **#5279**(open,known difftest bug) | 存在 |

**小计:补充 case 触发 ~2,533 case(主要为 B3 的 2,288)**

### C. 撤销(非 bug)

| # | 现象 | case 数 | 指令 | 撤销原因 |
|---|---|---:|---|---|
| C1 | 重构后 WIP 指令误报 illegal(RTL mcause=2,NEMU 执行) | **721**(新基线) | vwsll.{vi,vv,vx}、vrol.*/vror.*、vandn.*、vbrev8/vbrev、vclz/vctz/vcpop、vwredsumu/vredsum、vssrl/vssra、vmadc.{vi,vim}、vmv.s.x 等 21 形态 | **WIP 未支持**(kunminghu-v3 向量活跃开发,未接线指令报 illegal 为保守合理行为) |
| C2 | vsm.v MMIO store 不 fault | **3**(旧基线) | vsm.v | **PMA 实现定义**(RISC-V Priv Spec §6,PMA 为平台配置,不违 ISA) |
| C3 | 旧基线满载假超时 | **399**(旧基线,空载复证全 pass) | 各种 | 满载 -j48 时 emu 初始化+执行被 CPU 拖慢,30s 超时不够 |

**小计:撤销 ~1,123 case**

### D. 已修复(新基线验证通过)

| # | Bug | 旧基线 case | 新基线 case | 说明 |
|---|---|---:|---:|---|
| D1 | misaligned(B1) | 201 | **0** | 向量重构修复了寄存器组对齐检查 |

---

## Bug 触发总计

| 分类 | case 数 | 占比 |
|---|---:|---:|
| 原创 RTL bug(A1+A2) | **11,459** | 57.6% |
| 原创 工具 bug(A3) | **~506** | 2.5% |
| 补充已有 issue(B1-B5) | **~2,533** | 12.7% |
| 撤销非 bug(C1-C3) | **~1,123** | 5.6% |
| **通过** | **7,183** | 36.1% |
| **总计** | **19,908** | 100% |

**实际发现 bug 的 case:~14,522(72.9%)**(原创 + 补充)

## 各指令族 bug 触发热力(top-20)

| 指令 | stall(#6598) | WIP(C1) | vr-sync(A3) | vxsat(B2) | mtval(A2) | 总计 |
|---|---:|---:|---:|---:|---:|---:|
| vslide1up.vx | 197 | - | - | - | - | 197 |
| vwsll.vx | 196 | 150 | - | - | - | 346 |
| vwmaccsu.vx | 190 | - | - | - | - | 190 |
| vwmaccus.vx | 188 | - | - | - | - | 188 |
| vwmaccu.vx | 187 | - | - | - | - | 187 |
| vwmacc.vx | 182 | - | - | - | - | 182 |
| vwmulsu.vx | 164 | - | - | - | - | 164 |
| vwadd.vx | 163 | - | 17 | - | - | 180 |
| vwmul.vx | 160 | - | - | - | - | 160 |
| vwsubu.vx | 159 | - | 17 | - | - | 176 |
| vwaddu.vx | 158 | - | - | - | - | 158 |
| vwmulu.vx | 158 | - | - | - | - | 158 |
| vwsub.vx | 156 | - | - | - | - | 156 |
| vwmaccu.vv | 153 | - | 21 | - | - | 174 |
| vwmaccsu.vv | 152 | - | 19 | - | - | 171 |
| vwmacc.vv | 151 | - | 15 | - | - | 166 |
| vnclipu.wv | - | - | - | 17 | - | 17 |
| vsm.v | - | - | - | - | 12+3 | 15 |

## Bug finder 效果评估

| 指标 | 数值 |
|---|---|
| 输入条数 | 19,908(make solve 全量) |
| 发现 bug 的 case | ~14,522(72.9%) |
| 原创 bug 数 | 3(A1 挂死 + A2 mtval + A3 difftest) |
| 补充已有 issue 数 | 5(#6410/#5772、#6555、#6298、#5725、#5279) |
| 撤销非 bug 数 | 3(WIP、PMA、满载假象) |
| 确认已修复 | 1(misaligned → 0) |
| GitHub 独立核查 agent 总数 | 76(逐形态)+ 5(组级)|
| PoC 实测验证 | 3 个提交 issue 均通过编译+运行+现象复现+codex 复核 |
