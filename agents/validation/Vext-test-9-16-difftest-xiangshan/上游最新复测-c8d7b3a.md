# 上游最新 kunminghu-v3(c8d7b3a)复测

日期:2026-09-19。动机:用户要求 pull 最新 commit 重新运行所有 PoC 对比变化。向量单元已在上游重构(基线 7bf51a8 → c8d7b3a 共 270 提交,其中 vector 相关 86 个、Decoder/DecodeFields 新体系 +101 文件 +14,449 行,含 `IsVstartForceZeroField`/`VRegTypesField` 等 per-pattern 检查)。

## 环境与构建

- emu:`make emu CONFIG=MinimalConfig EMU_THREADS=4 RELEASE=1 -j 64` + `NOOP_HOME=$PWD`(构建坑 2 个,见下);Commit SHA 自证 c8d7b3a5c1
- NEMU:ready-to-run submodule 同步 bump(新 RTL + 新 NEMU 配套组合)
- 旧基线 emu 已备份:`difftest-xiangshan/emu-baseline-7bf51a8`
- **新 emu 行为变化**:GOOD TRAP 输出到 stderr(旧版 stdout)——`pipeline.py run_case` 已改为 stderr 合并捕获,否则全部误判 failure
- 构建坑(附带发现,可报上游):① 不带 RELEASE 时新代码在 `Rob.scala:1489 perfDebugInfo.get` 处 elaboration 崩溃(CI 走 --release/--fpga-platform 路径未暴露);② difftest DPIC.collect 需要 NOOP_HOME 环境变量

## 【重要修正】RELEASE 构建丢失 --enable-difftest,污染首轮重跑

- **根因链**:Makefile `RELEASE=1` → `RELEASE_ARGS`(含 `--fpga-platform`、`--default-layer-specialization=disable`)但**不含 `--enable-difftest`**;默认 DEBUG 路径才有 `--enable-difftest` + layer enable。缺失导致 difftest 的**向量寄存器同步上报**被裁:RTL 侧 vr 正常变化,NEMU(无论新旧 so)永远收不到 vr 写,比较时恒为初值 pattern。
- **实证**:case-103(success 条目)加"32 个 vr 全部 vl1re8.v 写 0x55"补丁后,RTL 侧=0x5555…,NEMU 侧恒为 0xffff…(新 so)或初值 pattern(旧 so,从 ready-to-run 旧 submodule 指针 e131ac5 恢复,两版 so md5 不同、现象相同)→ 问题在 emu 构建而非 so。
- **影响面**:首轮 success 重跑(5,969/10,799,已中止)的 898 条 abort-diff 全部是该污染;smoke 中 case-1750(vnclipu)的"新数据分歧"**同样是被污染的假象**(其 NEMU 侧 right 值 0x84b8c59ed6306400 与 case-105 的 NEMU 初值完全相同),不是真 bug——待新构建复核。
- spike so 替代不可用:`tinfo` CSR 比较不兼容直接 ABORT。
- **修复**:全 clean(`make clean` + `rm -rf build out`)后以 `SIM_ARGS=--fpga-platform`(绕 Rob 崩溃)+ 默认 DEBUG 路径(自带 `--enable-difftest` + layer enable)重编;两 flag 在 ArgParser 中相互独立,该组合 = FPGAPlatform=true(跳过 debug 表崩溃)+ EnableDifftest=true(完整同步)。
- 备份:新 so `/tmp/nemu-so-new-c8d7b3a`、旧 so `/tmp/nemu-so-old-7bf51a8`。

## Smoke 结果(新基线关键 PoC 分化)

| PoC | 旧基线行为 | 新基线行为 | 判定 |
|---|---|---|---|
| case-048 vmerge.vvm misaligned | ABORT(NEMU illegal/RTL 执行) | **GOODTRAP** | **misaligned 已修**(VRegTypesField 对齐检查落地) |
| case-007 vmerge.vim misaligned | ABORT | **GOODTRAP** | **已修**(连 #6410 未实测的 vim 变体也修了) |
| case-622 vaadd.vv vstart=0x40 | (空载 GOODTRAP/满载假超时) | GOODTRAP | 正常 |
| case-1750 vnclipu.wv masked vxsat | ABORT(vxsat NEMU=1/RTL=0) | **仍 ABORT,但差异字段变为 v31 数据低位**(right=0x...0004 vs wrong=0x...6479) | vxsat 修复,但暴露**新的计算结果分歧**(SEW=16 narrowing clip 数据) |
| case-4859 vrev8.v vstart=2^63 | 挂死(--no-diff) | **仍 TIMEOUT(--no-diff 与 --diff 双确认)** | **挂死未修** |
| case-3802 vid.v vstart=2^63 | 挂死(--no-diff) | **仍 TIMEOUT** | **挂死未修** |

初步结论:静态推断"上游 isVstartForceZero 覆盖即可封死挂死"**被实测推翻**——vstart=2^63 时 vrev8.v/vid.v 依然挂死(说明译码检查之外仍有路径落入挂死状态,或巨大 vstart 在检查生效前已破坏流水线);misaligned 族已修;vnclipu 出现新数据分歧待全量定规模。

## 全量重跑(19,908 条,已完成 2026-09-19)

- 执行:8 shard × 4 jobs = 32 emu 并行(-j64 上限内),timeout 60s(满载实测 GOODTRAP 需 12s,30s 会假超时),分片脚本 `rerun_shard.py`,结果 `work/rerun-c8d7b3a/shards/*.ndjson`(逐条落盘、按 id 去重)
- 最终分类(19,908):trap 集 success 4,199 / timeout 4,123 / 真实 ABORT 538 / vr 污染 249;success 集 success 2,984 / timeout 7,262 / 真实 ABORT 349 / vr 污染 141(另 22 条 emu 崩溃)
- 旧→新对比:**修复** = misaligned 族(旧 201 ABORT→新 GOODTRAP,含 #6410 未实测的 vim/vxm 变体);**回归** = ①合法指令误报 illegal(~887)②vw* 加宽挂死(~1,150)③vnclip 族数据错(升级)④vstart=2^63 挂死仍存(旧发现延续,已验证);**工具污染** = vr 同步回归(390)
- 逐条原创性核查与组级复核:见 `新基线回归-逐条核查.md`(76/76 形态全原创;5 组;最终 5 新开 issue + 3 追加 + 1 待定)
