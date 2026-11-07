# P1b 变异体的实际守卫类（2026-11-07）

**核心结论：5000 个变异体中，2640 个（52.80%）留在父类，2360 个（47.20%）跳到其他类，存在相当比例的跳类；不能把父种子类号当作变异体的实际类号。**

本批恰好一条路径接纳 5000/5000，未接纳 0，新类 0。变异体命中既有 2033/2836 个类（71.69%），803 个类从未被本批变异体命中。14 个原有硬件分歧全部得到实际类号；新 judge 与旧 J2/J1 的不一致样本为 0。

## 对后续工作的意义

按守卫类统计或调度时，应在变异后取得实际类，父类只能作为来源记录。下表可直接比较三个算子的留类和跳类比例。本轮没有测量 Rust 变异器的吞吐，因此这些数字能说明类号更新的必要性，不能单独说明改写 Rust 的性能收益。

## 算子与场景统计

每行留类、跳类比例的分母是该行变异体总数；命中率的分母是该场景全部种子类数。跨场景合计使用 2836 类。命中只统计这 5000 个变异体，不把作为映射基准的种子计入。类身份是“场景、路径号、类号”三者，类号从 0 起且只在同一路径内有效。

| 场景 / 算子 | 变异体 | 留父类 | 跳其他类 | 未接纳 / 新类 | 命中类 / 总类 | 从未命中类 | 类命中率 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 全部 | 5000 | 2640（52.80%） | 2360（47.20%） | 0 / 0 | 2033/2836 | 803 | 71.69% |
| M1 | 1644 | 214（13.02%） | 1430（86.98%） | 0 / 0 | 488/2836 | 2348 | 17.21% |
| M2 | 1369 | 876（63.99%） | 493（36.01%） | 0 / 0 | 911/2836 | 1925 | 32.12% |
| M5 | 1987 | 1550（78.01%） | 437（21.99%） | 0 / 0 | 1508/2836 | 1328 | 53.17% |
| sv39-load | 2000 | 1095（54.75%） | 905（45.25%） | 0 / 0 | 672/728 | 56 | 92.31% |
| sv39-load/M1 | 626 | 84（13.42%） | 542（86.58%） | 0 / 0 | 157/728 | 571 | 21.57% |
| sv39-load/M2 | 536 | 352（65.67%） | 184（34.33%） | 0 / 0 | 344/728 | 384 | 47.25% |
| sv39-load/M5 | 838 | 659（78.64%） | 179（21.36%） | 0 / 0 | 604/728 | 124 | 82.97% |
| sv39-store | 1000 | 548（54.80%） | 452（45.20%） | 0 / 0 | 354/380 | 26 | 93.16% |
| sv39-store/M1 | 328 | 54（16.46%） | 274（83.54%） | 0 / 0 | 102/380 | 278 | 26.84% |
| sv39-store/M2 | 292 | 193（66.10%） | 99（33.90%） | 0 / 0 | 199/380 | 181 | 52.37% |
| sv39-store/M5 | 380 | 301（79.21%） | 79（20.79%） | 0 / 0 | 309/380 | 71 | 81.32% |
| sv48-load | 1000 | 494（49.40%） | 506（50.60%） | 0 / 0 | 581/1122 | 541 | 51.78% |
| sv48-load/M1 | 344 | 34（9.88%） | 310（90.12%） | 0 / 0 | 118/1122 | 1004 | 10.52% |
| sv48-load/M2 | 272 | 163（59.93%） | 109（40.07%） | 0 / 0 | 204/1122 | 918 | 18.18% |
| sv48-load/M5 | 384 | 297（77.34%） | 87（22.66%） | 0 / 0 | 344/1122 | 778 | 30.66% |
| sv48-store | 1000 | 503（50.30%） | 497（49.70%） | 0 / 0 | 426/606 | 180 | 70.30% |
| sv48-store/M1 | 346 | 42（12.14%） | 304（87.86%） | 0 / 0 | 111/606 | 495 | 18.32% |
| sv48-store/M2 | 269 | 168（62.45%） | 101（37.55%） | 0 / 0 | 164/606 | 442 | 27.06% |
| sv48-store/M5 | 385 | 293（76.10%） | 92（23.90%） | 0 / 0 | 251/606 | 355 | 41.42% |

M1 为翻转标志位，M2 为 PPN 重排，M5 为未测位扰动（G、RSW）。同一类被多个算子命中时，合计只算一次，不能直接相加各算子命中类数。

完整逐例结果：[ledger.csv](../../output/fuzz-p1b-classes/ledger.csv) / [ledger.json](../../output/fuzz-p1b-classes/ledger.json)；完整统计：[statistics.json](../../output/fuzz-p1b-classes/statistics.json)；未命中类清单：[unhit-classes.json](../../output/fuzz-p1b-classes/unhit-classes.json)。

已填入实际 `class_id` 的完整样本：[sv39-load](../../output/fuzz-p1b-classes/classified/sv39-load.jsonl)、[sv39-store](../../output/fuzz-p1b-classes/classified/sv39-store.jsonl)、[sv48-load](../../output/fuzz-p1b-classes/classified/sv48-load.jsonl)、[sv48-store](../../output/fuzz-p1b-classes/classified/sv48-store.jsonl)。这些样本保留补好两处 `fcsr` 的原始变异体，只填写实际路径号和类号。judge 重新计算的结果、完整后态和原始守卫向量另存于 `mutants/judge/<场景>/judged.jsonl`，原样保留。

M5 也有 437 个（21.99%）跳类。它在 P1b 中保证结果和形状不变，并不保证守卫类不变；按守卫类调度时也需要重新取得其类号。

## 父类 → 子类转移

仅统计跳类，共 2322 条不同的“场景、算子、父类、子类”转移，合计 2360 个变异体。完整转移表（只列有跳转的）：[transitions.csv](../../output/fuzz-p1b-classes/transitions.csv) / [transitions.json](../../output/fuzz-p1b-classes/transitions.json)。

下表列次数最多的 20 条。`Pxx/Cn` 表示该场景的路径别名和原始类号；路径别名只为方便阅读，按路径号排序生成，完整对应见 [paths.csv](../../output/fuzz-p1b-classes/paths.csv)，不参与类号计算。

| 场景 | 算子 | 父类 | 子类 | 个数 |
| --- | --- | --- | --- | ---: |
| sv39-load | M1 | P09/C12 | P26/C1 | 2 |
| sv39-load | M1 | P11/C5 | P02/C1 | 2 |
| sv39-load | M1 | P12/C31 | P02/C1 | 2 |
| sv39-load | M1 | P12/C58 | P19/C0 | 2 |
| sv39-load | M1 | P13/C4 | P02/C1 | 2 |
| sv39-load | M1 | P18/C19 | P09/C1 | 2 |
| sv39-load | M1 | P18/C46 | P09/C2 | 2 |
| sv39-load | M1 | P18/C93 | P09/C10 | 2 |
| sv39-load | M1 | P18/C173 | P09/C19 | 2 |
| sv39-load | M1 | P24/C19 | P02/C1 | 2 |
| sv39-load | M2 | P11/C12 | P04/C3 | 2 |
| sv39-load | M2 | P11/C14 | P04/C3 | 2 |
| sv39-load | M2 | P16/C0 | P04/C0 | 2 |
| sv39-load | M2 | P18/C56 | P09/C4 | 2 |
| sv39-load | M2 | P20/C89 | P09/C31 | 2 |
| sv39-load | M5 | P07/C19 | P07/C23 | 2 |
| sv39-load | M5 | P12/C24 | P12/C16 | 2 |
| sv39-load | M5 | P18/C44 | P18/C32 | 2 |
| sv39-load | M5 | P18/C146 | P18/C154 | 2 |
| sv39-store | M2 | P24/C42 | P09/C14 | 2 |

## 14 个原有硬件分歧落在哪些类

14 例覆盖 14 个不同的实际守卫类。类身份包含场景，不能把不同场景的同号类合并。全部由 M2 产生，其中 13 例留在父类，1 例跳类。因此，本批跳类率不能代替发现价值，也不能把跳类作为保留变异体的唯一条件。

| 场景 | 变异体 | 算子 | 父类 → 实际类 | 叶级别 | 失败原因 | judge / J2 / 旧 J1 cause | XiangShan / NEMU cause |
| --- | --- | --- | --- | ---: | --- | --- | --- |
| sv39-load | mutant-0151 | M2 | P24/C3 → P24/C3 | L0 | A=0 | 13/13/13 | 5/13 |
| sv39-load | mutant-0153 | M2 | P05/C9 → P05/C9 | L0 | LOAD 权限 | 13/13/13 | 5/13 |
| sv39-load | mutant-0927 | M2 | P24/C80 → P24/C80 | L0 | A=0 | 13/13/13 | 5/13 |
| sv39-load | mutant-1012 | M2 | P15/C8 → P15/C8 | L2 | A=0 | 13/13/13 | 5/13 |
| sv39-load | mutant-1641 | M2 | P08/C5 → P08/C5 | L1 | A=0 | 13/13/13 | 5/13 |
| sv39-load | mutant-1697 | M2 | P08/C18 → P08/C18 | L1 | A=0 | 13/13/13 | 5/13 |
| sv39-store | mutant-0119 | M2 | P14/C3 → P23/C11 | L1 | STORE 权限 | 15/15/15 | 7/15 |
| sv39-store | mutant-0371 | M2 | P15/C8 → P15/C8 | L2 | A=0 | 15/15/15 | 7/15 |
| sv39-store | mutant-0520 | M2 | P24/C48 → P24/C48 | L0 | A=0 | 15/15/15 | 7/15 |
| sv39-store | mutant-0793 | M2 | P16/C1 → P16/C1 | L2 | STORE 权限 | 15/15/15 | 7/15 |
| sv48-load | mutant-0589 | M2 | P07/C83 → P07/C83 | L0 | A=0 | 13/13/13 | 5/13 |
| sv48-load | mutant-0672 | M2 | P07/C6 → P07/C6 | L0 | A=0 | 13/13/13 | 5/13 |
| sv48-load | mutant-0702 | M2 | P01/C21 → P01/C21 | L1 | A=0 | 13/13/13 | 5/13 |
| sv48-store | mutant-0209 | M2 | P01/C33 → P01/C33 | L1 | A=0 | 15/15/15 | 7/15 |

上述实际类涉及的路径号：

| 场景 | 路径别名 | path_signature |
| --- | --- | --- |
| sv39-load | P05 | `6417597896559680344` |
| sv39-load | P08 | `7143617572799853392` |
| sv39-load | P15 | `9915689945045587861` |
| sv39-load | P24 | `14946538549964930339` |
| sv39-store | P15 | `9915689945045587861` |
| sv39-store | P16 | `10425144959524720486` |
| sv39-store | P23 | `14651400866703406955` |
| sv39-store | P24 | `14946538549964930339` |
| sv48-load | P01 | `211570932649944466` |
| sv48-load | P07 | `3756867546370179447` |
| sv48-store | P01 | `211570932649944466` |

它们属于同一已上报问题族：实际叶 PTE 的 PPN 超宽，遍历因权限或 A/D 检查应报页异常；XiangShan 报访问异常，NEMU 与 Isla 报页异常。“同一问题族”沿用 P1b 已确认的窄规则，不能解释为同一个守卫类，也不能按整类过滤。

每例完整叶 PTE、守卫向量、原始路径号和三方 cause 见 [mismatches-14.json](../../output/fuzz-p1b-classes/mismatches-14.json)。

## 未接纳、新类和结果一致性

- 未被任何路径接纳：0 个。原因分类为空；没有需要归因于排除区的变异体。
- 守卫向量不在完整种子映射表内：0 个。
- 所有 5000 条变异体接纳输出均标记守卫唯一、后态唯一；每个输入恰好一条路径接纳。
- judge 与 J2 的完整 `result`、异常 cause，以及旧 J1 接纳/一致记录的差异：0 个。
- 额外比较重新计算的寄存器后态（去掉新 IR 新增的 `fcsr`）和内存后态；差异同样纳入下方清单。

全部不一致清单：[differences.json](../../output/fuzz-p1b-classes/differences.json)；未接纳清单：[unaccepted.json](../../output/fuzz-p1b-classes/unaccepted.json)；新类清单：[new-classes.json](../../output/fuzz-p1b-classes/new-classes.json)。这里的“judge 与 J2/J1 不一致”与原有 14 个硬件分歧是两种统计。

## 输入处理与类号来源

先用新 judge 对 ecfg4b 四场景 2836 个种子分类，建立 `(场景, path_signature, guard_vector) → class_id`。守卫向量直接取 judge 输出；每条路径内按向量排序，核对其从 0 起的名次全部等于种子类号，2836 个种子覆盖 122 条路径，没有自行解释守卫表达式或重算守卫。映射表见 [seed-map.json](../../output/fuzz-p1b-classes/seed-map.json)。

`guard_order` 中的记录编号是进程内全局计数器分配的编号，会随并发运行而变化，不能跨进程按编号匹配。judge 的规范向量按父链和记录位置排序；本轮只用规范向量作映射键。为确认坐标稳定，比较了本轮种子与已有种子 judge 输出：2836 条路径号及向量全部相同，虽然其中 2740 条的记录编号不同。记录见 [guard-order-note.json](../../output/fuzz-p1b-classes/guard-order-note.json)。

变异体从旧 `judge-batches.json` 指向的原始 J1 输入读取。通过变异记录中的父种子 `(path_signature, class_id)` 找到 ecfg4b 同类种子，只把该种子的 `pre_registers.fcsr` 与 `isa_state.fcsr` 分别补入变异体对应字段。不补后态，后态由 judge 重新计算。补入后再删除这两项，要求整个 JSON 对象与原变异体完全相等；`pre_memory` 也单独比较相等。因此没有改变任何页表字节、内存地址、SATP、指令或其他输入。5000/5000 均通过，见 [input-audit.json](../../output/fuzz-p1b-classes/input-audit.json)。

对比旧 J2 时使用原始 J1 输入的 `result`，同时核对 `accepted.json` 的结果与预测 cause；旧 J1 使用原批次 `check.json` 的逐例接纳/一致计数，并核对历史账本中的 Isla cause。`accepted.json` 中重放用的诱饵内存没有加入本轮 judge 输入。

## 执行状态与范围

直接复用 `target/release/isarch` 和 `output/judge/validate.py` 的命令及运行逻辑，新 IR、`config-xs.toml`、指令和前态沿用只读 ecfg4b。没有重建二进制、重验 judge 实现、改动 Sail/Isla 源码、写来源工作树或执行 git 写操作。每场景 `-T 32`，最多四场景并发；保留原 `--smt-timeout 5 --timeout 890` 和 900 秒外限。

| 阶段 | 场景 | 秒 | 原始退出码 | 原始状态 / errors |
| --- | --- | ---: | ---: | --- |
| 种子 | sv39-load | 221.80 | 1 | partial / 5 |
| 变异体 | sv39-load | 481.26 | 1 | partial / 5 |
| 种子 | sv39-store | 95.03 | 1 | partial / 5 |
| 变异体 | sv39-store | 266.37 | 1 | partial / 5 |
| 种子 | sv48-load | 628.39 | 1 | partial / 7 |
| 变异体 | sv48-load | 419.60 | 1 | partial / 7 |
| 种子 | sv48-store | 216.01 | 1 | partial / 7 |
| 变异体 | sv48-store | 323.37 | 1 | partial / 7 |

八个批次的执行超时、SMT 超时、终值查询超时、未完成路径和待处理批次均为 0。原始 `partial`、退出 1 和每场景 5/7 个执行错误均保留；它们与既有排除域记录相符，本轮没有重做逐查询排除证明，也没有把它们改写为 finished。没有触发单步超过 40 分钟无进展的停止条件。完整 argv、cwd、耗时、退出码在各批次 `done.json`，汇总见 [raw-runs.json](../../output/fuzz-p1b-classes/raw-runs.json)。

## 可复现命令

从 isla-judge 工作树根目录执行。已有完成批次拒绝覆盖；复跑先在脚本中将 OUT 改为本树内新的空目录，同步报告输出路径。所有脚本、输入副本、缓存和日志均位于本轮输出目录。

```sh
export PYTHONDONTWRITEBYTECODE=1
python3 output/fuzz-p1b-classes/test_classify.py
python3 output/fuzz-p1b-classes/classify.py seeds
python3 output/fuzz-p1b-classes/classify.py prepare
python3 output/fuzz-p1b-classes/classify.py mutants
python3 output/fuzz-p1b-classes/analyze.py
python3 output/fuzz-p1b-classes/report.py
python3 output/fuzz-p1b-classes/audit.py
```

数据处理测试按先失败后实现执行，覆盖只补两处 `fcsr`、跨路径同号跳类、新类识别和实际类去重计数，4/4 通过。失败/通过日志保存在本轮输出目录。产物核账见 [final-audit.json](../../output/fuzz-p1b-classes/final-audit.json)。本轮不改 Rust 源码，不重新运行构建、make 或 judge 实现的既有验证。
