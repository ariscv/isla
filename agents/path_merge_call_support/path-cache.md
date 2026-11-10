**结论：RTYPE 与 STORE 的缓存读回等价验收均通过；九组运行全部完成。STORE 两次独立探索的完整认证、judged、mutants 相同，额外的独立 DAG 字节比较不同。阶段日志和最小单测已完成。**

例如，STORE B／C／D 的 2803 个 DAG 文件全部逐字节相同，20 条 corpus 的完整认证及 20 个 mutant 的输出相同；双编码 DTO、重建后 DTO 和 FastFacts 重算均通过。RTYPE 的 A1／A2／B／C／D 全部比较项相同。独立 STORE B／A2 的 2543 个 DAG 文件不同，差异完整保留，下文列出具体字段和原因。

**实际架构与方案 v2 的对应关系**

| 位置 | 职责 |
| --- | --- |
| `isla-lib/src/executor/path_cache/expr.rs` | 完整 SMT 类型、表达式、定义及浮点运算镜像；也保留 Assume 事件中以位置为变量的表达式 |
| `value.rs`、`event.rs` | 完整值、混合位串、事件、属性、访存选项和区域边界镜像 |
| `trace.rs` | 按实际 Arc 节点导出共享分段，保留空段，恢复父链及检查点计数 |
| `path.rs` | 完整 SamplePath、合并记录、受保护寄存器读取和 FastFacts |
| `names.rs`、`validate.rs` | 原始名字环境核对、枚举与反向表核对、符号及结构检查 |
| `src/isarch/path_cache.rs` | CLI、文件发布、来源记录、Target 运行期数据和计时 |
| `src/isarch/exec.rs`、`fuzz/classifier.rs` | 完成初始化后选择探索或读缓存，再进入既有认证、变异和 judge |

数据文件共用同一套静态 DTO，使用 serde 外部标签，不省略字段。索引使用 u64，Sym 使用 u32；集合按名字编号或符号编号排序。已有 serde 的 Name、SourceLoc、B64、B129 和 Accessor 直接复用。manifest 的来源记录和错误摘要也使用静态类型，并补充 bincode 往返测试。

核心类型的私有字段通过 `smt.rs` 和 `sample_fast.rs` 的受控转换进出。现有 `Symtab::to_raw_table()` 已满足原始表导出要求，因此没有修改 `ir.rs`。检查点恢复继续使用既有 Solver 重放接口，没有保存 Z3 指针或执行闭包。

文件布局保持方案 v2：

```text
缓存目录/
  manifest.json
  segments.json
  segments.bin
  paths.json
  paths.bin
```

写出要求使用新目录。数据文件完成写入、刷新和同步后，才把 `manifest.pending` 重命名为 `manifest.json`。manifest 与数据封套都记录批次编号和条目数。缺文件、混用批次、条目数不符和结构损坏均直接 panic。

这些是方案 v2 的落地细节，没有改变架构：

- 除双编码核对外，读回还立即重新导出 DTO，逐字段核对恢复后的路径和分段。
- 导出器持有原 Arc，防止已释放地址被复用后误判为共享节点。
- arm 恢复到 root／then／else 静态字面量；region 在进程级锁内查询、分配和插入，同名字符串只分配一次。
- 一次缓存限定一个 clause、一个探索批次，避免目录被多个独立结果覆盖。
- 读缓存用于 fuzz 入口；写缓存也支持 solve-state。旧用例列表和执行帧不在快照范围内。

**本轮最小改动与阶段记录**

新增一项单测，先确认 Stages 接口缺失导致失败，再实现日志接口；本轮 `cargo test -j 16 -p isla --lib path_cache` 的 4 项测试全部通过。没有扩大单测范围。fmt 和 diff 空白检查通过，红绿日志分别为 `output/path-cache/stages-red.log`、`stages-green.log`。

每个完成阶段都立即向 stderr 输出 `[PATH_CACHE_STAGE]`，并追加到 fuzz 输出目录的 `path-cache-stages.jsonl`，每行同步落盘。记录包含 stage、seconds、since_start；编码写出另有文件名、字节数，最终缓存写出记录还含 json／bin 累计耗时、路径数、段数、未去重段数与去重率。

阶段包括 exploration、dag、fast_facts、cache_capture、cache_write_json／bin、cache_write、cache_manifest、cache_read_json／bin、cache_crosscheck、cache_validate、dto_rebuild、checkpoint_restore、corpus_certification、campaign_start 和 campaign_end。DAG 与事实分析的日志分别列出内部 Z3 重放时间；checkpoint_restore 在初始 corpus 认证前立即记录，便于区分两者。缓存格式和执行语义保持原实现。

**新增 CLI 的完整示例**

以下命令从本工作树根目录执行。示例复用验收生成的配置和 corpus，每个 fuzz 输出目录都必须尚不存在。

```bash
path_cache_common=(
  -A /data1/baiyifan/workplace/isla-runner/.worktree/pathmerge-all-20261110/isla/rv64d.ir
  -C "$PWD/output/path-cache/acceptance/store-isa.toml"
  -T 32 --tastic qfaufbv --smt-timeout 5 --timeout 240 --path-merging
  --execution-limits-config "$PWD/output/path-cache/acceptance/store-judge.toml"
  --prestate 'satp=0x8000000000080200'
  --prestate 'menvcfg={bits=0x0000000000000000}'
  --prestate 'senvcfg={bits=0x0000000000000000}'
  --prestate 'mseccfg={bits=0x0000000000000000}'
  --prestate 'mstatus={bits=0x0000000a00040000}'
)
path_cache_campaign=(
  fuzz --clause STORE --fuzz-mode campaign --fuzz-scenario path-cache-store
  --fuzz-corpus "$PWD/output/path-cache/acceptance/store/corpus.jsonl"
  --fuzz-feedback none --fuzz-control-percent 0 --fuzz-seed 42
  --fuzz-budget 20 --fuzz-certify-all
)

timeout --signal=TERM --kill-after=10s 120m \
  output/path-cache/build/release/isarch \
  "${path_cache_common[@]}" "${path_cache_campaign[@]}" \
  --fuzz-output "$PWD/output/path-cache/example-write" \
  --path-cache-write "$PWD/output/path-cache/example-cache" --path-cache-format both

timeout --signal=TERM --kill-after=10s 120m \
  output/path-cache/build/release/isarch \
  "${path_cache_common[@]}" "${path_cache_campaign[@]}" \
  --fuzz-output "$PWD/output/path-cache/example-json" \
  --path-cache-read "$PWD/output/path-cache/example-cache" --path-cache-encoding json

timeout --signal=TERM --kill-after=10s 120m \
  output/path-cache/build/release/isarch \
  "${path_cache_common[@]}" "${path_cache_campaign[@]}" \
  --fuzz-output "$PWD/output/path-cache/example-bin" \
  --path-cache-read "$PWD/output/path-cache/example-cache" --path-cache-encoding bin
```

`--path-cache-format` 可选 json、bin、both，默认 both。`--path-cache-encoding` 默认 json，不会在缺少 JSON 时改读 bin。读写选项不能同时使用。

读回时可分别追加 `--path-cache-export-dag` 和 `--path-cache-recompute-facts`。后者重新计算事实，并与缓存事实完整比较。`--path-cache-crosscheck` 同时解码两种格式，比较全部 DTO 字段。

**输入与资源边界**

本轮命令、原始日志、阶段记录、资源采样、进程监督结果及比较报告均在 `output/path-cache/acceptance-v2/`。驱动复用上一轮 `acceptance/run.py` 的探索参数，以及原来的 IR、ISA 配置、执行限制和 corpus 文件。所有新组使用 `binary.json` 记录的同一二进制。

IR 只读复用指定外部 rv64d.ir。STORE 保留 U／S／M 三态自由，使用原 SATP、mstatus 和环境 CSR 参数及 20 条 corpus；RTYPE 使用默认 ISA 配置、`--tastic default`、路径合并和原有 10 条 corpus；选择 default 是因为 RTYPE 在 qfaufbv 下有已知的 Poison 部分错误，该错误不在本任务范围内。所有组均为 -T 32、种子 42、预算 20、feedback none、control-percent 0、certify-all。

RTYPE 顺序为 A1→A2→B→C→D，每组外限 30m；STORE 为 B→C→D→A2，每组外限 120m。C／D 均启用 export-dag、recompute-facts、crosscheck。本轮九组 isarch 均由现有 `scripts/solve_process.py` 监督 GNU timeout，带 TERM 与 kill-after=10s。每组结束记录 `remaining-isarch.json`，已完成组均为空。超时组不重跑，继续下一组；STORE A2 仅在 B 的认证与 campaign 均结束时运行。

corpus 沿用上轮原文件，没有再次导出；STORE 原 class_cap=1 导出拿到足够 entry 后中断，残留进程已由主机终止，导出并非完整枚举（见 acceptance/store/export/result.json）。后续所有 isarch 均执行上述外层 timeout；本轮没有新增导出运行。

上一轮 STORE A1 的 2803 个 DAG 与 path-index 保留作额外对照；它使用旧二进制。本轮只增加阶段输出，没有修改 DAG 的生成方式。C／D 的 DAG 已在逐文件比较并保留完整 SHA 摘要后删除，分别记录于 dag-removed.json；其余 DAG 保留。最终 output/path-cache 约 7.1GiB，低于 10G 上限。

**真实文件格式片段**

以下来自本轮 RTYPE B 的真实缓存；bit_width=129 指 Isla 位向量承载类型 B129，不是 ISA 的 XLEN。manifest.json 字段摘录：

```json
{
  "schema_version": 1,
  "bit_width": 129,
  "current_ir_review": "未做当前 IR 复核",
  "completeness": "complete",
  "clause": "zRTYPE",
  "paths": [
    {
      "file": "paths.json",
      "encoding": "Json",
      "entries": 10,
      "batch_id": "164-1794258485889650110"
    },
    {
      "file": "paths.bin",
      "encoding": "Bin",
      "entries": 10,
      "batch_id": "164-1794258485889650110"
    }
  ]
}
```

paths.json 首条路径字段摘录：

```json
{
  "signature": 211687959586195726,
  "checkpoint": {
    "num": 7,
    "next_var": 1113,
    "leaf": 6
  },
  "facts": {
    "guard_unique": true,
    "post_unique": true,
    "simple_pre": true
  }
}
```

**RTYPE 的完整逐项对照**

| 比较项 | A1／A2 | A1／B | B／C | B／D |
| --- | --- | --- | --- | --- |
| FastFacts／path-index | 相同 | 相同 | 相同 | 相同 |
| DAG 清单 | 相同 | 相同 | 相同 | 相同 |
| 全部 DAG 文件逐字节 | 相同 | 相同 | 相同 | 相同 |
| 完整认证报告 | 相同 | 相同 | 相同 | 相同 |
| 完整 corpus-judged | 相同 | 相同 | 相同 | 相同 |
| 类目录映射 | 相同 | 相同 | 相同 | 相同 |
| 完整 judged | 相同 | 相同 | 相同 | 相同 |
| 完整 mutants | 相同 | 相同 | 相同 | 相同 |

C／D 均记录 cache_crosscheck.equal=true、dto_rebuild.dto_equal=true，重算事实的完整断言也通过。每组都认证 10 条 corpus，并生成、判定和认证 20 个 mutant。没有删除或规范化任何比较字段。证据为 `rtype/compare-*.json`、`dag-sha-*.json`、各组阶段 JSONL 及原始输出。

**RTYPE 效果数据**

| 组 | 探索秒 | 写缓存秒 | JSON 主解析秒 | bin 主解析秒 | 判定池 Z3 重放秒 | 到 campaign 秒 | 进程墙钟秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| A1 | 47.034234 | — | — | — | 0.332303 | 50.885380 | 55.032404 |
| A2 | 48.400390 | — | — | — | 0.389919 | 52.115588 | 56.035643 |
| B | 47.838281 | 0.041409 | — | — | 0.433528 | 52.822748 | 56.036251 |
| C | — | — | 0.010969 | — | 0.477703 | 5.661054 | 10.011687 |
| D | — | — | — | 0.001823 | 0.500443 | 5.978825 | 11.010874 |

到 campaign 时间从 clause 的缓存／探索入口起算，不含此前的 IR 与公共环境初始化；进程墙钟另列。主解析时间包含数据文件读取与解码，不含 Z3；另一编码的 crosscheck 时间另记在阶段文件。C／D 的到 campaign 时间包含全部三个审计开关开销，不是默认跳过 DAG 和事实分析的最短路径。共享主机的单次结果不作为稳定性能基准。

RTYPE：10 条路径；20 个共享段；逐路径计数合计 74 段，段去重率 **72.97%**。JSON 数据文件合计 **3255664 字节**，bin 合计 **306499 字节**；共享 manifest 为 **693290 字节**。JSON 写出 0.020323 秒，bin 写出 0.004684 秒；缓存总写出含发布为 0.041409 秒。

RTYPE 两次无缓存到 campaign 的均值为 51.500484 秒；C 为 5.661054 秒，减少 89.01%；D 为 5.978825 秒，减少 88.39%。

**STORE 的阶段结果**

| 组 | 状态 | 最近完成阶段 | 说明 |
| --- | --- | --- | --- |
| B | 退出 0 | campaign_end |  |
| C | 退出 0 | campaign_end |  |
| D | 退出 0 | campaign_end |  |
| A2 | 退出 0 | campaign_end |  |

**STORE 的逐项对照**

| 比较项 | 旧 A1／B（额外对照） | B／C | B／D | B／A2 |
| --- | --- | --- | --- | --- |
| FastFacts／path-index | 相同 | 相同 | 相同 | 相同 |
| DAG 清单 | 相同 | 相同 | 相同 | 相同 |
| 全部 DAG 文件逐字节 | 不同 | 相同 | 相同 | 不同 |
| 完整认证报告 | 未完成 | 相同 | 相同 | 相同 |
| 完整 corpus-judged | 未完成 | 相同 | 相同 | 相同 |
| 类目录映射 | 未完成 | 相同 | 相同 | 相同 |
| 完整 judged | 未完成 | 相同 | 相同 | 相同 |
| 完整 mutants | 未完成 | 相同 | 相同 | 相同 |

证据在 `store/compare-*.json`、`store/dag-sha-*.json` 及各组 `fuzz/path-cache-stages.jsonl`。B／C 和 B／D 还要求双编码 DTO、重建后 DTO、FastFacts 重算的完整断言通过；对应阶段完成记录是断言后的证据。独立探索的 DAG 另行报告，不把它与缓存恢复的逐字段等价混为一项。


旧 STORE A1 在上轮 60m 外限下退出 124，墙钟 3602.875114 秒；DAG 和 path-index 已写完，认证及 campaign 未完成。旧二进制没有本轮的阶段 JSONL，不能从它得到精确阶段计时；原始 result.json 和产物时间保留作证据。

STORE 额外旧 A1／新 B：path-index 和 DAG 清单相同，2541 个 DAG 文件不同。示例中 definitions[1018].smtlib 的排除值为旧 v1177=8、新 v1177=2；后态 tlb.vector[41].ctor 为旧 Some<RTLB_Entry>、新 None<RTLB_Entry>。差异涉及实际断言和状态表达式，不能只称为文本顺序。现有 symbolic_length.rs 的 fork_symbolic_value 从求解模型取候选，再加入排除约束；这部分及 SMT 种子策略本轮均未改动。证据为 old-A1-B-explanation.json 与 first-differences.json，未修改或删除字段来对齐。

**STORE 效果数据**

| 组 | 探索秒 | 缓存写出秒 | JSON 主解析秒 | bin 主解析秒 | 判定池 Z3 重放秒 | corpus 认证秒 | 到 campaign 秒 | 进程墙钟秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| B | 558.918151 | 18.803919 | — | — | 409.519650 | 28.427269 | 4151.066250 | 4225.145679 |
| C | — | — | 4.587788 | — | 413.784557 | 27.614816 | 3517.138632 | 3586.398792 |
| D | — | — | — | 0.934898 | 430.575706 | 28.760685 | 3572.433642 | 3642.474605 |
| A2 | 625.066120 | — | — | — | 411.058333 | 28.530680 | 4117.402997 | 4192.871574 |

| 组 | DAG 总秒（其中 Z3） | FastFacts 总秒（其中 Z3） | 交叉编码解析秒 | 结构检查秒 | DTO 重建与再导出核对秒 |
| --- | ---: | ---: | ---: | ---: | ---: |
| B | 2402.527906（121.899341） | 721.393998（113.887546） | — | — | — |
| C | 2349.891079（109.066201） | 711.675109（108.138436） | 1.017276 | 1.617408 | 3.693690 |
| D | 2400.761809（115.862901） | 699.254990（105.623047） | 4.437023 | 1.384150 | 3.102907 |
| A2 | 2330.424758（115.008356） | 716.397802（111.763068） | — | — | — |

DAG 和 FastFacts 总时间各自已经包含括号内的 Z3 重放；判定池重放是另一阶段，不重复计入解析时间。C／D 的到 campaign 总时间含重新导出 DAG、事实重算和双编码核对。


STORE B：2803 条路径、6159 个共享段，逐路径段数 169233，去重率 96.36%；JSON 数据 1065653368 字节，bin 数据 121180626 字节；共享 manifest 为 765814 字节。JSON 写出 15.122372 秒，bin 写出 2.481201 秒。

与纯无缓存 A2 的 4117.402997 秒相比，C 到 campaign 减少 600.264365 秒（14.58%），D 减少 544.969355 秒（13.24%）。JSON 与 bin 主解析分别为 4.587788 秒和 0.934898 秒，bin 数据大小约为 JSON 的 1／8.79。当前 C／D 仍强制重导出 DAG 与重算事实，共享主机单次数据不能用于比较编码的稳定端到端速度。汇总数值见 `effects-summary.json`。


STORE B／A2 的完整认证报告、corpus-judged、类目录映射、judged、mutants、path-index 与 DAG 清单全部逐字节相同；2543 个 DAG 文件不同。示例 `path-10001880363071611004.json` 中 definitions[1016].smtlib 排除的候选为 B 的 v1177=0、A2 的 v1177=62；state.post.tlb.vector[33].ctor 为 B 的 None<RTLB_Entry>、A2 的 Some<RTLB_Entry>。现有 fork_symbolic_value 从 Model.get_var 取候选再加入等式／排除约束，候选选择存在自由度。这是实际约束与状态表达式的差异，不只是文本排序；本轮没有修改该枚举逻辑或 SMT 种子策略。证据为 `store/B-A2-explanation.json`、`B-A2-first-differences.json` 及完整 SHA 清单。没有证明两次独立探索 DAG 的整体语义等价。

九组 isarch 全部退出 0，均完成 campaign_end，各组 remaining-isarch.json 均为空；没有新组触及外限。辅助驱动末尾额外要求 B／A2 的独立 DAG 字节相同，因此断言退出 1，未重跑或删除差异。`finished.json` 根据全部九份运行收据和完整比较报告记录此区别。方案 v2 必需的两次无缓存完整认证／judged／mutants 确定性，以及 B／C／D 的全部严格比较均通过。

**回归与已知限制**

| 命令 | 结果与记录 |
| --- | --- |
| `cargo test -j 16 -p isla --lib path_cache` | 本轮 4 通过，含新增阶段顺序测试；stages-green.log |
| `cargo test -j 16 -p isla-lib --test path_cache --test path_cache_structure --test path_cache_variants` | 上轮新增集成测试 13＋2＋14 通过；final-cache-tests.log |
| `cargo test -j 16 -p isla-lib` | 上轮库测试 809 通过、6 忽略，集成测试通过；final-official-isla-lib.log |
| `cargo test -j 16 -p isla --lib` | 上轮 231 通过、7 项既有失败；final-official-isla-libroot.log |
| `cargo test -j 16 -p isla --bins --test smt_contract` | 上轮二进制 27 项及 SMT 契约 1 项通过；final-official-isla-bins.log |
| `cargo fmt --all -- --check` | 本轮通过；stages-format-check.log |
| `git diff --check` | 本轮通过；stages-diff-check.log |

以上日志均在 `output/path-cache/`。本轮只增加一项阶段日志测试，没有重新扩大测试面。

上轮完整回归：isla-lib 库测试 809 通过、6 项既有忽略；isla 库测试 231 通过、7 项失败均为基线已存在的根目录 rv64d.ir 缺失；二进制测试与 SMT 契约通过。本轮只运行最小阶段测试及既有缓存测试，共 4 项通过；不重复扩大测试面。系统 Z3 4.13.3 的 default 随机种子问题仍通过 Makefile 指定的官方 Z3 5.3.4.0、提交 1fd1d3613 规避，没有修改 SMT 执行语义。

基线 7 项缺 IR 失败分别为 encdec_guard_f5_继承策略与固定前置权限、压缩编码回环与构造子校验、向量段store编码回环、回环拒绝amoswapq非法编码、回环拒绝ldu非法编码、回环放行合法load编码、非位向量编码报错。6 项忽略为 F5 万类压力测试，以及需要外部真实 IR 的 pte_is_invalid、get_xlpe、region_merge_real_ir_effects、samples_real_ir_pte_cross_mode、regions_real_ir。

本期未做当前 IR 的独立语义复核；manifest 与 provenance 均明确标注。跨 IR 编号重定位、压缩、执行帧续跑仍在范围外。本轮指定九组没有未完成项。历史旧 A1 的认证与 campaign 未完成，旧 A1／B 与 B／A2 的独立 STORE DAG 字节对照均不相同，已保留原始证据。当前 IR 独立复核仍未做，也没有修复 RTYPE qfaufbv 的已知 Poison 错误。C／D 全部带三个核对开关，本轮未另跑默认跳过 DAG／事实分析的最短读取路径，因此不报告该路径的实测总耗时。

**预期文件单元测试**

新增 `isla-lib/tests/path_cache_golden.rs`，不读取真实 IR、不运行 isarch：

- `正向序列化逐字节符合预期文件`：从核心类型构造快照，导出 DTO 并序列化，与手写预期 JSON 的全部字节比较。
- `反向预期文件重建核心字段及_dag_一致`：直接解码预期文件，逐字段比较核心路径、合并记录、访存和 SMT 事件；两边分别重放 checkpoint、导出 DAG，再逐字节比较。另仅用一条断言核对预期 DTO 的 bincode 编码／解码相等，不维护 bin 预期文件。

输入包含两条路径、一个共享父 trace 段、一个空段和一个含 Assert 的子段；覆盖 DeclareConst、DeclareFun／函数应用、DefineConst、DefineEnum／枚举成员、Assert、构造子寄存器读取、读写内存与 Cycle。前态覆盖 14 种主要 Val 变体，含具体位串、MixedBits 的具体段和符号段、结构、列表及符号构造子；记录覆盖 root／then／else、非连续编号、父引用、受保护寄存器读取和 memory_reads，memory_guards 非空，两条路径的 FastFacts 取不同值。

预期文件位于 `isla-lib/tests/path_cache_golden/segments.json`（56 行）与 `paths.json`（123 行），共 **179 行**。它们保存完整的 Segment／CachedPath DTO 数组，不纳入 isarch 的 manifest／批次封套，因此没有时间或来源哈希等变化字段。仅测试内的 Formatter 控制空白排版，所有 DTO 字段照常序列化；生产代码未增加规范化或字段跳过。

预期字段由固定输入逐项推出：名字 25～31 对应 kind／first／second／constructor／field／function／register；DefineEnum 先消耗 v0、v1，输入、条件、函数、结果、枚举结果依次为 v2～v6，next_var=7；两叶段 1、2 都引用父段 0；记录 20、30 的父记录均为 10。预期 JSON 按这些编号、字段值、事件顺序及集合排序核对，没有从被测程序输出直接更新文件。测试也没有自动更新预期文件的入口。

先故意把预期 signature 从 11 改为 12，确认两个测试分别在 paths 字节与核心 signature 比较处失败，再恢复 11 定稿。红绿日志为 `output/path-cache/golden-red.log`、`golden-green.log`。

运行命令（沿用 `scripts/run.mk` 的官方 Z3 前缀与链接设置）：

```bash
export Z3_PREFIX=/home/baiyifan/.local/opt/z3-official-1fd1d3613
export RUSTFLAGS="-L native=$Z3_PREFIX/lib -C link-arg=-Wl,-rpath,$Z3_PREFIX/lib"
export LD_LIBRARY_PATH="$Z3_PREFIX/lib"
export CARGO_TARGET_DIR=output/path-cache/build
export CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
cargo test -j 16 -p isla-lib --test path_cache_golden --test path_cache --test path_cache_structure --test path_cache_variants
cargo test -j 16 -p isla-lib -p isla --lib path_cache
cargo fmt --all -- --check
git diff --check
```

本轮结果：新增预期文件测试 2 项通过；既有缓存集成测试 29 项、缓存库内测试 5 项通过，共 36 项通过。`cargo fmt --all -- --check` 与 `git diff --check` 通过。既有库内测试日志为 `output/path-cache/golden-existing.log`；未运行 isarch、真实 IR 或大回归，未修改生产代码。
