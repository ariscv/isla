# 环境变量清点与迁移对照

原位置以 a286b00c 为准；功能与诊断共16项，已全部移除环境读取。TOML 字段统一位于 `[execution_limits.region_options]`，CLI 覆盖对应 TOML 值。

| 原环境变量 | 原读取位置 | 用途 | 默认值 | 类别 | TOML 字段 | CLI |
| --- | --- | --- | --- | --- | --- | --- |
| `ISLA_REGION_DEFER_EXIT_CHECK` | isla-lib/src/executor/region_merge.rs:549 | 延迟区域出口检查 | false | 功能开关 | `defer_exit_check` | `--region-defer-exit-check=true/false` |
| `ISLA_REGION_WITNESS_EVAL` | isla-lib/src/smt/witness_shadow.rs:387 | 完整前提见证求值 | false | 功能开关 | `witness_eval` | `--region-witness-eval=true/false` |
| `ISLA_REGION_WITNESS_SHADOW` | isla-lib/src/smt/witness_shadow.rs:391 | 见证影子诊断 | false | 诊断 | `witness_shadow` | `--region-witness-shadow=true/false` |
| `ISLA_REGION_WITNESS_LOCAL_SHADOW` | isla-lib/src/smt/witness_shadow.rs:395 | 局部见证补全影子诊断 | false | 诊断 | `witness_local_shadow` | `--region-witness-local-shadow=true/false` |
| `ISLA_REGION_PREFIX_COMPACT` | isla-lib/src/smt/query.rs:706 | 迭代边界前缀固化 | false | 功能开关 | `prefix_compact` | `--region-prefix-compact=true/false` |
| `ISLA_REGION_BOOL_PROOF_PROFILE` | isla-lib/src/smt/proof_budget.rs:16 | 可选布尔证明资源统计 | false | 诊断 | `bool_proof_profile` | `--region-bool-proof-profile=true/false` |
| `ISLA_REGION_PROGRESS` | isla-lib/src/executor/stats/region_progress.rs:21<br>isla-lib/src/executor/stats/region_progress.rs:94 | 区域步数和查询进度诊断 | false | 诊断 | `progress` | `--region-progress=true/false` |
| `ISLA_REGION_NATIVE_SNAPSHOT` | isla-lib/src/smt/query.rs:109 | 原生查询快照 | false | 功能开关 | `native_snapshot` | `--region-native-snapshot=true/false` |
| `ISLA_CALL_CENSUS` | isla-lib/src/executor/stats/call_census.rs:10 | 有界函数调用统计 | false | 诊断 | `call_census` | `--call-census=true/false` |
| `ISLA_PROBE_ROUND_COST` | isla-lib/src/executor/stats/region_cost.rs:74 | 逐轮成本分账 | false | 诊断 | `probe_round_cost` | `--probe-round-cost=true/false` |
| `ISLA_PROBE_QUERY_TIMINGS` | isla-lib/src/smt/z3_timeout.rs:85 | 有界逐查询计时 | false | 诊断 | `probe_query_timings` | `--probe-query-timings=true/false` |
| `ISLA_REGION_BOOL_PROOF_RLIMIT` | isla-lib/src/smt/proof_budget.rs:7 | 可选布尔证明资源上限 | 0（不限） | 功能开关 | `bool_proof_rlimit` | `--region-bool-proof-rlimit=<value>` |
| `ISLA_QUERY_DUMP_SITES` | isla-lib/src/executor/stats/region_progress.rs:413 | 有界查询导出位置 | [] | 诊断 | `query_dump_sites` | `--query-dump-sites=<value>` |
| `ISLA_SAME_CONTEXT_SITES` | isla-lib/src/smt/dump.rs:365 | 同 Context 配对位置 | [] | 诊断 | `same_context_sites` | `--same-context-sites=<value>` |
| `ISLA_QUERY_DUMP_DIR` | isla-lib/src/smt/dump.rs:340 | 查询 SMT2 导出目录 | 未配置 | 诊断 | `query_dump_dir` | `--query-dump-dir=<value>` |
| `ISLA_OBLIGATION_DUMP_DIR` | isla-lib/src/smt/deferred_assertions.rs:198 | 断言义务诊断目录 | 未配置 | 诊断 | `obligation_dump_dir` | `--obligation-dump-dir=<value>` |

测试内部通信保留：

| 变量 | 读取／设置位置 | 用途与缺省 |
| --- | --- | --- |
| `ISLA_EXIT_CHECK_TEST_CHILD` | `isla-lib/src/executor/tests/region_merge_tests.rs` | 缺省父进程；子进程值0／1选择测试模式，子进程再调用正式 RegionOptions 配置接口 |
| `ISLA_ASSERT_OBLIGATION_CHILD` | 同上 | 缺省父进程；标识隔离义务回归及其被其他测试复用的执行体 |
| `ISLA_DEAD_ARM_TEST_CHILD` | 同上 | 缺省父进程；标识死臂回归子进程，进入后通过正式 API 开启候选 |
| `ISLA_REGION_QUERY_LIFETIME_TEST` | `isla-lib/src/smt/query.rs` | 缺省父进程；测试名标识隔离的 SMT tactic／查询生命周期测试 |

`ISLA_REGION_PROGRESS` 在生产缺省 false；cfg(test) 下原有自动采集保持不变。原有 `ISLA_STATS`、`ISLA_REGIONS_IR`、`ISLA_VERSION`、`ISLA_EXPORT_SAMPLES`、其他旧诊断及非本分支新增测试夹具不在迁移范围。本轮没有触碰 lazy Z3 scope 分支及其 `ISLA_REGION_LAZY_Z3_SCOPE`。
