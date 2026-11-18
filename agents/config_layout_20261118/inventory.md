# 逐字段映射（实施前盘点）

来源：`isla-lib/src/config.rs`、`isla-lib/src/config/region_options.rs`、`src/isarch/region_options.rs`、`src/isarch_main.rs`，基线 fe2c9e08。

| 旧 execution_limits 字段 | 新位置 | 语义 |
| --- | --- | --- |
| path_merging | path_merge.enabled | 全局合并启用 |
| region_step_budget | path_merge.step_budget | 默认8192；-1关闭，原校验不变 |
| region_options.defer_exit_check | path_merge.defer_exit_check | 功能开关 |
| region_options.lazy_z3_scope | path_merge.lazy_z3_scope | 功能开关，仅defer内生效 |
| region_options.witness_eval | path_merge.witness_eval | 功能开关 |
| region_options.prefix_compact | path_merge.prefix_compact | 功能开关 |
| region_options.bool_proof_rlimit | solver.bool_proof_rlimit | 求解参数，默认0 |
| region_options.witness_shadow | path_merge.diagnostics.witness_shadow | 只读诊断 |
| region_options.witness_local_shadow | path_merge.diagnostics.witness_local_shadow | 只读诊断 |
| region_options.bool_proof_profile | path_merge.diagnostics.bool_proof_profile | 只读诊断 |
| region_options.progress | path_merge.diagnostics.progress | 只读诊断 |
| region_options.native_snapshot | path_merge.diagnostics.native_snapshot | 只读诊断 |
| region_options.call_census | path_merge.diagnostics.call_census | 只读诊断 |
| region_options.probe_round_cost | path_merge.diagnostics.probe_round_cost | 只读诊断 |
| region_options.probe_query_timings | path_merge.diagnostics.probe_query_timings | 只读诊断 |
| region_options.query_dump_sites | path_merge.diagnostics.query_dump_sites | 只读诊断 |
| region_options.same_context_sites | path_merge.diagnostics.same_context_sites | 只读诊断 |
| region_options.query_dump_dir | path_merge.diagnostics.query_dump_dir | 只读诊断 |
| region_options.obligation_dump_dir | path_merge.diagnostics.obligation_dump_dir | 只读诊断 |
| regions | path_merge.regions，kind=limit_filter | 原分支/循环限制范围，保留原有清除override语义 |
| branch_region_limits | path_merge.regions，kind=branch_limit | 原每分支点的局部预算 |
| region_fork_limits | path_merge.regions，kind=fork_limit | 原区域预算及sample_bias和sample_bias_direction |
| merge_policy | path_merge.regions，kind=merge_policy | 原mode及函数/源码位置选择器；优先级不变 |
| merge_enumeration | path_merge.enumeration | 全局枚举配置；原enabled/mode/class_cap/path_cap/sample_stride/enumeration_threads/outputs(format,path)/max_output_bytes/predict_probes/predict_seed/predict_domain_cap原样保留 |
| strict | strict（不动） | IR校验 |
| ir_sha256 | ir_sha256（不动） | 来源/严格校验 |
| enabled | enabled（不动） | 执行限制总开关 |
| max_forks_per_branch | max_forks_per_branch（不动） | 非合并限制 |
| max_forks_per_path | max_forks_per_path（不动） | 非合并限制 |
| max_backjumps_per_loop | max_backjumps_per_loop（不动） | 非合并限制 |
| max_path_depth | max_path_depth（不动） | 非合并限制 |
| max_fork_pct_per_branch | max_fork_pct_per_branch（不动） | 非合并限制 |
| max_fork_pct_check_delay | max_fork_pct_check_delay（不动） | 非合并限制 |
| call_context_depth | call_context_depth（不动） | 限制计数上下文 |
| branch_sampling_seed | branch_sampling_seed（不动） | 具体化抽样 |
| on_limit_reached | on_limit_reached（不动） | 限制后行为 |
| case_quota | case_quota（不动） | 输出配额 |
| filter_model_exceptions | filter_model_exceptions（不动） | 输出过滤 |
| judge_resident_batch_size | judge_resident_batch_size（不动） | judge恢复上限 |

草案微调：regions使用显式kind区分四种现有语义，避免把范围筛选误当合并策略。求解组本基线只有bool_proof_rlimit；no_smt、skip_branch_checks、skip_bool_proofs、no_smt_keep_bool_proofs不存在，不新增。CLI诊断slow-query-*是现有独立全局SMT接口，基线无TOML字段，本轮保留。

运行时ExecutionLimits的path_merging、region_step_budget等名称不改；配置DTO删除对应旧字段。进程冻结只安装功能/诊断/证明参数，保持原冻结粒度。
