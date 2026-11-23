//! 区域合并候选及诊断的 CLI 配置。
use isla_lib::config::ExecutionLimitsConfig;

const BOOL_OPTIONS: &[(&str, &str, &str)] = &[
    ("partial_commit_solver", "partial-commit-solver", "嵌套区域遇到Z3 查询失败时在外层保留两个片段；默认关闭"),
    (
        "partial_commit_finite_domain",
        "partial-commit-finite-domain",
        "嵌套区域遇到有限域推导不足时在外层保留两个片段；默认关闭",
    ),
    (
        "partial_commit_deferred_mode",
        "partial-commit-deferred-mode",
        "嵌套区域遇到延后模式限制时在外层保留两个片段；默认关闭",
    ),
    ("finite_domain_enumeration", "finite-domain-enumeration", "先按可确认的有限域枚举具体值；默认开启"),
    ("merge_poison_slots", "merge-poison-slots", "只消除已证明不可观察的局部未初始化槽位或载荷；默认开启"),
    ("defer_ctor_checks", "region-defer-ctor-checks", "延后推演时，构造子解包标签转为出口待证义务；默认开启"),
    ("defer_range_proofs", "region-defer-range-proofs", "延后推演时，范围证明转为出口待证义务；默认开启"),
    ("prune_constant_branches", "prune-constant-branches", "分支入口识别布尔恒值；默认开启"),
    ("arm_error_leaf", "arm-error-leaf", "保留带到达条件的臂内执行错误；默认关闭"),
    ("merge_concrete_values", "merge-concrete-values", "延后拆分区域具体字符串和机器整数；默认开启"),
    ("defer_call_effect_checks", "defer-call-effect-checks", "延后普通被调函数的传递状态效应检查；默认开启"),
    ("defer_exit_check", "region-defer-exit-check", "延迟区域出口检查；默认关闭"),
    ("lazy_z3_scope", "region-lazy-z3-scope", "延迟 Z3 条件作用域；默认关闭，仅在 defer 内生效，可能增加内存占用"),
    ("witness_eval", "region-witness-eval", "完整前提见证求值；默认关闭"),
    ("witness_shadow", "region-witness-shadow", "见证影子诊断；默认关闭"),
    ("witness_local_shadow", "region-witness-local-shadow", "局部见证补全影子诊断；默认关闭"),
    ("loop_fold_shapes", "region-loop-fold-shapes", "扩展循环逐轮折叠形状；默认关闭"),
    ("prefix_compact", "region-prefix-compact", "迭代边界前缀固化；默认关闭"),
    ("bool_proof_profile", "region-bool-proof-profile", "可选布尔证明资源统计；默认关闭"),
    ("progress", "region-progress", "区域步数和查询进度诊断；默认关闭"),
    ("native_snapshot", "region-native-snapshot", "原生查询快照；默认关闭"),
    ("call_census", "call-census", "有界函数调用统计；默认关闭"),
    ("probe_round_cost", "probe-round-cost", "逐轮成本分账；默认关闭"),
    ("probe_query_timings", "probe-query-timings", "有界逐查询计时；默认关闭"),
];

const NO_SMT_OPTIONS: &[(&str, &str)] = &[
    ("skip_branch_checks", "skip-branch-checks"),
    ("skip_bool_proofs", "skip-bool-proofs"),
    ("no_smt", "no-smt"),
    ("no_smt_keep_bool_proofs", "no-smt-keep-bool-proofs"),
];

pub fn add_cli(opts: &mut getopts::Options) {
    opts.optflagopt("", "bv-rewrite", "通用等价改写，缺省启用三条规则，false 关闭", "true|false|规则名列表");
    for (_, flag) in NO_SMT_OPTIONS {
        opts.optflagopt("", flag, "无 SMT 实验选项；裸 flag 等于 true，覆盖 TOML，默认 false", "true|false");
    }
    for (_, flag, help) in BOOL_OPTIONS {
        opts.optopt("", flag, help, "true|false");
    }
    opts.optopt("", "solver-on-unknown", "路径求解未判定或超时的处置，缺省 panic", "panic|dead");
    opts.optopt("", "on-path-timeout", "逐路径 --timeout 到限的处置，缺省 panic", "panic|dead");
    opts.optopt("", "region-max-merge-depth", "区域嵌套上限，默认不限；-1不限", "正整数|-1");
    opts.optopt("", "region-bool-proof-rlimit", "可选布尔证明资源上限，0 不限；默认 0", "u32");
    opts.optopt("", "query-dump-sites", "查询导出位置；逗号分隔，空串清空", "sites");
    opts.optopt("", "same-context-sites", "同 Context 配对位置，最多两个；空串清空", "sites");
    opts.optopt("", "query-dump-dir", "查询 SMT2 导出目录", "path");
    opts.optopt("", "obligation-dump-dir", "断言义务诊断导出目录", "path");
}

pub fn apply_cli(matches: &getopts::Matches, limits: &mut ExecutionLimitsConfig) -> Result<(), String> {
    let mut updated = limits.clone();
    if let Some(value) = matches.opt_str("solver-on-unknown") {
        updated.solver.on_unknown = value.parse().map_err(|error| format!("--solver-on-unknown {error}"))?;
    }
    if let Some(value) = matches.opt_str("on-path-timeout") {
        updated.on_path_timeout = value.parse().map_err(|error| format!("--on-path-timeout {error}"))?;
    }
    if matches.opt_present("bv-rewrite") {
        updated.solver.bv_rewrite =
            isla_lib::smt::rewrite::BvRewrite::parse(&matches.opt_str("bv-rewrite").unwrap_or_else(|| "true".into()))?;
    }
    for (field, flag, _) in BOOL_OPTIONS {
        if let Some(value) = matches.opt_str(flag) {
            let value: bool = value.parse().map_err(|_| format!("--{flag} 必须是 true 或 false"))?;
            match *field {
                "merge_poison_slots" => updated.path_merge.merge_poison_slots = value,
                "defer_ctor_checks" => updated.path_merge.defer_ctor_checks = value,
                "defer_range_proofs" => updated.path_merge.defer_range_proofs = value,
                "prune_constant_branches" => updated.path_merge.prune_constant_branches = value,
                "arm_error_leaf" => updated.path_merge.arm_error_leaf = value,
                "merge_concrete_values" => updated.path_merge.merge_concrete_values = value,
                "defer_call_effect_checks" => updated.path_merge.defer_call_effect_checks = value,
                "defer_exit_check" => updated.path_merge.defer_exit_check = value,
                "partial_commit_solver" => updated.path_merge.partial_commit_solver = value,
                "partial_commit_finite_domain" => updated.path_merge.partial_commit_finite_domain = value,
                "partial_commit_deferred_mode" => updated.path_merge.partial_commit_deferred_mode = value,
                "finite_domain_enumeration" => updated.path_merge.finite_domain_enumeration = value,
                "lazy_z3_scope" => updated.path_merge.lazy_z3_scope = value,
                "witness_eval" => updated.path_merge.witness_eval = value,
                "witness_shadow" => updated.path_merge.diagnostics.witness_shadow = value,
                "witness_local_shadow" => updated.path_merge.diagnostics.witness_local_shadow = value,
                "loop_fold_shapes" => updated.path_merge.loop_fold_shapes = value,
                "prefix_compact" => updated.path_merge.prefix_compact = value,
                "bool_proof_profile" => updated.path_merge.diagnostics.bool_proof_profile = value,
                "progress" => updated.path_merge.diagnostics.progress = value,
                "native_snapshot" => updated.path_merge.diagnostics.native_snapshot = value,
                "call_census" => updated.path_merge.diagnostics.call_census = value,
                "probe_round_cost" => updated.path_merge.diagnostics.probe_round_cost = value,
                "probe_query_timings" => updated.path_merge.diagnostics.probe_query_timings = value,
                _ => unreachable!("区域 CLI 字段必须登记"),
            }
        }
    }
    if let Some(value) = matches.opt_str("region-max-merge-depth") {
        updated.path_merge.max_merge_depth = Some(value.parse().map_err(|_| "--region-max-merge-depth 必须为整数")?);
    }
    if let Some(value) = matches.opt_str("region-bool-proof-rlimit") {
        updated.solver.bool_proof_rlimit =
            value.parse().map_err(|_| "--region-bool-proof-rlimit 必须是非负32位整数")?;
    }
    for flag in ["query-dump-sites", "same-context-sites"] {
        if let Some(value) = matches.opt_str(flag) {
            let sites = if value.is_empty() { Vec::new() } else { value.split(',').map(str::to_owned).collect() };
            match flag {
                "query-dump-sites" => updated.path_merge.diagnostics.query_dump_sites = sites,
                "same-context-sites" => updated.path_merge.diagnostics.same_context_sites = sites,
                _ => unreachable!(),
            }
        }
    }
    for flag in ["query-dump-dir", "obligation-dump-dir"] {
        if let Some(value) = matches.opt_str(flag) {
            match flag {
                "query-dump-dir" => updated.path_merge.diagnostics.query_dump_dir = Some(value.into()),
                "obligation-dump-dir" => updated.path_merge.diagnostics.obligation_dump_dir = Some(value.into()),
                _ => unreachable!(),
            }
        }
    }
    for (field, flag) in NO_SMT_OPTIONS {
        if matches.opt_present(flag) {
            let value = matches.opt_str(flag).unwrap_or_else(|| "true".into());
            let value: bool = value.parse().map_err(|_| format!("--{flag} 必须是 true 或 false"))?;
            match *field {
                "skip_branch_checks" => updated.solver.skip_branch_checks = value,
                "skip_bool_proofs" => updated.solver.skip_bool_proofs = value,
                "no_smt" => updated.solver.no_smt = value,
                "no_smt_keep_bool_proofs" => updated.solver.no_smt_keep_bool_proofs = value,
                _ => unreachable!("无 SMT CLI 字段必须登记"),
            }
        }
    }
    isla_lib::config::RegionOptions::from_config(&updated).validate()?;
    *limits = updated;
    Ok(())
}

/// 全局无 SMT 只允许导出未认证候选，禁止生成样例、认证或普通缓存读回。
pub fn validate_no_smt_mode(
    matches: &getopts::Matches,
    options: &isla_lib::config::RegionOptions,
) -> Result<(), String> {
    if options.no_smt
        && (!matches.opt_present("path-cache-only")
            || !matches.opt_present("path-cache-write")
            || matches.opt_present("path-cache-read")
            || matches.opt_present("check-samples")
            || matches.free.first().map(String::as_str) != Some("solve-state"))
    {
        return Err("no_smt 只支持 solve-state --path-cache-only --path-cache-write，不支持样例认证或缓存读回".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::config::RegionOptions;

    fn cli(config: &mut ExecutionLimitsConfig, args: &[&str]) -> Result<(), String> {
        let mut opts = getopts::Options::new();
        add_cli(&mut opts);
        apply_cli(&opts.parse(args).map_err(|e| e.to_string())?, config)
    }

    #[test]
    fn bv_rewrite_cli_overrides_toml_and_rejects_unknown_rules() {
        let mut config = ExecutionLimitsConfig::default();
        let all = isla_lib::smt::rewrite::BvRewrite::parse("true").unwrap();
        cli(&mut config, &[]).unwrap();
        assert_eq!(config.solver.bv_rewrite, all);
        let mut config: ExecutionLimitsConfig = toml::from_str("[solver]\nbv_rewrite=false").unwrap();
        cli(&mut config, &[]).unwrap();
        assert!(!config.solver.bv_rewrite.enabled());
        cli(&mut config, &["--bv-rewrite"]).unwrap();
        assert_eq!(config.solver.bv_rewrite, all);
        cli(&mut config, &["--bv-rewrite=false"]).unwrap();
        assert!(!config.solver.bv_rewrite.enabled());
        cli(&mut config, &["--bv-rewrite=mask-and,sign-bound"]).unwrap();
        assert_eq!(isla_lib::config::RegionOptions::from_config(&config).bv_rewrite, config.solver.bv_rewrite);
        let prior = config.clone();
        assert!(cli(&mut config, &["--bv-rewrite=unknown"]).is_err());
        assert_eq!(config, prior);
    }

    #[test]
    fn region_options_cli_defaults_and_boolean_overrides() {
        let mut limits = ExecutionLimitsConfig::default();
        cli(&mut limits, &[]).unwrap();
        assert_eq!(limits, ExecutionLimitsConfig::default());
        assert!(limits.path_merge.merge_concrete_values);
        assert!(limits.path_merge.defer_call_effect_checks);
        assert!(limits.path_merge.defer_range_proofs && limits.path_merge.defer_ctor_checks);
        for (field, flag, _) in BOOL_OPTIONS {
            let section = if [
                "partial_commit_finite_domain",
                "partial_commit_solver",
                "partial_commit_deferred_mode",
                "prune_constant_branches",
                "arm_error_leaf",
                "merge_concrete_values",
                "merge_poison_slots",
                "defer_ctor_checks",
                "defer_range_proofs",
                "defer_call_effect_checks",
                "defer_exit_check",
                "lazy_z3_scope",
                "finite_domain_enumeration",
                "witness_eval",
                "prefix_compact",
                "loop_fold_shapes",
            ]
            .contains(field)
            {
                "execution_limits.path_merge"
            } else {
                "execution_limits.path_merge.diagnostics"
            };
            let config = |value| -> ExecutionLimitsConfig {
                let text = format!("[{section}]\n{field}={value}");
                let table: toml::Value = text.parse().unwrap();
                table["execution_limits"].clone().try_into().unwrap()
            };
            let mut limits = config(false);
            cli(&mut limits, &[&format!("--{flag}=true")]).unwrap();
            assert_eq!(limits, config(true), "{flag}");
            cli(&mut limits, &[&format!("--{flag}=false")]).unwrap();
            assert_eq!(limits, config(false), "{flag}");
        }
    }

    #[test]
    fn region_options_poison_slots_require_path_merge_section_and_boolean() {
        for section in ["execution_limits", "execution_limits.solver", "execution_limits.path_merge.diagnostics"] {
            let value: toml::Value = format!("[{section}]\nmerge_poison_slots=true").parse().unwrap();
            assert!(value["execution_limits"].clone().try_into::<ExecutionLimitsConfig>().is_err());
        }
        let mut limits = ExecutionLimitsConfig::default();
        assert!(cli(&mut limits, &["--merge-poison-slots=yes"]).is_err());
        assert!(limits.path_merge.merge_poison_slots);
    }

    #[test]
    fn region_options_cli_lazy_scope_preserves_and_overrides_toml() {
        let value: toml::Value =
            "[execution_limits.path_merge]\nlazy_z3_scope=true\ndefer_exit_check=true".parse().unwrap();
        let mut limits: ExecutionLimitsConfig = value["execution_limits"].clone().try_into().unwrap();
        cli(&mut limits, &[]).unwrap();
        assert!(limits.path_merge.lazy_z3_scope);
        cli(&mut limits, &["--region-lazy-z3-scope=false"]).unwrap();
        assert!(!limits.path_merge.lazy_z3_scope);
        assert!(limits.path_merge.defer_exit_check, "CLI仅覆盖指定字段");
        let mut enabled = ExecutionLimitsConfig::default();
        cli(&mut enabled, &["--region-lazy-z3-scope=true"]).unwrap();
        assert!(enabled.path_merge.lazy_z3_scope);
        assert!(!enabled.path_merge.defer_exit_check);
        for value in ["1", "0", "TRUE", "", "yes"] {
            assert!(cli(&mut limits, &[&format!("--region-lazy-z3-scope={value}")]).is_err());
        }
    }

    #[test]
    fn region_options_cli_values_override_toml_and_validate() {
        let mut limits = ExecutionLimitsConfig::default();
        cli(
            &mut limits,
            &[
                "--region-bool-proof-rlimit=17",
                "--query-dump-sites=f@1,g@2",
                "--query-dump-dir=queries",
                "--same-context-sites=f@1",
                "--obligation-dump-dir=obligations",
            ],
        )
        .unwrap();
        assert_eq!(limits.solver.bool_proof_rlimit, 17);
        let options = RegionOptions::from_config(&limits);
        assert_eq!(options.query_dump_sites, ["f@1", "g@2"]);
        assert_eq!(options.same_context_sites, ["f@1"]);
        assert_eq!(options.query_dump_dir.as_deref(), Some(std::path::Path::new("queries")));
        assert_eq!(options.obligation_dump_dir.as_deref(), Some(std::path::Path::new("obligations")));
        cli(&mut limits, &["--region-bool-proof-rlimit=0", "--query-dump-sites=", "--same-context-sites="]).unwrap();
        assert_eq!(limits.solver.bool_proof_rlimit, 0);
        assert!(limits.path_merge.diagnostics.query_dump_sites.is_empty());
        for value in [
            "--region-defer-exit-check=1",
            "--region-bool-proof-rlimit=-1",
            "--region-bool-proof-rlimit=4294967296",
            "--query-dump-dir=",
            "--obligation-dump-dir=",
            "--query-dump-sites=a",
            "--query-dump-sites=a,,b",
            "--same-context-sites=a,b,c",
        ] {
            assert!(cli(&mut ExecutionLimitsConfig::default(), &[value]).is_err(), "{value}");
        }
    }
}

#[cfg(test)]
mod region_depth_tests {
    use super::*;
    #[test]
    fn region_depth_cli_overrides_toml_and_rejects_invalid() {
        let mut opts = getopts::Options::new();
        add_cli(&mut opts);
        let mut limits = ExecutionLimitsConfig::default();
        for (text, expected) in [("32", Some(32)), ("64", Some(64)), ("-1", None)] {
            apply_cli(&opts.parse(&[format!("--region-max-merge-depth={text}")]).unwrap(), &mut limits).unwrap();
            assert_eq!(isla_lib::config::RegionOptions::from_config(&limits).merge_depth_limit(), expected);
        }
        for text in ["0", "-2", "true", ""] {
            assert!(
                apply_cli(&opts.parse(&[format!("--region-max-merge-depth={text}")]).unwrap(), &mut limits).is_err()
            );
        }
    }
}

#[cfg(test)]
mod no_smt_port_tests {
    use super::*;
    use isla_lib::config::RegionOptions;

    fn parse(args: &[&str]) -> getopts::Matches {
        let mut opts = getopts::Options::new();
        add_cli(&mut opts);
        super::super::path_cache::Options::add_cli(&mut opts);
        opts.optopt("", "check-samples", "", "path");
        opts.parse(args).unwrap()
    }

    #[test]
    fn unknown_solver_policy_uses_only_solver_table_and_cli() {
        use isla_lib::config::PathFailureAction;
        let mut limits = ExecutionLimitsConfig::default();
        assert_eq!(limits.solver.on_unknown, PathFailureAction::Panic);
        let legacy = toml::from_str::<ExecutionLimitsConfig>("[solver]\non_unknown='error'").unwrap_err();
        assert!(legacy.to_string().contains("panic"), "{legacy}");
        let legacy_cli = apply_cli(&parse(&["--solver-on-unknown=error"]), &mut limits).unwrap_err();
        assert!(legacy_cli.contains("panic"), "{legacy_cli}");
        assert!(apply_cli(&parse(&["--solver-on-unknown=ignore"]), &mut limits).is_err());
        apply_cli(&parse(&["--solver-on-unknown=dead"]), &mut limits).unwrap();
        assert_eq!(limits.solver.on_unknown, PathFailureAction::Dead);
        assert!(toml::from_str::<ExecutionLimitsConfig>("[path_merge]\non_unknown='error'").is_err());
        assert!(toml::from_str::<ExecutionLimitsConfig>("[solver]\non_unknown='ignore'").is_err());
    }

    #[test]
    fn path_timeout_policy_uses_execution_limits_and_cli_override() {
        use isla_lib::config::PathFailureAction;
        assert_eq!(ExecutionLimitsConfig::default().on_path_timeout, PathFailureAction::Panic);
        let mut limits = toml::from_str::<ExecutionLimitsConfig>("on_path_timeout='dead'").unwrap();
        assert_eq!(limits.on_path_timeout, PathFailureAction::Dead);
        apply_cli(&parse(&["--on-path-timeout=panic"]), &mut limits).unwrap();
        assert_eq!(limits.on_path_timeout, PathFailureAction::Panic);
        assert_eq!(limits.solver.on_unknown, PathFailureAction::Panic);
        assert!(apply_cli(&parse(&["--on-path-timeout=ignore"]), &mut limits).is_err());
    }

    #[test]
    fn no_smt_cli_preserves_toml_and_supports_bare_and_false() {
        for (field, flag) in NO_SMT_OPTIONS {
            let text = if *field == "no_smt_keep_bool_proofs" {
                format!("no_smt=true\n{field}=true")
            } else {
                format!("{field}=true")
            };
            let value: toml::Value = format!("[execution_limits.solver]\n{text}").parse().unwrap();
            let toml: ExecutionLimitsConfig = value["execution_limits"].clone().try_into().unwrap();
            let mut limits = toml.clone();
            apply_cli(&parse(&[]), &mut limits).unwrap();
            assert_eq!(limits, toml);
            apply_cli(&parse(&[&format!("--{flag}=false")]), &mut limits).unwrap();
            let expected = if *field == "no_smt_keep_bool_proofs" {
                RegionOptions { no_smt: true, ..Default::default() }
            } else {
                RegionOptions::default()
            };
            assert_eq!(RegionOptions::from_config(&limits), expected);
            let args = if *field == "no_smt_keep_bool_proofs" {
                vec!["--no-smt", "--no-smt-keep-bool-proofs"]
            } else {
                vec![*flag]
            };
            let args: Vec<String> = args
                .into_iter()
                .map(|arg| if arg.starts_with("--") { arg.into() } else { format!("--{arg}") })
                .collect();
            let args: Vec<&str> = args.iter().map(String::as_str).collect();
            apply_cli(&parse(&args), &mut limits).unwrap();
            assert_eq!(limits, toml, "裸 flag 应恢复 TOML 的开关");
            assert!(apply_cli(&parse(&[&format!("--{flag}=1")]), &mut limits).is_err());
        }
    }

    #[test]
    fn no_smt_cli_rejects_conflicting_proofs_and_unsafe_modes() {
        for args in
            [vec!["--no-smt-keep-bool-proofs"], vec!["--no-smt", "--no-smt-keep-bool-proofs", "--skip-bool-proofs"]]
        {
            assert!(apply_cli(&parse(&args), &mut ExecutionLimitsConfig::default()).is_err());
        }
        let options = RegionOptions { no_smt: true, ..Default::default() };
        for args in [
            vec!["solve-state"],
            vec!["solve-state", "--path-cache-only"],
            vec!["fuzz", "--path-cache-only", "--path-cache-write=cache"],
            vec!["solve-state", "--path-cache-only", "--path-cache-write=cache", "--path-cache-read=old"],
            vec!["solve-state", "--path-cache-only", "--path-cache-write=cache", "--check-samples=x.jsonl"],
        ] {
            assert!(validate_no_smt_mode(&parse(&args), &options).is_err(), "{args:?}");
        }
        validate_no_smt_mode(&parse(&["solve-state", "--path-cache-only", "--path-cache-write=cache"]), &options)
            .unwrap();
    }
}
