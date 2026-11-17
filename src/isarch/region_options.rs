//! 区域合并候选及诊断的 CLI 配置。
use isla_lib::config::ExecutionLimitsConfig;

const BOOL_OPTIONS: &[(&str, &str, &str)] = &[
    ("defer_exit_check", "region-defer-exit-check", "延迟区域出口检查；默认关闭"),
    ("lazy_z3_scope", "region-lazy-z3-scope", "延迟 Z3 条件作用域；默认关闭，仅在 defer 内生效，可能增加内存占用"),
    ("witness_eval", "region-witness-eval", "完整前提见证求值；默认关闭"),
    ("witness_shadow", "region-witness-shadow", "见证影子诊断；默认关闭"),
    ("witness_local_shadow", "region-witness-local-shadow", "局部见证补全影子诊断；默认关闭"),
    ("prefix_compact", "region-prefix-compact", "迭代边界前缀固化；默认关闭"),
    ("bool_proof_profile", "region-bool-proof-profile", "可选布尔证明资源统计；默认关闭"),
    ("progress", "region-progress", "区域步数和查询进度诊断；默认关闭"),
    ("native_snapshot", "region-native-snapshot", "原生查询快照；默认关闭"),
    ("call_census", "call-census", "有界函数调用统计；默认关闭"),
    ("probe_round_cost", "probe-round-cost", "逐轮成本分账；默认关闭"),
    ("probe_query_timings", "probe-query-timings", "有界逐查询计时；默认关闭"),
];

pub fn add_cli(opts: &mut getopts::Options) {
    for (_, flag, help) in BOOL_OPTIONS {
        opts.optopt("", flag, help, "true|false");
    }
    opts.optopt("", "region-bool-proof-rlimit", "可选布尔证明资源上限，0 不限；默认 0", "u32");
    opts.optopt("", "query-dump-sites", "查询导出位置；逗号分隔，空串清空", "sites");
    opts.optopt("", "same-context-sites", "同 Context 配对位置，最多两个；空串清空", "sites");
    opts.optopt("", "query-dump-dir", "查询 SMT2 导出目录", "path");
    opts.optopt("", "obligation-dump-dir", "断言义务诊断导出目录", "path");
}

pub fn apply_cli(matches: &getopts::Matches, limits: &mut ExecutionLimitsConfig) -> Result<(), String> {
    let mut options = limits.region_options.clone().unwrap_or_default();
    let mut changed = false;
    for (field, flag, _) in BOOL_OPTIONS {
        if let Some(value) = matches.opt_str(flag) {
            let value: bool = value.parse().map_err(|_| format!("--{flag} 必须是 true 或 false"))?;
            match *field {
                "defer_exit_check" => options.defer_exit_check = value,
                "lazy_z3_scope" => options.lazy_z3_scope = value,
                "witness_eval" => options.witness_eval = value,
                "witness_shadow" => options.witness_shadow = value,
                "witness_local_shadow" => options.witness_local_shadow = value,
                "prefix_compact" => options.prefix_compact = value,
                "bool_proof_profile" => options.bool_proof_profile = value,
                "progress" => options.progress = value,
                "native_snapshot" => options.native_snapshot = value,
                "call_census" => options.call_census = value,
                "probe_round_cost" => options.probe_round_cost = value,
                "probe_query_timings" => options.probe_query_timings = value,
                _ => unreachable!("区域 CLI 字段必须登记"),
            }
            changed = true;
        }
    }
    if let Some(value) = matches.opt_str("region-bool-proof-rlimit") {
        options.bool_proof_rlimit = value.parse().map_err(|_| "--region-bool-proof-rlimit 必须是非负32位整数")?;
        changed = true;
    }
    for flag in ["query-dump-sites", "same-context-sites"] {
        if let Some(value) = matches.opt_str(flag) {
            let sites = if value.is_empty() { Vec::new() } else { value.split(',').map(str::to_owned).collect() };
            match flag {
                "query-dump-sites" => options.query_dump_sites = sites,
                "same-context-sites" => options.same_context_sites = sites,
                _ => unreachable!(),
            }
            changed = true;
        }
    }
    for flag in ["query-dump-dir", "obligation-dump-dir"] {
        if let Some(value) = matches.opt_str(flag) {
            match flag {
                "query-dump-dir" => options.query_dump_dir = Some(value.into()),
                "obligation-dump-dir" => options.obligation_dump_dir = Some(value.into()),
                _ => unreachable!(),
            }
            changed = true;
        }
    }
    options.validate()?;
    if changed {
        limits.region_options = Some(options);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::config::{ExecutionLimitsConfig, RegionOptions};

    fn cli(config: &mut ExecutionLimitsConfig, args: &[&str]) -> Result<(), String> {
        let mut opts = getopts::Options::new();
        add_cli(&mut opts);
        apply_cli(&opts.parse(args).map_err(|e| e.to_string())?, config)
    }

    #[test]
    fn region_options_cli_defaults_and_boolean_overrides() {
        let mut limits = ExecutionLimitsConfig::default();
        cli(&mut limits, &[]).unwrap();
        assert!(limits.region_options.is_none());
        for (field, flag, _) in BOOL_OPTIONS {
            let toml: RegionOptions = toml::from_str(&format!("{field}=true")).unwrap();
            let mut enabled = ExecutionLimitsConfig::default();
            cli(&mut enabled, &[&format!("--{flag}=true")]).unwrap();
            assert_eq!(enabled.region_options, Some(toml.clone()), "{flag}");
            let mut limits = ExecutionLimitsConfig { region_options: Some(toml), ..Default::default() };
            cli(&mut limits, &[&format!("--{flag}=false")]).unwrap();
            assert_eq!(limits.region_options, Some(RegionOptions::default()), "{flag}");
        }
    }

    #[test]
    fn region_options_cli_lazy_scope_preserves_and_overrides_toml() {
        let options: RegionOptions = toml::from_str("lazy_z3_scope=true\ndefer_exit_check=true").unwrap();
        let mut limits = ExecutionLimitsConfig { region_options: Some(options), ..Default::default() };
        cli(&mut limits, &[]).unwrap();
        assert!(limits.region_options.as_ref().unwrap().lazy_z3_scope);
        cli(&mut limits, &["--region-lazy-z3-scope=false"]).unwrap();
        let options = limits.region_options.as_ref().unwrap();
        assert!(!options.lazy_z3_scope);
        assert!(options.defer_exit_check, "CLI 仅覆盖指定字段");
        let mut enabled = ExecutionLimitsConfig::default();
        cli(&mut enabled, &["--region-lazy-z3-scope=true"]).unwrap();
        let options = enabled.region_options.unwrap();
        assert!(options.lazy_z3_scope);
        assert!(!options.defer_exit_check, "仅 lazy 开启时静默无效，不报配置错误");
        for value in ["1", "0", "TRUE", "", "yes"] {
            assert!(cli(&mut limits, &[&format!("--region-lazy-z3-scope={value}")]).is_err(), "{value}");
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
        let options = limits.region_options.as_ref().unwrap();
        assert_eq!(options.bool_proof_rlimit, 17);
        assert_eq!(options.query_dump_sites, ["f@1", "g@2"]);
        assert_eq!(options.same_context_sites, ["f@1"]);
        assert_eq!(options.query_dump_dir.as_deref(), Some(std::path::Path::new("queries")));
        assert_eq!(options.obligation_dump_dir.as_deref(), Some(std::path::Path::new("obligations")));
        cli(&mut limits, &["--region-bool-proof-rlimit=0", "--query-dump-sites=", "--same-context-sites="]).unwrap();
        assert_eq!(limits.region_options.as_ref().unwrap().bool_proof_rlimit, 0);
        assert!(limits.region_options.as_ref().unwrap().query_dump_sites.is_empty());
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
