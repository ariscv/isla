//! execution_limits.path_merge的路径合并开关；只覆盖 CLI 显式给出的字段。
use isla_lib::config::ExecutionLimitsConfig;

pub fn add_cli(opts: &mut getopts::Options) {
    opts.optopt("", "merge-strategy", "路径合并策略；默认 recursive", "recursive|flat");
    opts.optopt("", "ordered-events", "flat 保留事件偏序；默认 false", "true|false");
}

pub fn apply_cli(matches: &getopts::Matches, limits: &mut ExecutionLimitsConfig) -> Result<(), String> {
    if let Some(value) = matches.opt_str("merge-strategy") {
        limits.path_merge.strategy = Some(value.parse()?);
    }
    if let Some(value) = matches.opt_str("ordered-events") {
        limits.path_merge.ordered_events = Some(value.parse().map_err(|_| "--ordered-events 必须是 true 或 false")?);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::config::MergeStrategy;
    fn cli(limits: &mut ExecutionLimitsConfig, args: &[&str]) -> Result<(), String> {
        let mut opts = getopts::Options::new();
        add_cli(&mut opts);
        apply_cli(&opts.parse(args).unwrap(), limits)
    }
    #[test]
    fn path_merge_cli_defaults_preserve_toml_and_override() {
        let mut limits = ExecutionLimitsConfig::default();
        cli(&mut limits, &[]).unwrap();
        assert!(limits.path_merge.strategy.is_none() && limits.path_merge.ordered_events.is_none());
        cli(&mut limits, &["--merge-strategy=flat", "--ordered-events=true"]).unwrap();
        assert_eq!(limits.path_merge.strategy, Some(MergeStrategy::Flat));
        assert_eq!(limits.path_merge.ordered_events, Some(true));
        cli(&mut limits, &[]).unwrap();
        assert_eq!(limits.path_merge.ordered_events, Some(true));
        cli(&mut limits, &["--merge-strategy=recursive", "--ordered-events=false"]).unwrap();
        assert_eq!(limits.path_merge.strategy, Some(MergeStrategy::Recursive));
        assert_eq!(limits.path_merge.ordered_events, Some(false));
        assert!(limits.path_merge.regions.is_none());
        for args in [["--merge-strategy=bad"], ["--ordered-events=1"]] {
            assert!(cli(&mut limits, &args).is_err());
        }
    }
}
