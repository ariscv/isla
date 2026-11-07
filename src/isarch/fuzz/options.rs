//! 公共命令选项与模式约束。
use std::path::PathBuf;

#[derive(Clone, Debug)]
pub enum Mode {
    JudgeOnly,
    ReplayLog,
    Campaign,
}
#[derive(Clone, Debug)]
pub struct Options {
    pub mode: Mode,
    pub scenario: String,
    pub corpus: PathBuf,
    pub inputs: Option<PathBuf>,
    pub mutations: Option<PathBuf>,
    pub output: PathBuf,
    pub random_seed: u64,
    pub batch_size: usize,
    pub budget: usize,
    pub control_percent: usize,
    pub certify_all: bool,
}
impl Options {
    pub fn parse(matches: &getopts::Matches) -> Result<Self, String> {
        let mode = match matches.opt_str("fuzz-mode").as_deref() {
            Some("judge-only") => Mode::JudgeOnly,
            Some("replay-log") => Mode::ReplayLog,
            Some("campaign") => Mode::Campaign,
            _ => return Err("--fuzz-mode 必须是 judge-only、replay-log 或 campaign".into()),
        };
        let required = |name: &str| matches.opt_str(name).ok_or_else(|| format!("fuzz 需要 --{name}"));
        let options = Self {
            mode,
            scenario: required("fuzz-scenario")?,
            corpus: required("fuzz-corpus")?.into(),
            inputs: matches.opt_str("fuzz-inputs").map(Into::into),
            mutations: matches.opt_str("fuzz-mutations").map(Into::into),
            output: required("fuzz-output")?.into(),
            random_seed: matches
                .opt_str("fuzz-seed")
                .unwrap_or_else(|| "0".into())
                .parse()
                .map_err(|e| format!("随机数初值无效：{e}"))?,
            batch_size: matches
                .opt_str("fuzz-batch-size")
                .unwrap_or_else(|| "256".into())
                .parse()
                .map_err(|e| format!("批量大小无效：{e}"))?,
            budget: matches
                .opt_str("fuzz-budget")
                .unwrap_or_else(|| "2000".into())
                .parse()
                .map_err(|e| format!("预算无效：{e}"))?,
            control_percent: matches
                .opt_str("fuzz-control-percent")
                .unwrap_or_else(|| "5".into())
                .parse()
                .map_err(|e| format!("对照比例无效：{e}"))?,
            certify_all: matches.opt_present("fuzz-certify-all"),
        };
        if options.scenario.is_empty() || options.batch_size == 0 {
            return Err("场景 id 不得为空，批量大小必须大于零".into());
        }
        if options.budget == 0 || options.control_percent > 100 {
            return Err("预算必须大于零，对照百分比必须在 0 到 100 之间".into());
        }
        if matches!(options.mode, Mode::Campaign) && options.control_percent > 0 && options.mutations.is_none() {
            return Err(
                "campaign 的对照使用 replay-log 记录池，需要 --fuzz-mutations；纯路径引导可设 --fuzz-control-percent 0"
                    .into(),
            );
        }
        if matches!(options.mode, Mode::JudgeOnly) && options.inputs.is_none() {
            return Err("judge-only 需要 --fuzz-inputs mutants.jsonl".into());
        }
        if matches!(options.mode, Mode::ReplayLog) && options.mutations.is_none() {
            return Err("replay-log 需要 --fuzz-mutations mutations.json".into());
        }
        for flag in
            ["check-samples", "check-samples-judge", "judge-resident", "judge-resident-out", "judge-resident-fast"]
        {
            if matches.opt_present(flag) {
                return Err(format!("fuzz 不得与 --{flag} 同时使用"));
            }
        }
        Ok(options)
    }
}
