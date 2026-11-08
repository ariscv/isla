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
    pub feedback: bool,
    pub difftest: Option<super::difftest::Config>,
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
            feedback: match matches.opt_str("fuzz-feedback").as_deref() {
                None | Some("coverage") => true,
                Some("none") => false,
                Some(_) => return Err("--fuzz-feedback 必须为 coverage 或 none".into()),
            },
            difftest: match matches.opt_str("executor").as_deref() {
                None | Some("model") => None,
                Some("difftest") => {
                    let base = std::env::var("DIFFTEST_XIANGSHAN_DIR")
                        .map(PathBuf::from)
                        .unwrap_or_else(|_| {
                            PathBuf::from(
                                "/data1/baiyifan/workplace/isla-runner/.worktree/replay-p0/difftest-xiangshan",
                            )
                        })
                        .parent()
                        .unwrap()
                        .join("output/ecfg4b");
                    let path = |name: &str, default: PathBuf| -> Result<PathBuf, String> {
                        let path = matches.opt_str(name).map(PathBuf::from).unwrap_or(default);
                        std::fs::canonicalize(&path).map_err(|error| format!("--{name}: {error}（{}）", path.display()))
                    };
                    let workers = matches
                        .opt_str("difftest-workers")
                        .unwrap_or_else(|| "8".into())
                        .parse::<usize>()
                        .map_err(|e| e.to_string())?;
                    let timeout = matches
                        .opt_str("difftest-timeout")
                        .unwrap_or_else(|| "120".into())
                        .parse::<u64>()
                        .map_err(|e| e.to_string())?;
                    if !(1..=12).contains(&workers) || !(1..=600).contains(&timeout) {
                        return Err("emu 并发数必须为 1..12，单例超时为 1..600 秒".into());
                    }
                    Some(super::difftest::Config {
                        worker: path(
                            "difftest-worker",
                            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tools/fuzz/paging_worker.py"),
                        )?,
                        profile: path("difftest-profile", base.join("profile.json"))?,
                        lock: path("difftest-lock", base.join("profile.lock.json"))?,
                        files: path("difftest-files", base.join("files.json"))?,
                        observer: path("difftest-observer", base.join("nemu_native_observer.so"))?,
                        output: PathBuf::from(required("fuzz-output")?).join("difftest"),
                        workers,
                        timeout,
                    })
                }
                Some(_) => return Err("--executor 必须为 model 或 difftest".into()),
            },
        };
        if options.difftest.is_some() && !matches!(options.mode, Mode::Campaign) {
            return Err("--executor difftest 仅用于 campaign".into());
        }
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
