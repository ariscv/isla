//! property 的路径计数与诊断。性质判定沿用执行器的原收集器。
use std::collections::BTreeMap;
use std::fs::File;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use isla_lib::bitvector::BV;
use isla_lib::error::ExecError;
use isla_lib::executor::{self, LocalFrame, Run, Task, TaskId};
use isla_lib::ir::{SharedState, Val};
use isla_lib::smt::{smtlib::Exp, Event, SmtResult, Solver};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use serde::Serialize;

pub fn add_options(opts: &mut getopts::Options) {
    opts.optflag("", "path-merging", "启用区域路径合并，策略从 -C 读取");
    opts.optopt("", "expect-paths", "要求可满足的完成路径数恰好为指定值", "<N>");
    opts.optflag("", "print-paths", "打印完成路径数、守卫与返回值");
    opts.optopt("", "dump-paths", "将完成路径的守卫、返回值和合并记录数写入 JSON", "<文件>");
}

pub struct PathOptions {
    expected: Option<usize>,
    print: bool,
    dump: Option<PathBuf>,
}

impl PathOptions {
    pub fn parse(matches: &getopts::Matches) -> Result<Self, String> {
        Ok(Self {
            expected: matches
                .opt_str("expect-paths")
                .map(|value| value.parse())
                .transpose()
                .map_err(|error| format!("--expect-paths 需要非负整数：{error}"))?,
            print: matches.opt_present("print-paths"),
            dump: matches.opt_str("dump-paths").map(PathBuf::from),
        })
    }

    pub fn run<'ir, B: BV>(&self, threads: usize, task: Task<'ir, '_, B>, shared: &SharedState<'ir, B>) -> i32 {
        let (passed, path_status) = if self.expected.is_none() && !self.print && self.dump.is_none() {
            let result = Arc::new(AtomicBool::new(true));
            executor::start_multi(threads, None, vec![task], shared, result.clone(), &executor::all_unsat_collector);
            (result.load(Ordering::Acquire), 0)
        } else {
            let collected = Arc::new(PathResults {
                passed: AtomicBool::new(true),
                incomplete: AtomicBool::new(false),
                paths: Mutex::new(Vec::new()),
            });
            executor::start_multi(threads, None, vec![task], shared, collected.clone(), &collect_path);
            (collected.passed.load(Ordering::Acquire), self.report(&collected))
        };
        println!("{}", if passed { "ok" } else { "fail" });
        if path_status == 0 {
            i32::from(!passed)
        } else {
            path_status
        }
    }

    fn report(&self, collected: &PathResults) -> i32 {
        let mut paths = collected.paths.lock().unwrap();
        paths.sort_by(|a, b| (&a.guard_smtlib, &a.return_value).cmp(&(&b.guard_smtlib, &b.return_value)));
        let wrong_count = self.expected.is_some_and(|n| n != paths.len());
        let incomplete = collected.incomplete.load(Ordering::Acquire);
        println!("Paths: {}", paths.len());
        if self.print || wrong_count || incomplete {
            for (i, path) in paths.iter().enumerate() {
                println!(
                    "路径 {}，返回 {}，合并记录 {}\n{}",
                    i + 1,
                    path.return_value,
                    path.merge_records,
                    path.guard_smtlib.trim_end()
                );
            }
        }
        if wrong_count {
            eprintln!("期望 {} 条完成路径，实际 {} 条", self.expected.unwrap(), paths.len());
        }
        if incomplete {
            eprintln!("至少一条路径未完成或求解失败");
        }
        if let Some(file) = &self.dump {
            let result = File::create(file)
                .map_err(serde_json::Error::io)
                .and_then(|file| serde_json::to_writer_pretty(file, &*paths));
            if let Err(error) = result {
                eprintln!("无法写入路径 JSON {}：{error}", file.display());
                return 3;
            }
        }
        if incomplete {
            3
        } else if wrong_count {
            2
        } else {
            0
        }
    }
}

#[derive(Serialize)]
struct PathSummary {
    guard_smtlib: String,
    return_value: String,
    merge_records: usize,
    register_writes: BTreeMap<String, String>,
}

struct PathResults {
    passed: AtomicBool,
    incomplete: AtomicBool,
    paths: Mutex<Vec<PathSummary>>,
}

fn value_expression<B: BV>(value: &Val<B>, solver: &mut Solver<B>, shared: &SharedState<B>) -> String {
    match value {
        Val::Symbolic(sym) => solver.exp_to_str(&Exp::Var(*sym)),
        Val::Bits(bits) => solver.exp_to_str(&Exp::Bits(bits.to_vec())),
        _ => value.to_string(shared),
    }
}

fn collect_path<'ir, B: BV>(
    tid: usize,
    task_id: TaskId,
    result: Result<(Run<B>, LocalFrame<'ir, B>), (ExecError, LocalFrame<'ir, B>)>,
    shared: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    collected: &PathResults,
) {
    match &result {
        Ok((Run::Finished(value), frame)) => match solver.check_sat(SourceLoc::unknown()) {
            SmtResult::Sat => {
                let writes: Vec<_> = solver
                    .trace()
                    .to_vec()
                    .into_iter()
                    .filter_map(|event| match event {
                        Event::WriteReg(reg, accessors, value) if accessors.is_empty() => Some((*reg, value.clone())),
                        _ => None,
                    })
                    .collect();
                let mut register_writes = BTreeMap::new();
                for (reg, value) in writes {
                    let name = zencode::decode(shared.symtab.to_str(reg));
                    register_writes.entry(name).or_insert_with(|| value_expression(&value, &mut solver, shared));
                }
                let mut guard = Vec::new();
                solver.write_smtlib(&mut guard).unwrap();
                collected.paths.lock().unwrap().push(PathSummary {
                    guard_smtlib: String::from_utf8(guard).unwrap(),
                    return_value: value_expression(value, &mut solver, shared),
                    merge_records: frame.region_merge_records().len(),
                    register_writes,
                });
            }
            SmtResult::Unsat => (),
            SmtResult::Unknown => collected.incomplete.store(true, Ordering::Release),
            SmtResult::Error(error) => {
                eprintln!("路径求解失败：{error:?}");
                collected.incomplete.store(true, Ordering::Release);
            }
        },
        Ok((Run::Dead, _)) => (),
        Ok((Run::Exit | Run::Suspended { .. }, _)) => collected.incomplete.store(true, Ordering::Release),
        Err((error, _)) => {
            eprintln!("路径执行失败：{error:?}");
            collected.incomplete.store(true, Ordering::Release);
        }
    }
    // 收集器求解返回值的否定式。保存原守卫后再交给它。
    executor::all_unsat_collector(tid, task_id, result, shared, solver, &collected.passed);
}
