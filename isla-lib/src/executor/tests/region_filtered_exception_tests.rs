use super::*;
use crate::config::{ExecutionLimitsConfig, RegionOptions};
use crate::memory::Memory;

type Program = Vec<Instr<Name, B64>>;
const FILTERED: &str = "Error_internal_error";

struct Fixture {
    shared: SharedState<'static, B64>,
    program: Program,
    inputs: usize,
    register: Name,
}

impl Fixture {
    fn new(constructor: &str, nested: bool, both: bool) -> Self {
        let mut shared = empty_shared_state();
        shared.execution_stats = Arc::new(stats::ExecutionStats::new(true));
        let ctor = shared.symtab.intern(Box::leak(zencode::encode(constructor).into_boxed_str()));
        shared.type_info.union_ctors.insert(ctor);
        let register = shared.symtab.intern("zafter_throw");
        shared.registers.insert(register, Ty::Bool);
        let leaf = shared.symtab.intern("zthrow_leaf");
        let wrapper = shared.symtab.intern("zthrow_wrapper");
        let slot = test_name(999);
        let copy = |dest, exp| Instr::Copy(Loc::Id(dest), exp, info());
        let call = |dest, callee, args| Instr::Call(Loc::Id(dest), false, callee, args, info());
        let body = vec![
            Instr::Decl(slot, Ty::Union(SAIL_EXCEPTION), info()),
            call(slot, ctor, vec![Exp::String("fixture.sail:19: failed".into())]),
            copy(CURRENT_EXCEPTION, Exp::Id(slot)),
            copy(HAVE_EXCEPTION, Exp::Bool(true)),
            copy(register, Exp::Bool(true)),
            Instr::Arbitrary,
        ];
        shared.functions.insert(leaf, (Vec::new(), &Ty::Bool, Box::leak(body.into_boxed_slice())));
        let body = vec![
            call(RETURN, leaf, Vec::new()),
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 3, info()),
            Instr::End,
            Instr::Arbitrary,
        ];
        shared.functions.insert(wrapper, (Vec::new(), &Ty::Bool, Box::leak(body.into_boxed_slice())));
        let throw = || call(RETURN, wrapper, Vec::new());
        let program = if both {
            vec![Instr::Jump(input(0), 3, info()), throw(), Instr::Goto(4), throw(), Instr::Arbitrary]
        } else if nested {
            vec![
                Instr::Jump(input(0), 3, info()),
                copy(RETURN, Exp::Bool(false)),
                Instr::Goto(8),
                Instr::Jump(input(1), 6, info()),
                copy(RETURN, Exp::Bool(true)),
                Instr::Goto(8),
                throw(),
                Instr::Goto(8),
                Instr::Jump(Exp::Id(HAVE_EXCEPTION), 10, info()),
                Instr::End,
                Instr::Arbitrary,
            ]
        } else {
            vec![
                Instr::Jump(input(0), 3, info()),
                copy(RETURN, Exp::Bool(true)),
                Instr::Goto(4),
                throw(),
                Instr::Jump(Exp::Id(HAVE_EXCEPTION), 6, info()),
                Instr::End,
                Instr::Arbitrary,
            ]
        };
        Self { shared, program, inputs: if nested { 2 } else { 1 }, register }
    }

    fn limits(&self, merge: bool, names: &[&str]) -> ExecutionLimits {
        let config = ExecutionLimitsConfig {
            filter_model_exceptions: names.iter().map(|name| name.to_string()).collect(),
            ..Default::default()
        };
        ExecutionLimits::default()
            .with_config(&config, &self.shared.symtab)
            .with_path_merging(merge)
            .with_region_global_state(true)
            .with_region_loop_analysis(true)
    }

    fn run(&self, merge: bool, names: &[&str]) -> Vec<Path> {
        paths_with_state(
            self.program.clone(),
            &self.shared,
            self.inputs,
            self.limits(merge, names),
            Memory::new(),
            |_| (),
        )
    }

    fn after_throw_executed(&self, path: &Path) -> bool {
        path.events.iter().any(|event| matches!(event, Event::WriteReg(reg, ..) if *reg == self.register))
    }
}

#[test]
fn region_filtered_exception_stops_plain_and_nested_calls_at_throw() {
    let fixture = Fixture::new(FILTERED, false, false);
    let forked = fixture.run(false, &[]);
    assert_eq!(forked.len(), 2);
    let exception = forked.iter().find(|path| path.exception.is_some()).unwrap();
    assert!(fixture.after_throw_executed(exception));
    let filtered = fixture.run(false, &[FILTERED]);
    assert_eq!(filtered.len(), 1, "普通执行必须在 throw 处丢弃匹配异常");
    assert!(filtered[0].exception.is_none());
    assert!(!fixture.after_throw_executed(&filtered[0]));
    assert_eq!(fixture.shared.execution_stats.merge_json()["filtered_model_exception_paths_at_throw"], 1);

    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut frame = make_frame(fixture.program.clone());
    frame.vars_mut().insert(test_name(900), UVal::Init(Val::Bool(true)));
    frame.regs_mut().insert(fixture.register, false, UVal::Init(Val::Bool(false)));
    let state = TaskState::new().with_execution_limits(fixture.limits(false, &[FILTERED]));
    let output = Mutex::new(None);
    start_single(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        &fixture.shared,
        &output,
        &|_, _, result, _, solver, output| {
            let Ok((Run::Dead, frame)) = result else { panic!("匹配异常必须返回 Run::Dead") };
            assert_eq!(frame.function_name, fixture.shared.symtab.lookup("zthrow_leaf"));
            assert_eq!(frame.pc, 3, "返回前应停在 have_exception 赋值");
            assert_eq!(frame.backtrace.len(), 2, "调用者尚未恢复");
            assert!(!solver
                .trace()
                .to_vec()
                .iter()
                .any(|event| matches!(event, Event::WriteReg(reg, ..) if *reg == fixture.register)));
            *output.lock().unwrap() = Some(frame.pc);
        },
    );
    assert_eq!(output.into_inner().unwrap(), Some(3));
}

#[test]
fn region_filtered_exception_empty_and_unmatched_keep_rejection() {
    for (ctor, names) in [(FILTERED, vec![]), ("Error_other", vec![FILTERED])] {
        let fixture = Fixture::new(ctor, false, false);
        let paths = fixture.run(true, &names);
        assert_eq!(paths.len(), 2);
        assert!(paths.iter().all(|path| path.records.is_empty()));
        assert!(paths.iter().any(|path| path.exception.is_some() && fixture.after_throw_executed(path)));
        let rejections = fixture.shared.execution_stats.arm_unsupported_json(&fixture.shared.symtab);
        assert_eq!(rejections["top"][0]["reason"], "region_escaped");
    }
}

fn check_region() {
    for (nested, both, global) in
        [(false, false, true), (true, false, true), (false, true, true), (false, false, false)]
    {
        let fixture = Fixture::new(FILTERED, nested, both);
        let mut forked = fixture.run(false, &[]);
        let names = [FILTERED.to_owned()];
        forked.retain(|path| {
            path.exception
                .as_ref()
                .is_none_or(|exception| model_exception::filtered_site(&names, exception, &fixture.shared).is_none())
        });
        let merged = paths_with_state(
            fixture.program.clone(),
            &fixture.shared,
            fixture.inputs,
            fixture.limits(true, &[FILTERED]).with_region_global_state(global),
            Memory::new(),
            |_| (),
        );
        assert!(merged.iter().all(|path| path.exception.is_none()));
        assert_eq!(
            equivalent_paths(&forked, &merged, fixture.inputs, false),
            match (nested, both) {
                (_, true) => (0, 0),
                (true, _) => (2, 1),
                _ => (1, 1),
            }
        );
        assert!(merged.iter().all(|path| !fixture.after_throw_executed(path)));
        if let Some(path) = merged.first() {
            assert!(path.records.iter().any(|record| record.branch_pc == 0 && !record.dead));
            if nested {
                assert!(path.records.iter().any(|record| record.branch_pc == 3 && record.parent_record.is_some()));
            }
        }
        fixture.shared.execution_stats.print(&fixture.shared);
        assert_eq!(
            fixture.shared.execution_stats.merge_json()["filtered_model_exception_arms"],
            if both { 2 } else { 1 }
        );
    }
}

#[test]
fn region_filtered_exception_deferred_and_immediate() {
    let name = "executor::tests::region_merge_tests::filtered_exception_tests::region_filtered_exception_deferred_and_immediate";
    let args = ["--exact", name, "--nocapture", "--test-threads=1"];
    let actual: Vec<_> = std::env::args().skip(1).collect();
    if actual.starts_with(&args.map(str::to_owned)) {
        RegionOptions { defer_exit_check: actual.contains(&"--include-ignored".to_string()), ..Default::default() }
            .configure();
        stats::merge_diagnostics::configure("detail").unwrap();
        check_region();
        return;
    }
    for deferred in [false, true] {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap());
        child.args(args);
        if deferred {
            child.arg("--include-ignored");
        }
        let output = child.output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "defer={deferred}: {}\n{stderr}", String::from_utf8_lossy(&output.stdout));
        assert!(stderr.contains("\"kind\":\"filtered_model_exception_arm\""));
        assert!(stderr.contains("fixture.sail:19: failed"));
        assert!(stderr.contains("\"kind\":\"filtered_model_exception_summary\""));
    }
}
