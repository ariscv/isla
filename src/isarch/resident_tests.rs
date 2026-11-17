//! 使用真实 checkpoint、judge 和跨批计数验证恢复边界。
use super::*;
use isla_lib::bitvector::b64::B64;
use isla_lib::executor::samples::Sample;
use isla_lib::ir::{Symtab, Val};
use isla_lib::smt::{
    checkpoint,
    smtlib::{Exp, Ty},
    Model, SmtResult,
};
use isla_lib::source_loc::SourceLoc;

#[test]
fn resident_batch_options_validate_and_reach_session() {
    use super::super::samples::{SampleOptions, SampleSession};
    let options = SampleOptions { resident_batch_size: Some(0), ..Default::default() };
    assert!(options.validate().is_err());
    let options = SampleOptions { resident_batch_size: Some(2), ..Default::default() };
    assert!(options.validate().is_err());
    let mut options = SampleOptions {
        resident: Some("input".into()),
        resident_out: Some("output".into()),
        resident_batch_size: Some(2),
        resident_fast: true,
        ..Default::default()
    };
    assert!(options.validate().is_err());
    options.resident_fast = false;
    assert!(options.validate().is_ok());
    let session = SampleSession::new(&SampleOptions::default(), None).unwrap();
    assert_eq!(session.resident_batch_size, None);
    let dir = std::env::temp_dir().join(format!("resident-batch-options-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (_, samples) = fixture(false);
    let input = dir.join("input.jsonl");
    std::fs::write(&input, serde_json::to_vec(&samples[0]).unwrap()).unwrap();
    options.resident = Some(input);
    options.resident_out = Some(dir.join("output.jsonl"));
    let session = SampleSession::new(&options, None).unwrap();
    assert_eq!(session.resident_batch_size, Some(2));
    drop(session);
    std::fs::remove_dir_all(dir).unwrap();
}

fn fixture(duplicate: bool) -> (Vec<ResidentPath<B64>>, Vec<Sample>) {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let shared = SharedState::empty(Symtab::new());
    let mut paths = Vec::new();
    let mut samples = Vec::new();
    for signature in 0..4 {
        let mut solver = Solver::<B64>::new(&context);
        let x = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
        let guard = solver
            .define_const(Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(0, 8)))), SourceLoc::unknown());
        let records = vec![RegionMergeRecord {
            record_id: 7,
            parent_record: None,
            arm: "root",
            function: isla_lib::ir::TOP_LEVEL_LET,
            branch_pc: 0,
            join: isla_lib::ir::regions::RegionPoint::FunctionExit,
            condition: guard,
            source_loc: SourceLoc::unknown(),
            depth: 0,
            dead: false,
            value_symbols: Default::default(),
            input_symbols: Default::default(),
            single_arm_reads: Vec::new().into(),
            memory_reads: Vec::new().into(),
        }];
        let path = SamplePath {
            terminal: Default::default(),
            pre: BTreeMap::from([("x".into(), Val::Symbolic(x))]),
            post: BTreeMap::from([("x".into(), Val::Symbolic(x))]),
            result: Val::Symbolic(x),
            memory: vec![isla_lib::smt::Event::ReadMem {
                value: Val::Symbolic(x),
                read_kind: Val::Unit,
                address: Val::Bits(B64::new(0x80000000, 64)),
                bytes: 1,
                tag_value: None,
                opts: Default::default(),
                region: "resident-fixture",
            }],
            memory_guards: BTreeMap::new(),
        };
        let value = if duplicate && signature == 3 { 0 } else { signature };
        solver.assert(Exp::Eq(Box::new(Exp::Var(x)), Box::new(Exp::Bits64(B64::new(value, 8)))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        if signature == 0 {
            let sample = path.materialize(&mut Model::new(&solver), &shared, "fork", signature, None).unwrap();
            let mut rejected = sample.clone();
            rejected.sample_id = 1;
            rejected.pre_registers.insert("x".into(), json!({"bits":"11111111"}));
            samples = vec![sample, rejected];
        }
        paths.push(ResidentPath {
            checkpoint: checkpoint(&mut solver),
            path,
            records,
            signature,
            pure_definitions: Vec::new(),
        });
    }
    (paths, samples)
}

#[test]
fn resident_batches_preserve_rows_counts_and_solver_bound() {
    let shared = SharedState::empty(Symtab::new());
    let target = super::super::target::RV64::<B64>::default();
    let mut reference = None;
    for batch_size in [None, Some(1), Some(2), Some(4)] {
        let (paths, samples) = fixture(false);
        let output = std::env::temp_dir().join(format!("resident-batch-{}-{batch_size:?}.jsonl", std::process::id()));
        let checker = SampleChecker::new(samples).with_judge_output(&output).unwrap();
        let peak = run(paths, &checker, &shared, &target, 2, 0.0, false, batch_size);
        assert_eq!(peak, batch_size.unwrap_or(2));
        let report = checker.report();
        assert_eq!(report["samples"][0]["accepted_paths"], 1);
        assert_eq!(report["samples"][1]["accepted_paths"], 0);
        assert_eq!(report["unaccepted_sample_ids"], json!([1]));
        let bytes = std::fs::read(&output).unwrap();
        let row: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(row["guard_unique"], true);
        assert_eq!(row["post_unique"], true);
        assert_eq!(row["guard_vector"], "1");
        assert_eq!(row["sample"]["pre_memory"].as_array().unwrap().len(), 1);
        assert_eq!(row["sample"]["pre_memory"], row["sample"]["post_memory"]);
        if let Some(reference) = &reference {
            assert_eq!(&(report, bytes), reference);
        } else {
            reference = Some((report, bytes));
        }
        std::fs::remove_file(output).unwrap();
    }
}

#[test]
fn resident_batches_reject_overlap_across_batches() {
    let shared = SharedState::empty(Symtab::new());
    let target = super::super::target::RV64::<B64>::default();
    for batch_size in [1, 2, 4] {
        let (paths, samples) = fixture(true);
        let checker = SampleChecker::new(samples);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run(paths, &checker, &shared, &target, 2, 0.0, false, Some(batch_size));
        }));
        assert!(outcome.is_err(), "跨批重复接纳必须失败");
        assert_eq!(checker.report()["samples"][0]["accepted_paths"], 1);
    }
}
