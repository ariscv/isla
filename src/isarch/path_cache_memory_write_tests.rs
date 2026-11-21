use super::*;
use crate::isarch::target::RV64;
use isla_lib::bitvector::b64::B64;
use isla_lib::executor::{samples::SamplePath, RegionMergeRecord};
use isla_lib::ir::{regions::RegionPoint, Symtab, Val, TOP_LEVEL_LET};
use isla_lib::smt::{
    checkpoint,
    smtlib::{Exp, Ty},
    Event, Model, SmtResult,
};
use isla_lib::source_loc::SourceLoc;

#[test]
fn guarded_memory_write_roundtrips_in_both_cache_encodings_and_judge() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let shared = SharedState::<B64>::empty(Symtab::new());
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let loc = SourceLoc::unknown();
    let guard = solver.declare_const(Ty::Bool, loc);
    let result = solver.declare_const(Ty::Bool, loc);
    let write = Event::WriteMem {
        value: result,
        write_kind: Val::Unit,
        address: Val::Bits(B64::new(0x1000, 64)),
        data: Val::Bits(B64::new(0xAA, 8)),
        bytes: 1,
        tag_value: None,
        opts: Default::default(),
        region: "ram",
    };
    solver.add_event(write.clone());
    let record = RegionMergeRecord {
        record_id: 0,
        parent_record: None,
        arm: "root",
        function: TOP_LEVEL_LET,
        branch_pc: 0,
        join: RegionPoint::FunctionExit,
        condition: guard,
        source_loc: loc,
        depth: 0,
        dead: false,
        value_symbols: Default::default(),
        input_symbols: Default::default(),
        single_arm_reads: Vec::new().into(),
        memory_reads: vec![(0, Exp::Var(guard), write.clone())].into(),
    };
    let paths = [ResidentPath {
        signature: 42,
        checkpoint: checkpoint(&mut solver),
        path: SamplePath {
            terminal: Default::default(),
            pre: [("input".into(), Val::Symbolic(guard))].into(),
            post: Default::default(),
            result: Val::Bool(true),
            memory: vec![write],
            memory_guards: [(0, Exp::Var(guard))].into(),
        },
        records: vec![record].into(),
        pure_definitions: vec![],
    }];
    let directory =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("output/guarded-write-cache-{}", std::process::id()));
    assert!(!directory.exists());
    let stages = Stages::new(None, Instant::now());
    save(
        &Options { write: Some(directory.clone()), format: vec![Encoding::Json, Encoding::Bin], ..Default::default() },
        "generic",
        &paths,
        &[Facts { guard_unique: true, post_unique: true, simple_pre: true }.into()],
        &shared,
        &RV64::default(),
        &crate::isarch::solve_summary::SolveSummary::default().json(),
        &json!({"command":[],"inputs":{},"binary":{"path":"fixture","sha256":"fixture"}}),
        &mut Timing::default(),
        &stages,
    );
    for encoding in [Encoding::Json, Encoding::Bin] {
        let restored = load_for_judge::<B64>(&directory, encoding, true, &shared, "generic", &stages);
        let [resident] = restored.paths.as_slice() else { panic!("应还原一条路径") };
        assert_eq!(restored.manifest.schema_version, CACHE_SCHEMA_VERSION);
        assert_eq!(resident.path.memory_guards, paths[0].path.memory_guards);
        assert!(resident.records[0].memory_reads[0].2.is_memory_write());
        let mut solver = Solver::from_checkpoint(&context, resident.checkpoint.clone());
        for active in [false, true] {
            let tx = solver.start_transaction();
            solver.assert(Exp::Eq(Box::new(Exp::Var(guard)), Box::new(Exp::Bool(active))));
            assert_eq!(solver.check_sat(loc), SmtResult::Sat);
            let sample = resident.path.materialize(&mut Model::new(&mut solver), &shared, "merge", 42, None).unwrap();
            solver.rollback_transaction(tx);
            assert_eq!(sample.post_memory.len(), usize::from(active));
            let judged = resident
                .path
                .judge(&mut solver, &shared, &sample, &resident.records, 42, |_, _| Ok(()))
                .unwrap()
                .expect("缓存还原后的写样本必须接纳");
            assert_eq!(judged.guard_vector, if active { "1" } else { "0" });
        }
    }
    fs::remove_dir_all(directory).unwrap();
}
