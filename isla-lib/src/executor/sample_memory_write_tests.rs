use super::*;
use crate::bitvector::b64::B64;
use crate::smt::{Config, Context};

#[test]
fn samples_guarded_overlapping_writes_feed_reads_and_preserve_initial_bytes() {
    use Exp::{Not, Var};
    crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let loc = SourceLoc::unknown();
    let guard = solver.declare_const(crate::smt::smtlib::Ty::Bool, loc);
    let written = solver.declare_const(crate::smt::smtlib::Ty::Bool, loc);
    let bits = |value, width| Val::Bits(B64::new(value, width));
    let write = |address, data, exclusive| Event::WriteMem {
        value: written,
        write_kind: Val::Unit,
        address: bits(address, 64),
        data: bits(data, 16),
        bytes: 2,
        tag_value: None,
        opts: if exclusive { crate::smt::WriteOpts::exclusive() } else { Default::default() },
        region: "ram",
    };
    let result = solver.declare_bitvector(32, loc);
    let path = SamplePath {
        terminal: Default::default(),
        pre: BTreeMap::from([("g".into(), Val::Symbolic(guard))]),
        post: BTreeMap::new(),
        result: Val::Symbolic(result),
        memory: vec![
            write(0x1000, 0x2211, false),
            write(0x1001, 0x4433, false),
            write(0x1000, 0xFFFF, true),
            Event::ReadMem {
                value: Val::Symbolic(result),
                read_kind: Val::Unit,
                address: bits(0x1000, 64),
                bytes: 4,
                tag_value: None,
                opts: Default::default(),
                region: "ram",
            },
        ],
        memory_guards: BTreeMap::from([(0, Var(guard)), (1, Var(guard)), (2, Not(Box::new(Var(guard))))]),
    };
    let shared = SharedState::empty(crate::ir::Symtab::new());
    solver.assert(Not(Box::new(Var(written))));
    for (direction, observed) in [(true, 0x55443311), (false, 0x55887766)] {
        let tx = solver.start_transaction_with_guard(Some(Exp::Bool(true)));
        solver.assert(Exp::Eq(Box::new(Var(guard)), Box::new(Exp::Bool(direction))));
        solver.assert(Exp::Eq(Box::new(Var(result)), Box::new(crate::smt::smtlib::bits64(observed, 32))));
        assert!(sat(&mut solver).unwrap());
        let sample = path.materialize(&mut Model::new(&mut solver), &shared, "merge", 1, None).unwrap();
        solver.rollback_transaction(tx);
        assert_eq!(sample.pre_memory.iter().filter(|cell| cell.value.is_some()).count(), if direction { 1 } else { 4 });
        assert_eq!(sample.post_memory[0].value, Some(observed as u8));
        assert_eq!(path.check(&mut solver, &shared, &sample).unwrap(), Some(true));
        assert!(path.judge(&mut solver, &shared, &sample, &[], 1, |_, _| Ok(())).unwrap().is_some());
    }
}
