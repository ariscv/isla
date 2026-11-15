use super::*;
use isla_lib::bitvector::b64::B64;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{smtlib, Config, Context, Model, SmtResult};

#[test]
fn reservation_state_is_symbolic_and_exported() {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    for valid_value in [false, true] {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let valid = symtab.intern("zreservation_valid");
        let addr = symtab.intern("zreservation_addr");
        let mut shared = SharedState::empty(symtab);
        shared.registers.insert(valid, Ty::Bool);
        shared.registers.insert(addr, Ty::Bits(48));
        let mut regs = RegisterBindings::new();
        regs.insert(valid, false, UVal::Init(Val::Bool(false)));
        regs.insert(addr, false, UVal::Init(Val::Bits(B64::new(0, 48))));
        let mut target = RV64::<B64>::default();
        target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new()).unwrap();
        let Val::Symbolic(valid_sym) = target.pre_state().get(&valid).unwrap() else {
            panic!("reservation_valid 必须主动符号化");
        };
        let Val::Symbolic(addr_sym) = target.pre_state().get(&addr).unwrap() else {
            panic!("reservation_addr 必须主动符号化");
        };
        assert_eq!(solver.length(*addr_sym), Some(48));
        solver.assert_eq(smtlib::Exp::Var(*valid_sym), smtlib::Exp::Bool(valid_value));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        // 不约束地址，验证必输出机制仍可给 judge 和 testcase 完整前态。
        let state = target.solve_pre_state(&mut Model::new(&solver), &shared).unwrap();
        assert!(state.contains_key("reservation_valid"));
        assert!(state.contains_key("reservation_addr"));
        assert!(target.must_output_register("reservation_valid"));
        assert!(RV32::<B64>::default().reg_list().contains(&"reservation_addr".to_string()));
    }
}

#[test]
fn reservation_set_size_rejects_invalid_platform_constants() {
    for size in [1, 64, 4096] {
        let config = format!("[const_primops]\nsys_reservation_set_size='{size} : %i64'").parse().unwrap();
        assert!(RiscvPlatformConfig::from_merged_toml(&config).is_ok());
    }
    for value in ["0 : %i64", "3 : %i64", "8192 : %i64", "-1 : %i64", "64 : %bv64", "undefined : %i64"] {
        let config = format!("[const_primops]\nsys_reservation_set_size='{value}'").parse().unwrap();
        assert!(RiscvPlatformConfig::from_merged_toml(&config).is_err(), "应拒绝集合大小 {value}");
    }
}
