// 在完整模型 IR 中执行普通 Sail helper，预期值来自独立 SoftFloat 参考。

use isla_lib::bitvector::b64::B64;
use isla_lib::bitvector::BV;
use isla_lib::config::{ISAConfig, Tool};
use isla_lib::executor::{execute_ir_function, Run};
use isla_lib::init::initialize_architecture;
use isla_lib::ir::{AssertionMode, IRTypeInfo, Name, Symtab, Val};
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::ir_parser::IrParser;
use isla_lib::primop_util::smt_value;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{configure_tastic, Event, Model, SmtResult, Tactic};
use isla_lib::source_loc::SourceLoc;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Mutex;

fn empty_tool() -> Tool {
    Tool { executable: PathBuf::new(), options: Vec::new() }
}

fn empty_config() -> ISAConfig<B64> {
    ISAConfig {
        pc: Name::from_u32(u32::MAX),
        register_event_sets: HashMap::new(),
        assembler: empty_tool(),
        objdump: empty_tool(),
        nm: empty_tool(),
        linker: empty_tool(),
        page_table_base: 0,
        page_size: 0,
        s2_page_table_base: 0,
        s2_page_size: 0,
        default_page_table_setup: String::new(),
        thread_base: 0,
        thread_top: 0,
        thread_stride: 0,
        symbolic_addr_base: 0,
        symbolic_addr_top: 0,
        symbolic_addr_stride: 0,
        default_registers: HashMap::new(),
        reset_registers: Vec::new(),
        reset_constraints: Vec::new(),
        const_primops: HashMap::new(),
        function_assumptions: Vec::new(),
        register_renames: HashMap::new(),
        ignored_registers: HashSet::new(),
        relaxed_registers: HashSet::new(),
        probes: HashSet::new(),
        probe_functions: HashSet::new(),
        trace_functions: HashSet::new(),
        translation_function: None,
        in_program_order: HashSet::new(),
        default_sizeof: 0,
        zero_announce_exit: false,
        memory_regions: None,
        page_table_config: None,
        pmp: None,
        clint_enabled: None,
        execution_limits: None,
    }
}

fn parse_hex(s: &str) -> u64 {
    u64::from_str_radix(s.strip_prefix("0x").unwrap_or(s), 16).unwrap()
}

fn main() {
    configure_tastic(Tactic::Qfaufbv);
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: isla-softfloat-legacy-regression WRAPPED_IR CASES");
    let ir = Box::leak(std::fs::read_to_string(&args[1]).unwrap().into_boxed_str());
    let mut symtab = Symtab::new();
    let definitions = IrParser::new().parse(&mut symtab, new_ir_lexer(ir)).expect("parse wrapped IR");
    let type_info = IRTypeInfo::new(&definitions);
    let definitions = Box::leak(definitions.into_boxed_slice());
    let mut config = empty_config();
    let input = std::fs::read_to_string(&args[2]).unwrap();
    let cases: Vec<_> = input.lines().filter(|line| !line.is_empty()).collect();
    for line in &cases {
        let name = line.split('\t').next().unwrap();
        config.trace_functions.insert(symtab.lookup(&format!("z{name}")));
    }
    let state = initialize_architecture(definitions, symtab, type_info, &config, AssertionMode::Optimistic, false);
    for (index, line) in cases.iter().enumerate() {
        let parts: Vec<_> = line.split('\t').collect();
        assert_eq!(parts.len(), 5, "bad case line {index}");
        let name = parts[0];
        let arguments: Vec<Val<B64>> = parts[1]
            .split(',')
            .map(|part| {
                let (width, value) = part.split_once(':').unwrap();
                let width: u32 = width.parse().unwrap();
                let value = parse_hex(value);
                if width == 1 {
                    Val::Bool(value != 0)
                } else {
                    Val::Bits(B64::new(value, width))
                }
            })
            .collect();
        let expected_flags = parse_hex(parts[2]);
        let expected_result = parse_hex(parts[3]);
        let expected_width: u32 = parts[4].parse().unwrap();
        let paths = Mutex::new(0usize);
        let wrapper = format!("zd_probe_{name}");
        let target = state.shared_state.symtab.lookup(&format!("z{name}"));
        execute_ir_function(
            &wrapper,
            &arguments,
            &state.shared_state,
            &state.regs,
            &state.lets,
            &paths,
            &|_, _, result, shared, mut solver, paths| {
                *paths.lock().unwrap() += 1;
                let value = match result {
                    Ok((Run::Finished(value), _)) => value,
                    Err((error, _)) => panic!("{index} {name}: execution failed: {error:?}"),
                    _ => panic!("{index} {name}: execution did not finish"),
                };
                assert!(
                    solver.trace().to_vec().iter().any(|event| {
                        matches!(event, Event::Function { name: called, call: true } if *called == target)
                    }),
                    "{index} {name}: missing ordinary body call event"
                );
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat, "{index} {name}: UNSAT");
                let concrete = Model::new(&solver).get_val(&value).expect("materialize result");
                let Val::Struct(symbolic_fields) = &value else { panic!("{index} {name}: expected symbolic tuple") };
                let mut ordered: Vec<_> = symbolic_fields.iter().collect();
                ordered.sort_by_key(|(field, _)| shared.symtab.to_str(**field));
                assert_eq!(ordered.len(), 2, "{index} {name}: tuple field count");
                let actual_flags = smt_value(ordered[0].1, SourceLoc::unknown()).expect("flags SMT expression");
                let actual_result = smt_value(ordered[1].1, SourceLoc::unknown()).expect("result SMT expression");
                let expected_result_exp = if expected_width == 1 {
                    Exp::Bool(expected_result != 0)
                } else {
                    Exp::Bits64(B64::new(expected_result, expected_width))
                };
                let mismatch = Exp::Or(
                    Box::new(Exp::Neq(Box::new(actual_flags), Box::new(Exp::Bits64(B64::new(expected_flags, 5))))),
                    Box::new(Exp::Neq(Box::new(actual_result), Box::new(expected_result_exp))),
                );
                assert_eq!(
                    solver.check_sat_with(&mismatch, SourceLoc::unknown()),
                    SmtResult::Unsat,
                    "{index} {name}: result or flags can differ"
                );
                let Val::Struct(fields) = concrete else { panic!("{index} {name}: expected tuple") };
                let mut flags = None;
                let mut result_bits = None;
                for item in fields.into_values() {
                    match item {
                        Val::Bits(bits) if bits.len() == 5 => flags = Some(bits.lower_u64()),
                        Val::Bits(bits) => result_bits = Some((bits.lower_u64(), bits.len())),
                        Val::Bool(value) => result_bits = Some((u64::from(value), 1)),
                        other => panic!("{index} {name}: unexpected result {other:?}"),
                    }
                }
                assert_eq!(flags, Some(expected_flags), "{index} {name}: flags");
                assert_eq!(result_bits, Some((expected_result, expected_width)), "{index} {name}: bits");
            },
        );
        assert_eq!(*paths.lock().unwrap(), 1, "{index} {name}: data path fork");
        println!("PASS {name}");
    }
    eprintln!("PASS {} legacy SoftFloat cases", cases.len());
}
