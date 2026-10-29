// 在完整模型 IR 中执行普通 Sail helper，预期值来自独立 SoftFloat 参考。

use isla_lib::bitvector::b129::B129 as B64;
use isla_lib::bitvector::BV;
use isla_lib::config::{ISAConfig, Tool};
use isla_lib::executor::{execute_ir_function, Run};
use isla_lib::init::initialize_architecture;
use isla_lib::ir::{AssertionMode, IRTypeInfo, Name, SharedState, Symtab, UVal, Val};
use isla_lib::ir_lexer::new_ir_lexer;
use isla_lib::ir_parser::IrParser;
use isla_lib::primop_util::replace_mixed_bits;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::EnumMember;
use isla_lib::smt::{configure_tastic, Model, SmtResult, Tactic};
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
        initial_state: Vec::new(),
        initial_state_rv64_domain: false,
    }
}

fn bv(value: u64, width: u32) -> Val<B64> {
    Val::Bits(B64::new(value, width))
}
fn assign<'ir>(regs: &mut RegisterBindings<'ir, B64>, shared: &SharedState<'ir, B64>, name: &str, value: Val<B64>) {
    let id = shared.symtab.lookup(&format!("z{name}"));
    let value = if matches!(name, "fcsr" | "mstatus" | "vtype" | "vcsr") {
        Val::Struct([(shared.symtab.lookup("zbits"), value)].into_iter().collect())
    } else {
        value
    };
    regs.assign(id, value, shared);
}
fn enum_val(shared: &SharedState<B64>, name: &str) -> Val<B64> {
    Val::Enum(EnumMember::from_name(shared.symtab.lookup(name), shared))
}
fn main() {
    configure_tastic(Tactic::Qfaufbv);
    let args: Vec<_> = std::env::args().collect();
    let mut ir = std::fs::read_to_string(&args[1]).unwrap();
    if args[2] == "add" {
        ir.push_str("\nval zreview_add : (%bv3, %bv32, %bv32) -> %struct ztuplez3z5bv5_z5bv32\nfn zreview_add(zrm,za,zb) {\nreturn = zriscv_f32Add(zrm,za,zb);\nend;\n}\n");
    }
    if args[2] == "guard" {
        // F能力已在生成IR时折叠为true；隔离断言域，仅调整测试副本的Ext_F常量臂。
        let marker = "jump @neq(zExt_F, zmergez3var)";
        let start = ir.find(marker).expect("Ext_F能力臂");
        let next = ir[start..].find("zz40 = true").expect("Ext_F静态true");
        let at = start + next;
        ir.replace_range(at..at + "zz40 = true".len(), "zz40 = false");
    }
    let ir = Box::leak(ir.into_boxed_str());
    let mut symtab = Symtab::new();
    let defs = IrParser::new().parse(&mut symtab, new_ir_lexer(ir)).expect("IR");
    let types = IRTypeInfo::new(&defs);
    let config = if args[2] == "add" {
        empty_config()
    } else {
        ISAConfig::parse(&std::fs::read_to_string(&args[3]).unwrap(), None, &symtab, &types).expect("config")
    };
    let defs = Box::leak(defs.into_boxed_slice());
    let state = initialize_architecture(defs, symtab, types, &config, AssertionMode::Optimistic, false);
    let xlen = match state.lets.get(&state.shared_state.symtab.lookup("zxlen")).unwrap() {
        UVal::Init(Val::I64(value)) => *value,
        value => panic!("xlen必须是具体整数: {value:?}"),
    };
    assert!(xlen == 32 || xlen == 64);
    let dirty_status = (1_u64 << (xlen - 1)) | 0x6600;
    let mut failures = 0;
    if args[2] == "add" {
        let results = Mutex::new(Vec::new());
        execute_ir_function(
            "zreview_add",
            &[bv(0, 3), bv(0x3f800000, 32), bv(0x40000000, 32)],
            &state.shared_state,
            &state.regs,
            &state.lets,
            &results,
            &|_, _, result, _, mut solver, results| match result {
                Ok((Run::Finished(value), _)) => {
                    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                    let value = Model::new(&solver).get_val(&value).unwrap();
                    let Val::Struct(fields) = value else { panic!("tuple") };
                    let mut seen_flags = false;
                    let mut seen_result = false;
                    for val in fields.into_values() {
                        let Val::Bits(bits) = replace_mixed_bits(val, &mut solver, SourceLoc::unknown()).unwrap()
                        else {
                            panic!("bits")
                        };
                        if bits.len() == 5 {
                            assert_eq!(bits.lower_u64(), 0);
                            seen_flags = true;
                        } else {
                            assert_eq!(bits.len(), 32);
                            assert_eq!(bits.lower_u64(), 0x40400000);
                            seen_result = true;
                        }
                    }
                    assert!(seen_flags && seen_result);
                    results.lock().unwrap().push(true);
                    println!("PASS riscv_f32Add 1+2=3 flags=0");
                }
                Err((error, _)) => {
                    println!("FAIL riscv_f32Add {error:?}");
                    results.lock().unwrap().push(false);
                }
                Ok(_) => panic!("unfinished"),
            },
        );
        let results = results.into_inner().unwrap();
        if results != [true] {
            failures += 1;
        }
    } else if args[2] == "guard" {
        for fast in [false, true] {
            for getter in [false, true] {
                let mut regs = state.regs.clone();
                assign(&mut regs, &state.shared_state, "__isla_vector_fpr", Val::Bool(fast));
                let (function, values) =
                    if getter { ("zget_F_bits", vec![bv(0, 5)]) } else { ("zset_F_bits", vec![bv(0, 5), bv(0, 64)]) };
                let results = Mutex::new(Vec::new());
                execute_ir_function(
                    function,
                    &values,
                    &state.shared_state,
                    &regs,
                    &state.lets,
                    &results,
                    &|_, _, result, _, _, results| {
                        let pass = matches!(result, Err((isla_lib::error::ExecError::AssertionFailure(..), _)));
                        println!("{} guard {function} fast={fast}", if pass { "PASS" } else { "FAIL" });
                        results.lock().unwrap().push(pass);
                    },
                );
                if results.into_inner().unwrap() != [true] {
                    failures += 1;
                }
            }
        }
    } else if args[2] == "bf16" {
        let cases = [
            ("vl0", 0_u64, 0_u64, false, 0_u64, 0_u64),
            ("allmasked", 1, 0, true, 0, 0),
            ("vstart_ge_vl", 1, 1, false, 0, 0),
            ("active", 1, 0, false, 0, 16),
            ("oldflags_noactive", 0, 0, false, 1, 1),
            ("oldflags_active", 1, 0, false, 1, 17),
        ];
        for (label, vl, vstart, masked, old_flags, expected_flags) in cases {
            let mut regs = state.regs.clone();
            for i in 0..32 {
                assign(&mut regs, &state.shared_state, &format!("vr{i}"), bv(0, 128));
            }
            assign(&mut regs, &state.shared_state, "mstatus", bv(0x8000000000006600, 64));
            assign(&mut regs, &state.shared_state, "fcsr", bv(old_flags, 32));
            assign(&mut regs, &state.shared_state, "vtype", bv(8, 64));
            assign(&mut regs, &state.shared_state, "vl", bv(vl, 64));
            assign(&mut regs, &state.shared_state, "vstart", bv(vstart, 64));
            assign(&mut regs, &state.shared_state, "f1", bv(0xffffffffffff7f81, 64));
            let prefix = "ztuplez3z5bv1_z5bv5_z5bv5_z5bv5";
            let fields = [bv(u64::from(!masked), 1), bv(4, 5), bv(1, 5), bv(8, 5)];
            let fields = fields
                .into_iter()
                .enumerate()
                .map(|(i, val)| (state.shared_state.symtab.lookup(&format!("{prefix}{i}")), val))
                .collect();
            let ins = Val::Ctor(state.shared_state.symtab.lookup("zVFWMACCBF16_VF"), Box::new(Val::Struct(fields)));
            let results = Mutex::new(Vec::new());
            execute_ir_function(
                "zexecute",
                &[ins],
                &state.shared_state,
                &regs,
                &state.lets,
                &results,
                &|_, _, result, shared, mut solver, results| {
                    let (ret, frame) = match result {
                        Ok((Run::Finished(ret), frame)) => (ret, frame),
                        Err((error, _)) => {
                            println!("FAIL BF16 {label}: {error:?}");
                            results.lock().unwrap().push(false);
                            return;
                        }
                        Ok(_) => panic!("unfinished"),
                    };
                    assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                    let mut model = Model::new(&solver);
                    let value = frame.regs().get_last_if_initialized(shared.symtab.lookup("zfcsr")).unwrap();
                    let Val::Struct(fields) = value else { panic!("fcsr") };
                    let value = model.get_val(&fields[&shared.symtab.lookup("zbits")]).unwrap();
                    drop(model);
                    let Val::Bits(flags) = replace_mixed_bits(value, &mut solver, SourceLoc::unknown()).unwrap() else {
                        panic!("flags")
                    };
                    let retire = matches!(&ret,Val::Ctor(name,_) if *name==shared.symtab.lookup("zRetire_Success"));
                    let pass = retire && flags.lower_u64() == expected_flags;
                    println!(
                        "{} BF16 {label} ret={ret:?} flags={:#x} expected={expected_flags:#x}",
                        if pass { "PASS" } else { "FAIL" },
                        flags.lower_u64()
                    );
                    results.lock().unwrap().push(pass);
                },
            );
            if results.into_inner().unwrap() != [true] {
                failures += 1;
            }
        }
    } else {
        for fast in [false, true] {
            for fs in [1_u64, 2, 3] {
                for operation in ["get", "set", "execute"] {
                    for same in [false, true] {
                        let mut regs = state.regs.clone();
                        for i in 0..32 {
                            assign(&mut regs, &state.shared_state, &format!("f{i}"), bv(0x5a5a5a5a00000000 | i, 64));
                        }
                        assign(
                            &mut regs,
                            &state.shared_state,
                            "f0",
                            bv(if same { 0xffffffff40600000 } else { 0x5a5a5a5a00000000 }, 64),
                        );
                        assign(&mut regs, &state.shared_state, "__isla_vector_fpr", Val::Bool(fast));
                        assign(&mut regs, &state.shared_state, "mstatus", bv((fs << 13) | 0x600, 64));
                        assign(&mut regs, &state.shared_state, "fcsr", bv(0, 32));
                        assign(&mut regs, &state.shared_state, "f1", bv(0xffffffff3fc00000, 64));
                        assign(&mut regs, &state.shared_state, "f2", bv(0xffffffff40000000, 64));
                        let (function, values) = if operation == "execute" {
                            let prefix = "ztuplez3z5bv5_z5bv5_z5enumz0zzrounding_mode_z5bv5_z5enumz0zzf_bin_rm_op_S";
                            let fields = [
                                bv(2, 5),
                                bv(1, 5),
                                enum_val(&state.shared_state, "zRM_RNE"),
                                bv(0, 5),
                                enum_val(&state.shared_state, "zFADD_S"),
                            ];
                            let fields = fields
                                .into_iter()
                                .enumerate()
                                .map(|(i, val)| (state.shared_state.symtab.lookup(&format!("{prefix}{i}")), val))
                                .collect();
                            (
                                "zexecute",
                                vec![Val::Ctor(
                                    state.shared_state.symtab.lookup("zF_BIN_RM_TYPE_S"),
                                    Box::new(Val::Struct(fields)),
                                )],
                            )
                        } else if operation == "get" {
                            ("zget_F_bits", vec![bv(31, 5)])
                        } else {
                            ("zset_F_bits", vec![bv(0, 5), bv(0xffffffff40600000, 64)])
                        };
                        let results = Mutex::new(Vec::new());
                        execute_ir_function(
                            function,
                            &values,
                            &state.shared_state,
                            &regs,
                            &state.lets,
                            &results,
                            &|_, _, result, shared, mut solver, results| {
                                let (return_value, frame) = match result {
                                    Ok((Run::Finished(value), frame)) => (value, frame),
                                    Err((error, _)) => {
                                        println!("FAIL {function} fast={fast} FS={fs}: {error:?}");
                                        results.lock().unwrap().push(false);
                                        return;
                                    }
                                    Ok(_) => panic!("unfinished"),
                                };
                                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                                let mut model = Model::new(&solver);
                                let mut read = |name: &str| {
                                    let mut value = frame
                                        .regs()
                                        .get_last_if_initialized(shared.symtab.lookup(&format!("z{name}")))
                                        .unwrap();
                                    if let Val::Struct(fields) = value {
                                        value = fields.get(&shared.symtab.lookup("zbits")).unwrap();
                                    }
                                    match model.get_val(value).unwrap() {
                                        Val::Bits(bits) => bits.lower_u64(),
                                        Val::MixedBits(parts) => {
                                            let mut result = 0_u64;
                                            for part in parts {
                                                let isla_lib::ir::BitsSegment::Concrete(bits) = part else {
                                                    panic!("concrete segment")
                                                };
                                                result = if bits.len() == 64 {
                                                    bits.lower_u64()
                                                } else {
                                                    (result << bits.len()) | bits.lower_u64()
                                                };
                                            }
                                            result
                                        }
                                        _ => panic!("bits"),
                                    }
                                };
                                let f0 = read("f0");
                                let fcsr = read("fcsr");
                                let ms = read("mstatus");
                                let expected_f0 =
                                    if operation == "get" && !same { 0x5a5a5a5a00000000 } else { 0xffffffff40600000 };
                                let expected_ms = if operation == "get" { (fs << 13) | 0x600 } else { dirty_status };
                                let mut pass = f0 == expected_f0 && fcsr == 0 && ms == expected_ms;
                                for i in 1..32 {
                                    let expected = match i {
                                        1 => 0xffffffff3fc00000,
                                        2 => 0xffffffff40000000,
                                        _ => 0x5a5a5a5a00000000 | i,
                                    };
                                    pass &= read(&format!("f{i}")) == expected;
                                }
                                if operation == "get" {
                                    let Val::Bits(bits) = model.get_val(&return_value).unwrap() else {
                                        panic!("getter返回值")
                                    };
                                    pass &= bits.lower_u64() == 0x5a5a5a5a0000001f;
                                }
                                println!("{} {function} fast={fast} FS={fs} f0={f0:#018x} fcsr={fcsr:#x} mstatus={ms:#018x} expected={expected_ms:#018x} same={same}",if pass {"PASS"} else {"FAIL"});
                                results.lock().unwrap().push(pass);
                            },
                        );
                        if results.into_inner().unwrap() != [true] {
                            failures += 1;
                        }
                    }
                }
            }
        }
    }
    println!("failures={failures}");
    if failures > 0 {
        std::process::exit(1);
    }
}
