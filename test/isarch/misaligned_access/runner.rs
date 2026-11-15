//! 使用真实 Sail IR 和 isarch 求解／judge；具体页表只用于定向回归。
use isla::isarch::{
    exec::{
        parse_fixed_prestate, solve_state_main, FixedInstruction, FixedSolveInputs, TimeoutReportConfig,
        TimeoutSmtOutput,
    },
    samples::SampleOptions,
    target::{Target, RV64},
    value_hints::RegionConfigInput,
};
use isla_lib::{
    bitvector::{b129::B129, BV},
    config::ISAConfig,
    executor::{execute_ir_function, Run},
    init::initialize_architecture,
    ir::{AssertionMode, Def, IRTypeInfo, Name, Symtab, Val},
    memory::{Memory, Region},
    smt::{configure_tastic, Tactic},
    tracetool::TraceOptions,
};
use std::{
    collections::HashMap,
    path::PathBuf,
    sync::{Arc, Mutex},
};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 7, "参数：IR 配置 场景 LOAD/STORE 宽度 export/judge/policy");
    let ir = PathBuf::from(&args[1]);
    let contents = Box::leak(std::fs::read_to_string(&ir).unwrap().into_boxed_str());
    let mut symtab = Symtab::new();
    let arch: &mut [Def<Name, B129>] = Box::leak(
        isla_lib::ir_parser::IrParser::new()
            .parse(&mut symtab, isla_lib::ir_lexer::new_ir_lexer(contents))
            .unwrap()
            .into_boxed_slice(),
    );
    let type_info = IRTypeInfo::new(arch);
    let config_text = std::fs::read_to_string(&args[2]).unwrap();
    let mut config = ISAConfig::parse(&config_text, None, &symtab, &type_info).unwrap();
    let mut target = RV64::default();
    target.configure_model(&config_text.parse().unwrap(), &symtab, &type_info, &mut config.default_registers).unwrap();
    configure_tastic(Tactic::Default);
    let mut state = initialize_architecture(arch, symtab, type_info, &config, AssertionMode::Optimistic, true);

    if args[6] == "policy" {
        let results = Mutex::new(Vec::new());
        execute_ir_function(
            "ztest_misaligned_access_policy",
            &[Val::Unit],
            &state.shared_state,
            &state.regs,
            &state.lets,
            &results,
            &|_, _, result, _, _, results| {
                results.lock().unwrap().push(matches!(result, Ok((Run::Finished(Val::Unit), _))));
            },
        );
        assert_eq!(*results.lock().unwrap(), vec![true]);
        println!("区域策略测试通过");
        return;
    }

    let scenario = args[3].as_str();
    let store = match args[4].as_str() {
        "LOAD" => false,
        "STORE" => true,
        _ => panic!("未知 clause"),
    };
    let width: u64 = args[5].parse().unwrap();
    let funct3 = match width {
        2 => 1,
        4 => 2,
        8 => 3,
        _ => panic!("仅验证 2/4/8 字节"),
    };
    let paged = matches!(scenario, "nc" | "io" | "pma-page" | "nc-hit" | "io-hit");
    let pbmt = match scenario {
        "nc" | "nc-hit" => 1,
        "io" | "io-hit" => 2,
        _ => 0,
    };
    let address: u64 = if paged {
        0x40000001
    } else if scenario == "device" {
        0x10000001
    } else {
        0x80000001
    };
    let pins = vec![
        format!("x1=0x{address:016x}"),
        "x2=0x8877665544332211".into(),
        "mstatus={bits=0x0000000a00000000}".into(),
        "misa={bits=0x800000000014112d}".into(),
        "menvcfg={bits=0x4000000000000000}".into(),
        "senvcfg={bits=0x0000000000000000}".into(),
        "mseccfg={bits=0x0000000000000000}".into(),
        format!("cur_privilege={}", if paged { "Supervisor" } else { "Machine" }),
        format!("satp=0x{:016x}", if paged { 0x8000000000080010u64 } else { 0 }),
    ];
    let pte = ((pbmt as u64) << 61) | (0x80000u64 << 10) | 0xcf;
    let prestate = parse_fixed_prestate(&pins, &state.shared_state, &state.regs, &state.lets).unwrap();
    if scenario.ends_with("-hit") {
        // 直接构造真实 IR 类型，避免为测试增加新的命令行值语法。
        let name = |text| state.shared_state.symtab.lookup(text);
        let bits = |value, width| Val::Bits(B129::new(value, width));
        let entry = Val::Struct(
            [
                (name("zasid"), bits(0, 16)),
                (name("zglobal"), Val::Bool(false)),
                (name("zvpn"), bits(0x40000, 45)),
                (name("zlevelMask"), bits(0x3ffff, 45)),
                (name("zppn"), bits(0x80000, 44)),
                (name("zpte"), bits(pte, 64)),
                (name("zpteAddr"), Val::Ctor(name("zPhysaddr"), Box::new(bits(0x80010008, 64)))),
            ]
            .into_iter()
            .collect(),
        );
        let mut entries = vec![Val::Ctor(name("zNonezIRTLB_EntryzK"), Box::new(Val::Unit)); 64];
        entries[0] = Val::Ctor(name("zSomezIRTLB_EntryzK"), Box::new(entry));
        state.regs.assign(name("ztlb"), Val::Vector(entries), &state.shared_state);
    }
    let instruction = if store {
        (2 << 20) | (1 << 15) | (funct3 << 12) | 0x23
    } else {
        (1 << 15) | (funct3 << 12) | (3 << 7) | 0x03
    };
    let fixed = FixedSolveInputs { instruction: Some(FixedInstruction { bits: instruction, width: 32 }), prestate };
    let mut memory = Memory::new();
    let mut bytes = HashMap::new();
    for (index, byte) in pte.to_le_bytes().iter().enumerate() {
        bytes.insert(0x80010008 + index as u64, *byte);
    }
    memory.add_region(Region::Concrete(0x80010000..0x80011000, Arc::new(bytes)));
    memory.add_zero_region(0x80000000..0x80001000);
    let mut samples = SampleOptions::default();
    match args[6].as_str() {
        "export" => std::env::set_var("ISLA_EXPORT_SAMPLES", "samples.jsonl"),
        "judge" => {
            std::env::remove_var("ISLA_EXPORT_SAMPLES");
            samples.check = Some("samples.jsonl".into());
            samples.report = Some("check.json".into());
            samples.judge = Some("judged.jsonl".into());
        }
        _ => panic!("未知模式"),
    }
    let pma_regions = target.platform.pma_regions.clone();
    assert!(solve_state_main(
        &state.shared_state,
        &state.regs,
        &state.lets,
        Some(memory),
        &mut target,
        &[args[4].clone()],
        &[],
        &[],
        false,
        TraceOptions::default(),
        Some(ir),
        2,
        Some(60),
        None,
        TimeoutReportConfig { output: TimeoutSmtOutput::new(true, false, false), directory: "smt-timeouts".into() },
        &fixed,
        &[],
        RegionConfigInput { pma_regions: pma_regions.as_deref(), memory_regions: None },
        &[],
        &samples
    ));
}
