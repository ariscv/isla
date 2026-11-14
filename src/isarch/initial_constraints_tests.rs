//! 初态约束的等价证明；旧规则只作为测试参照保留。
use super::*;
use isla_lib::bitvector::b64::B64;
use isla_lib::ir::Def;
use isla_lib::smt::{Config, Context, Event, SmtResult};

struct LegacyDomain {
    supports_s: bool,
    supports_u: bool,
    supports_h: bool,
}
impl LegacyDomain {
    fn mpp_values(&self) -> Vec<u64> {
        vec![0, 1, 3]
    }
}

fn legacy_constraints(
    target: &mut RV64<B64>,
    lets: &Bindings<B64>,
    shared_state: &SharedState<B64>,
    solver: &mut Solver<B64>,
) -> Result<(), ExecError> {
    let symtab = &shared_state.symtab;
    let privilege = target.pre_state.get_from_str("cur_privilege", symtab);
    let mstatus = target.pre_state.get_from_str("mstatus", symtab);
    match (privilege, mstatus) {
        (Some(_), Some(_)) => {
            if integer_let_from_lets(lets, symtab, "xlen") != 64 {
                panic!("防御性编程：RV64 pre-state 的 let xlen 不是 64");
            }
            let domain = LegacyDomain { supports_s: true, supports_u: true, supports_h: false };

            let privilege_exp = smt_value(privilege.unwrap(), SourceLoc::unknown())?;
            let mut allowed = vec!["zMachine"];
            if domain.supports_s {
                allowed.push("zSupervisor");
            }
            if domain.supports_u {
                allowed.push("zUser");
            }
            if domain.supports_h && domain.supports_s {
                allowed.push("zVirtualSupervisor");
            }
            if domain.supports_h && domain.supports_u {
                allowed.push("zVirtualUser");
            }
            let allowed_exp = allowed
                .into_iter()
                .map(|member_name| {
                    let member = EnumMember::from_name(symtab.lookup(member_name), shared_state);
                    smtlib::Exp::Eq(Box::new(privilege_exp.clone()), Box::new(smtlib::Exp::Enum(member)))
                })
                .reduce(|lhs, rhs| smtlib::Exp::Or(Box::new(lhs), Box::new(rhs)))
                .unwrap();
            solver.assert(allowed_exp);

            let mut bits = mstatus.unwrap();
            let mstatus_exp = loop {
                match bits {
                    Val::Struct(fields) => {
                        if fields.len() != 1 {
                            panic!("防御性编程：mstatus 不是单字段 bitfield struct");
                        }
                        bits = fields.values().next().unwrap();
                    }
                    _ => break smt_value(bits, SourceLoc::unknown())?,
                }
            };
            for (high, low, enabled) in [(35, 34, domain.supports_s), (33, 32, domain.supports_u)] {
                solver.assert_eq(
                    smtlib::Exp::Extract(high, low, Box::new(mstatus_exp.clone())),
                    smtlib::bits64(if enabled { 2 } else { 0 }, 2),
                );
            }
            // 排除保留编码与未实现的 S 模式，同时保留现行 Sail 的 MPP=0 reset 初态。
            let mpp_exp = smtlib::Exp::Extract(12, 11, Box::new(mstatus_exp));
            let allowed_mpp = domain
                .mpp_values()
                .into_iter()
                .map(|value| smtlib::Exp::Eq(Box::new(mpp_exp.clone()), Box::new(smtlib::bits64(value, 2))))
                .reduce(|lhs, rhs| smtlib::Exp::Or(Box::new(lhs), Box::new(rhs)))
                .unwrap();
            solver.assert(allowed_mpp);
        }
        (None, None) => (),
        _ => panic!("防御性编程：RV64 cur_privilege 与 mstatus 必须同时存在于 pre-state"),
    }

    // RV64 的向量状态要求 vtype 与 vl 成对合法，因此从已符号化的 pre-state 中取出二者。
    let pre_state = target.pre_state();
    let (Some(vtype), Some(vl)) = (pre_state.get_from_str("vtype", symtab), pre_state.get_from_str("vl", symtab))
    else {
        return Ok(());
    };

    // Sail 可能用单字段结构包装寄存器值；逐层取出实际位向量后再构造 SMT 表达式。
    let mut vtype_value = vtype;
    let vtype_exp = loop {
        match vtype_value {
            Val::Struct(fields) => {
                if fields.len() != 1 {
                    panic!("防御性编程：向量上下文寄存器 vtype 的结构字段数为 {}，无法提取位向量", fields.len());
                }
                vtype_value = fields.values().next().expect("防御性编程：非空结构缺少字段值");
            }
            _ => break smt_value(vtype_value, SourceLoc::unknown())?,
        }
    };
    let mut vl_value = vl;
    let vl_exp = loop {
        match vl_value {
            Val::Struct(fields) => {
                if fields.len() != 1 {
                    panic!("防御性编程：向量上下文寄存器 vl 的结构字段数为 {}，无法提取位向量", fields.len());
                }
                vl_value = fields.values().next().expect("防御性编程：非空结构缺少字段值");
            }
            _ => break smt_value(vl_value, SourceLoc::unknown())?,
        }
    };

    // 枚举 RVV 允许的 SEW/LMUL 编码，先按 ELEN 排除会进入 vill 的组合，再根据 VLEN 计算 VLMAX。
    let vlen_bits = u64::from(
        u32::try_from(integer_let_from_lets(lets, symtab, "vlen"))
            .unwrap_or_else(|err| panic!("防御性编程：let vlen 不能作为 bitvector 宽度: {}", err)),
    );
    let elen_bits = u64::try_from(integer_let_from_lets(lets, symtab, "elen"))
        .unwrap_or_else(|err| panic!("防御性编程：let elen 不是有效的位宽: {}", err));
    let mut bounds = Vec::new();
    for vsew in 0_u64..=3 {
        let sew = 1_u64 << (vsew + 3);
        for vlmul in [0_u64, 1, 2, 3, 5, 6, 7] {
            let (lmul_numerator, lmul_denominator) = match vlmul {
                0..=3 => (1_u64 << vlmul, 1),
                5 => (1, 8),
                6 => (1, 4),
                7 => (1, 2),
                _ => panic!("防御性编程：非法的 LMUL 编码 {}", vlmul),
            };
            // Sail/RVV 要求 SEW <= LMUL * ELEN；交叉相乘以精确处理分数 LMUL。
            let sew_scaled = u128::from(sew) * u128::from(lmul_denominator);
            let elen_scaled = u128::from(elen_bits) * u128::from(lmul_numerator);
            if sew_scaled > elen_scaled {
                continue;
            }
            let numerator = vlen_bits * lmul_numerator;
            let denominator = sew * lmul_denominator;
            if numerator >= denominator {
                bounds.push(((vsew << 3) | vlmul, numerator / denominator));
            }
        }
    }

    // 普通状态要求 vtype 编码合法且 vl 不超过对应 VLMAX。
    let legal_vtype = bounds
        .into_iter()
        .map(|(vtype_low_bits, vlmax)| {
            smtlib::Exp::And(
                Box::new(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Bvand(Box::new(vtype_exp.clone()), Box::new(smtlib::bits64(0x3f, 64)))),
                    Box::new(smtlib::bits64(vtype_low_bits, 64)),
                )),
                Box::new(smtlib::Exp::Bvule(Box::new(vl_exp.clone()), Box::new(smtlib::bits64(vlmax, 64)))),
            )
        })
        .reduce(|lhs, rhs| smtlib::Exp::Or(Box::new(lhs), Box::new(rhs)))
        .expect("防御性编程：当前 VLEN 不支持任何合法的 SEW/LMUL 组合");
    let legal_context = smtlib::Exp::And(
        Box::new(smtlib::Exp::Bvule(Box::new(vtype_exp.clone()), Box::new(smtlib::bits64(0xff, 64)))),
        Box::new(legal_vtype),
    );
    // vill 状态只允许 vill 位置位，其余位为零，并要求 vl 同时为零。
    let vill_context = smtlib::Exp::And(
        Box::new(smtlib::Exp::Eq(Box::new(vtype_exp), Box::new(smtlib::bits64(1_u64 << 63, 64)))),
        Box::new(smtlib::Exp::Eq(Box::new(vl_exp), Box::new(smtlib::bits64(0, 64)))),
    );
    // 将两类合法状态的并集加入求解器，排除当前执行路径上的非法向量 pre-state。
    solver.assert(smtlib::Exp::Or(Box::new(legal_context), Box::new(vill_context)));

    Ok(())
}

fn prove_equivalence(vector: bool) {
    isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
    let mut symtab = Symtab::new();
    let defs: Vec<Def<Name, B64>> = isla_lib::ir_parser::IrParser::new()
        .parse(
            &mut symtab,
            isla_lib::ir_lexer::new_ir_lexer(
                r#"
enum zPrivilege { zUser, zVirtualUser, zSupervisor, zVirtualSupervisor, zMachine }
struct zMstatus { zbits: %bv64 }
struct zVtype { zbits: %bv64 }
register zcur_privilege : %enum zPrivilege
register zmstatus : %struct zMstatus
register zvtype : %struct zVtype
register zvl : %bv64
"#,
            ),
        )
        .unwrap();
    let xlen = symtab.intern("zxlen");
    let vlen = symtab.intern("zvlen");
    let elen = symtab.intern("zelen");
    let pc = symtab.intern("zPC");
    let types = IRTypeInfo::new(&defs);
    let mut shared = SharedState::empty(symtab);
    shared.type_info = types;
    for def in &defs {
        if let Def::Register(name, ty, _) = def {
            shared.registers.insert(*name, ty.clone());
        }
    }
    let mut lets = Bindings::default();
    for (name, value) in [(xlen, 64), (vlen, 128), (elen, 64)] {
        lets.insert(name, UVal::Init(Val::I64(value)));
    }
    let context = Context::new(Config::new());
    let mut solver = Solver::<B64>::new(&context);
    let mut target = RV64::default();
    let mut regs = RegisterBindings::new();
    let names = if vector { vec!["vtype", "vl"] } else { vec!["cur_privilege", "mstatus"] };
    for text in names {
        let name = shared.symtab.lookup(&zencode::encode(text));
        let value = symbolic(&shared.registers[&name], &shared, &mut solver, SourceLoc::unknown()).unwrap();
        target.pre_state.insert(name, value.clone());
        regs.insert(name, false, UVal::Init(value));
    }
    let cp = isla_lib::smt::checkpoint(&mut solver);
    legacy_constraints(&mut target, &lets, &shared, &mut solver).unwrap();
    let old = solver
        .trace()
        .to_vec()
        .into_iter()
        .filter_map(|event| match event {
            Event::Smt(smtlib::Def::Assert(exp), _, _) => Some(exp.clone()),
            _ => None,
        })
        .reduce(|a, b| smtlib::Exp::And(Box::new(a), Box::new(b)))
        .unwrap();
    // 同一组符号、两台求解器；分别检查新且非旧、旧且非新。
    let mut configured = Solver::from_checkpoint(&context, cp.clone());
    let source: toml::Value = include_str!("../../configs/riscv64_difftest.toml").parse().unwrap();
    let mut selected_config: toml::Value = r#"pc = "PC"
assembler = "as"
objdump = "objdump"
nm = "nm"
linker = "ld"
[mmu]
page_table_base = "0"
page_size = "4096"
s2_page_table_base = "0"
s2_page_size = "4096"
[threads]
base = "0"
top = "4096"
stride = "4096"
[symbolic_addrs]
base = "4096"
top = "8192"
stride = "16"
"#
    .parse()
    .unwrap();
    for section in ["constraints", "symbolic_registers"] {
        selected_config.as_table_mut().unwrap().insert(section.into(), source[section].clone());
    }
    assert_eq!(shared.symtab.to_str(pc), "zPC");
    let config = isla_lib::config::ISAConfig::<B64>::parse(
        &selected_config.to_string(),
        None,
        &shared.symtab,
        &shared.type_info,
    )
    .unwrap();
    if !vector {
        target.symbolic_csrs = config.symbolic_registers.clone();
        target.apply_symbolic_csrs_to_registers(&mut regs, &shared, &mut configured).unwrap();
    }
    let selected: Vec<_> = config
        .initial_constraints
        .into_iter()
        .filter(|exp| {
            let mut has_vector = false;
            let mut has_vstart = false;
            exp.map_var(&mut |loc| {
                if loc.id() == zencode::encode("vtype") {
                    has_vector = true;
                }
                if loc.id() == zencode::encode("vstart") {
                    has_vstart = true;
                }
                Ok::<_, String>(smtlib::Exp::<Sym>::Bool(true))
            })
            .unwrap();
            // 历史规则没有 vstart 域；这里只证明原有域的等价，新增域由配置全值测试覆盖。
            !has_vstart && has_vector == vector
        })
        .collect();
    regs.apply_constraints(&selected, &shared, &mut configured, SourceLoc::unknown()).unwrap();
    let new = configured
        .trace()
        .to_vec()
        .into_iter()
        .filter_map(|event| match event {
            Event::Smt(smtlib::Def::Assert(exp), _, _) => Some(exp.clone()),
            _ => None,
        })
        .reduce(|a, b| smtlib::Exp::And(Box::new(a), Box::new(b)))
        .unwrap();
    assert_eq!(
        configured.check_sat_with(&smtlib::Exp::Not(Box::new(old)), SourceLoc::unknown()),
        SmtResult::Unsat,
        "新约束必须蕴含旧规则"
    );
    assert_eq!(
        solver.check_sat_with(&smtlib::Exp::Not(Box::new(new)), SourceLoc::unknown()),
        SmtResult::Unsat,
        "旧规则必须蕴含新约束"
    );
}

#[test]
fn configured_domain_equivalent_to_legacy_rules() {
    prove_equivalence(false);
}
#[test]
fn configured_rvv_equivalent_to_legacy_rules() {
    prove_equivalence(true);
}
