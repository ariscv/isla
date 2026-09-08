use std::collections::{BTreeMap, HashMap};

use isla_lib::bitvector::BV;
use isla_lib::config::{PmpConfig, PmpMode};
use isla_lib::error::ExecError;
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::{Bindings, IRTypeInfo, Name, SharedState, Symtab, Ty, UVal, Val};
use isla_lib::log;
use isla_lib::primop_util::{smt_value, symbolic};
use isla_lib::register::RegisterBindings;
use isla_lib::smt::Model;
use isla_lib::smt::{smtlib, Solver};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;

#[derive(Debug, Clone)]
pub struct PreStateCtx<B: BV> {
    map: HashMap<Name, Val<B>>,
}

impl<B: BV> PreStateCtx<B> {
    pub fn new() -> Self {
        PreStateCtx { map: HashMap::new() }
    }

    pub fn get(&self, name: &Name) -> Option<&Val<B>> {
        self.map.get(name)
    }

    pub fn get_from_str(&self, name_str: &str, symtab: &Symtab) -> Option<&Val<B>> {
        let name_zstr = zencode::encode(name_str);
        let name = symtab.get(&name_zstr)?;
        self.map.get(&name)
    }

    pub fn insert(&mut self, name: Name, value: Val<B>) -> Option<Val<B>> {
        self.map.insert(name, value)
    }

    pub fn insert_from_str(&mut self, name_str: &str, value: Val<B>, symtab: &Symtab) -> Option<Val<B>> {
        let name_zstr = zencode::encode(name_str);
        let name = symtab.get(&name_zstr)?;
        self.map.insert(name, value)
    }

    pub fn iter(&self) -> std::collections::hash_map::Iter<Name, Val<B>> {
        self.map.iter()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
}

pub trait Target<B: BV>
where
    Self: Sync,
{
    fn arch_name(&self) -> &'static str;
    fn xlen_name(&self) -> &'static str;
    fn xlen(&self) -> &'static str;

    fn arch_pretty_name(&self) -> &'static str {
        self.xlen_name()
    }

    fn reg_list(&self) -> Vec<String>;

    fn vector_context_registers(&self) -> &'static [&'static str] {
        &[]
    }

    fn setup_pre_state<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        // reg_list 是本次求解关注的寄存器集合；这里对集合中的每个寄存器建立独立的 pre-state 符号值。
        let reg_names = self.reg_list();
        // pre_state 保存这些符号值，供执行路径结束后的 solve_pre_state 从模型中取回。
        let pre_state = self.pre_state_mut();
        let symtab = &shared_state.symtab;
        for reg_name_str in reg_names.into_iter() {
            // 某些目标配置可能列出了当前 IR 中不存在的寄存器；这种寄存器不参与本次执行。
            let Some(name) = symtab.get(&zencode::encode(&reg_name_str)) else { continue };
            // shared_state.registers 是寄存器类型表。名称存在但不在类型表中说明 IR 内部不变量被破坏。
            let ty =
                shared_state.registers.get(&name).unwrap_or_else(|| panic!("防御性编程：{} 不是寄存器", reg_name_str));
            let recorded = match ty {
                // Sail 的 %bv 没有宽度信息；向量寄存器的宽度由已初始化的 let vlen 决定。
                Ty::AnyBits if is_vector_register_name(&reg_name_str) => {
                    let vlen = u32::try_from(integer_let_from_lets(lets, symtab, "vlen"))
                        .unwrap_or_else(|err| panic!("防御性编程：let vlen 不能作为 bitvector 宽度: {}", err));
                    let vector_ty = Ty::Bits(vlen);
                    symbolic(&vector_ty, shared_state, solver, SourceLoc::unknown()).unwrap_or_else(|err| {
                        panic!("防御性编程：寄存器 {} 无法符号化，类型 {:?}: {:?}", reg_name_str, vector_ty, err)
                    })
                }
                // 非向量 %bv 无法从当前上下文安全推断宽度，因此直接报告模型/配置错误。
                Ty::AnyBits => {
                    panic!("防御性编程：寄存器 {} 是 %bv，但不是已知可由 vlen 定宽的 vr* 寄存器", reg_name_str)
                }
                // 普通位向量、结构体、枚举等类型都按 IR 类型递归创建 fresh symbolic value。
                _ => symbolic(ty, shared_state, solver, SourceLoc::unknown()).unwrap_or_else(|err| {
                    panic!("防御性编程：寄存器 {} 无法符号化，类型 {:?}: {:?}", reg_name_str, ty, err)
                }),
            };
            // Poison 表示该类型不能表达为求解器值；这是不可恢复的内部错误。
            if matches!(recorded, Val::Poison) {
                panic!("防御性编程：寄存器 {} 的类型 {:?} 无法表示为符号值", reg_name_str, ty);
            }
            // 同一个符号值既覆盖执行帧中的寄存器，也记录到 pre_state，保证执行和输出使用同一变量。
            regs.assign(name, recorded.clone(), shared_state);
            pre_state.insert(name, recorded);
        }

        // 通用符号化完成后，再由具体 Target 为 pre-state 补充架构特有的合法性约束，例如向量 vtype/vl 配对。
        self.constrain_pre_state(lets, shared_state, solver)
    }

    // 默认没有额外约束；需要限制 pre-state 合法取值的架构自行覆写。
    fn constrain_pre_state<'ir>(
        &self,
        _: &Bindings<'ir, B>,
        _: &SharedState<'ir, B>,
        _: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        Ok(())
    }

    fn solve_pre_state<'state>(
        &self,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'state, B>,
    ) -> Result<BTreeMap<String, String>, ExecError> {
        let pre_state = self.pre_state();
        let symtab = &shared_state.symtab;
        let vector_context_registers = self.vector_context_registers();
        let mut result = BTreeMap::new();
        let mut arbitrary_vector_context_registers = Vec::new();
        for (name, val) in pre_state.iter() {
            let reg_name = zencode::decode(symtab.to_str(*name));
            // 将 pre_state 中的符号表达式用最终 SMT model 求值并转换为 ISA 状态字符串。
            match FmtVal::from_val(val, model) {
                Ok(fmt_val) => {
                    // 过滤未约束的符号变量（与历史提交 4639bd7 的 isa-state 打印过滤一致）：
                    // is_arbitrary 为真表示该 pre-state 符号在最终 model 中没有被任何约束定值
                    //（complete_model=false 下，z3 对从未出现在断言中的声明常量返回 Arbitrary）。
                    // 这类寄存器对当前指令路径没有实际约束，跳过不输出，避免 isa-state 被全 0
                    // 的 arbitrary 值淹没，只保留真正被符号执行约束过的 pre-state。
                    if fmt_val.is_arbitrary() {
                        if vector_context_registers.contains(&reg_name.as_str()) {
                            arbitrary_vector_context_registers.push((*name, val));
                        }
                        continue;
                    }
                    // 当前路径约束过的寄存器直接写入结果。
                    result.insert(reg_name, fmt_val.to_str(shared_state));
                }
                Err(e) => {
                    // SMT 错误需要向上传播；其他格式化失败只记录诊断并继续处理其他寄存器。
                    if matches!(e, ExecError::Smt(_)) {
                        return Err(e);
                    }
                    log!(log::PATH_RESULT, &format!("警告: pre-state 寄存器 {} 无法求解: {:?}", reg_name, e));
                }
            }
        }

        if !arbitrary_vector_context_registers.is_empty() {
            // 向量上下文即使未影响当前路径也必须输出，因此开启 complete model 补齐其具体值。
            model.set_complete_model(true);
            for (name, val) in arbitrary_vector_context_registers {
                let reg_name = zencode::decode(symtab.to_str(name));
                let fmt_val = FmtVal::from_val(val, model)?;
                if fmt_val.is_arbitrary() {
                    panic!("防御性编程：complete model 未能具化 V 上下文寄存器 {}", reg_name);
                }
                result.insert(reg_name, fmt_val.to_str(shared_state));
            }
        }

        Ok(result)
    }

    fn pre_state(&self) -> &PreStateCtx<B>;
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B>;
}

fn is_vector_register_name(reg_name: &str) -> bool {
    reg_name.strip_prefix("vr").is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
}

fn integer_let_from_lets<B: BV>(lets: &Bindings<B>, symtab: &Symtab, let_name: &str) -> i128 {
    let name =
        symtab.get(&zencode::encode(let_name)).unwrap_or_else(|| panic!("防御性编程：IR 中缺少 let {}", let_name));
    let value = lets.get(&name).unwrap_or_else(|| panic!("防御性编程：let {} 未初始化", let_name));
    match value {
        UVal::Init(Val::I64(value)) => *value as i128,
        UVal::Init(Val::I128(value)) => *value,
        UVal::Init(value) => panic!("防御性编程：let {} 不是整数值: {:?}", let_name, value),
        UVal::Uninit(ty) => panic!("防御性编程：let {} 仍未求值，类型 {:?}", let_name, ty),
    }
}

pub trait RISCV<B: BV>: Target<B> {
    fn pmp_symbolic(&self) -> bool;
    fn ppn_from_pa(&self, pa: u64) -> u64 {
        pa >> 12
    }

    fn pa_from_ppn(&self, ppn: u64) -> u64 {
        ppn << 12
    }

    // Page table constants (hardcoded defaults; override per-impl if needed)
    fn page_size(&self) -> u64 {
        4096
    }
    fn page_shift(&self) -> u64 {
        12
    }
    fn pte_size(&self) -> u64 {
        8
    }
    fn ptes_per_level(&self) -> u64 {
        512
    }
    fn page_table_size(&self) -> u64 {
        self.ptes_per_level() * self.pte_size()
    }
    fn pte_v(&self) -> u64 {
        1
    }
    fn pte_r(&self) -> u64 {
        2
    }
    fn pte_w(&self) -> u64 {
        4
    }
    fn pte_x(&self) -> u64 {
        8
    }
    fn pte_u(&self) -> u64 {
        16
    }
    fn pte_a(&self) -> u64 {
        64
    }
    fn pte_d(&self) -> u64 {
        128
    }
    fn vpn_bits(&self) -> u64 {
        9
    }
    fn sv39_levels(&self) -> u64 {
        3
    }
    fn sv48_levels(&self) -> u64 {
        4
    }

    fn apply_pmp_rules_to_config(
        &self,
        pmp_config: &PmpConfig,
        symtab: &Symtab,
        _type_info: &IRTypeInfo,
        default_registers: &mut HashMap<Name, Val<B>>,
    ) -> Result<(), String> {
        let mut pmpcfg_values = HashMap::<u32, u64>::new();

        for rule in &pmp_config.rules {
            let pmpaddr_value = match rule.mode {
                PmpMode::Tor | PmpMode::Na4 => rule.base >> 2,
                PmpMode::Napot => encode_napot(rule.base, rule.size.expect("NAPOT PMP rules require size")),
                _ => rule.base >> 2,
            };
            insert_register(
                symtab,
                default_registers,
                &format!("pmpaddr{}", rule.index),
                Val::I64(pmpaddr_value as i64),
            )?;

            let cfg_register = (rule.index / 8) * 2;
            let byte_offset = rule.index % 8;
            let cfg_byte = u64::from(encode_pmpcfg_byte(rule.mode, &rule.permissions, rule.locked));
            let entry = pmpcfg_values.entry(cfg_register).or_insert_with(|| {
                symtab
                    .get(&zencode::encode(&format!("pmpcfg{}", cfg_register)))
                    .and_then(|name| match default_registers.get(&name) {
                        Some(Val::I64(value)) => Some(*value as u64),
                        Some(Val::I128(value)) => Some(*value as u64),
                        _ => None,
                    })
                    .unwrap_or(0)
            });
            *entry &= !(0xff << (byte_offset * 8));
            *entry |= cfg_byte << (byte_offset * 8);
        }

        for (cfg_register, value) in pmpcfg_values {
            insert_register(symtab, default_registers, &format!("pmpcfg{}", cfg_register), Val::I64(value as i64))?;
        }

        Ok(())
    }

    fn apply_symbolic_pmp_to_registers<'ir>(
        &self,
        symtab: &Symtab,
        default_registers: &mut RegisterBindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        for index in 0..64 {
            let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
            insert_symbolic_register(
                symtab,
                default_registers,
                shared_state,
                &format!("pmpaddr{}", index),
                Val::Symbolic(sym),
            );
        }

        for index in 0..16 {
            let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
            insert_symbolic_register(
                symtab,
                default_registers,
                shared_state,
                &format!("pmpcfg{}", index),
                Val::Symbolic(sym),
            );
        }

        Ok(())
    }
}

pub struct RV32<B: BV> {
    pub pmp_symbolic: bool,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV32<B> {
    fn default() -> Self {
        RV32 { pmp_symbolic: false, pre_state: PreStateCtx::new() }
    }
}

impl<B: BV> Target<B> for RV32<B> {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv32"
    }
    fn xlen(&self) -> &'static str {
        "32"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("vl".to_string());
        regs.push("vstart".to_string());
        regs.push("vtype".to_string());
        regs.push("vcsr".to_string());
        regs
    }
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
}

impl<B: BV> RISCV<B> for RV32<B> {
    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
    }
}

pub struct RV64<B: BV> {
    pub pmp_symbolic: bool,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV64<B> {
    fn default() -> Self {
        RV64 { pmp_symbolic: false, pre_state: PreStateCtx::new() }
    }
}

impl<B: BV> Target<B> for RV64<B> {
    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (1..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        // regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("vl".to_string());
        regs.push("vstart".to_string());
        regs.push("vtype".to_string());
        regs.push("vcsr".to_string());
        regs
    }
    fn vector_context_registers(&self) -> &'static [&'static str] {
        &["vl", "vstart", "vtype", "vcsr"]
    }
    fn constrain_pre_state<'ir>(
        &self,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        // RV64 的向量状态要求 vtype 与 vl 成对合法，因此从已符号化的 pre-state 中取出二者。
        let pre_state = self.pre_state();
        let symtab = &shared_state.symtab;
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
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
}

impl<B: BV> RISCV<B> for RV64<B> {
    fn pmp_symbolic(&self) -> bool {
        self.pmp_symbolic
    }
}

impl<B: BV> RV64<B> {
    pub fn sv39_vpn_indices(&self, va: u64) -> [u64; 3] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF]
    }

    pub fn sv48_vpn_indices(&self, va: u64) -> [u64; 4] {
        [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF, (va >> 39) & 0x1FF]
    }
}

pub struct ARM<B: BV> {
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Target<B> for ARM<B> {
    fn arch_name(&self) -> &'static str {
        "aarch64"
    }
    fn xlen_name(&self) -> &'static str {
        "aarch64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn arch_pretty_name(&self) -> &'static str {
        "AArch64"
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
        regs.push("PC".to_string());
        regs
    }
    fn pre_state(&self) -> &PreStateCtx<B> {
        &self.pre_state
    }
    fn pre_state_mut(&mut self) -> &mut PreStateCtx<B> {
        &mut self.pre_state
    }
}
const PPN_MASK: u64 = 0xFFF_FFFF_FFF;

#[derive(Debug)]
pub struct RiscvPte {
    pub bits: u64,
}

impl RiscvPte {
    pub fn new(ppn: u64, flags: u64) -> Self {
        Self { bits: ((ppn & PPN_MASK) << 10) | (flags & 0xFF) }
    }

    pub fn ppn(&self) -> u64 {
        (self.bits >> 10) & PPN_MASK
    }

    pub fn flags(&self) -> u64 {
        self.bits & 0xFF
    }

    pub fn is_valid(&self) -> bool {
        self.bits & 1 != 0
    }

    pub fn has_read(&self) -> bool {
        self.bits & 2 != 0
    }

    pub fn has_write(&self) -> bool {
        self.bits & 4 != 0
    }

    pub fn has_execute(&self) -> bool {
        self.bits & 8 != 0
    }

    pub fn to_bytes(&self) -> [u8; 8] {
        self.bits.to_le_bytes()
    }
}

fn encode_napot(base: u64, size: u64) -> u64 {
    (base >> 2) | ((size >> 3) - 1)
}

fn encode_pmpcfg_byte(mode: PmpMode, permissions: &str, locked: bool) -> u8 {
    let mode_bits = match mode {
        PmpMode::Tor => 0b01,
        PmpMode::Na4 => 0b10,
        PmpMode::Napot => 0b11,
        _ => 0,
    };

    let mut cfg = 0u8;
    if permissions.contains('r') {
        cfg |= 1 << 0;
    }
    if permissions.contains('w') {
        cfg |= 1 << 1;
    }
    if permissions.contains('x') {
        cfg |= 1 << 2;
    }
    cfg |= mode_bits << 3;
    if locked {
        cfg |= 1 << 7;
    }
    cfg
}

fn insert_register<B: BV>(
    symtab: &Symtab,
    default_registers: &mut HashMap<Name, Val<B>>,
    register_name: &str,
    value: Val<B>,
) -> Result<(), String> {
    if let Some(name) = symtab.get(&zencode::encode(register_name)) {
        default_registers.insert(name, value);
        Ok(())
    } else {
        Err(format!("Could not find register {} when applying PMP configuration", register_name))
    }
}

fn insert_symbolic_register<'ir, B: BV>(
    symtab: &Symtab,
    default_registers: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    register_name: &str,
    value: Val<B>,
) {
    if let Some(name) = symtab.get(&zencode::encode(register_name)) {
        default_registers.assign(name, value, shared_state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::{Config, Context, SmtResult};

    fn rv64() -> RV64<B64> {
        RV64::default()
    }
    fn rv32() -> RV32<B64> {
        RV32::default()
    }
    #[test]
    fn pte_new_and_extract() {
        let pte = RiscvPte::new(0x1234, 0xF);
        assert_eq!(pte.ppn(), 0x1234);
        assert_eq!(pte.flags(), 0xF);
        assert!(pte.is_valid());
        assert!(pte.has_read());
        assert!(pte.has_write());
        assert!(pte.has_execute());
    }

    #[test]
    fn pte_flag_masks() {
        let pte = RiscvPte::new(0xFFFF_FFFF_FFFF, 0xFF);
        assert_eq!(pte.ppn(), 0xFFF_FFFF_FFF);
        assert_eq!(pte.flags(), 0xFF);
    }

    #[test]
    fn pte_not_valid() {
        let pte = RiscvPte::new(0, 0);
        assert!(!pte.is_valid());
        assert!(!pte.has_read());
        assert!(!pte.has_write());
        assert!(!pte.has_execute());
    }

    #[test]
    fn pte_individual_flags() {
        let r = rv64();
        let pte_v = RiscvPte::new(0, r.pte_v());
        assert!(pte_v.is_valid());
        assert!(!pte_v.has_read());

        let pte_r = RiscvPte::new(0, r.pte_r());
        assert!(!pte_r.is_valid());
        assert!(pte_r.has_read());

        let pte_w = RiscvPte::new(0, r.pte_w());
        assert!(pte_w.has_write());

        let pte_x = RiscvPte::new(0, r.pte_x());
        assert!(pte_x.has_execute());
    }

    #[test]
    fn pte_to_bytes_little_endian() {
        let pte = RiscvPte::new(0, 0x01);
        let bytes = pte.to_bytes();
        assert_eq!(bytes[0], 0x01);
        assert_eq!(bytes[1..], [0u8; 7]);
    }

    #[test]
    fn pte_roundtrip() {
        let r = rv64();
        let ppn = 0xABCD;
        let flags = r.pte_v() | r.pte_r() | r.pte_w() | r.pte_a() | r.pte_d();
        let pte = RiscvPte::new(ppn, flags);
        let reconstructed = RiscvPte::new(pte.ppn(), pte.flags());
        assert_eq!(pte.bits, reconstructed.bits);
    }

    #[test]
    fn sv39_vpn_indices_zero() {
        assert_eq!(rv64().sv39_vpn_indices(0), [0, 0, 0]);
    }

    #[test]
    fn sv39_vpn_indices_known() {
        let indices = rv64().sv39_vpn_indices(0x0400_0000);
        assert_eq!(indices[0], 0);
        assert_eq!(indices[1], 32);
        assert_eq!(indices[2], 0);
    }

    #[test]
    fn sv39_vpn_indices_max() {
        let va = (0x1FFu64 << 12) | (0x1FF << 21) | (0x1FF << 30);
        let indices = rv64().sv39_vpn_indices(va);
        assert_eq!(indices, [511, 511, 511]);
    }

    #[test]
    fn sv48_vpn_indices_zero() {
        assert_eq!(rv64().sv48_vpn_indices(0), [0, 0, 0, 0]);
    }

    #[test]
    fn sv48_vpn_indices_four_levels() {
        let va = (0x1u64 << 12) | (0x2u64 << 21) | (0x3u64 << 30) | (0x4u64 << 39);
        let indices = rv64().sv48_vpn_indices(va);
        assert_eq!(indices, [1, 2, 3, 4]);
    }

    #[test]
    fn ppn_pa_roundtrip() {
        let pa = 0x8000_1000u64;
        let rv64 = rv64();
        let ppn = rv64.ppn_from_pa(pa);
        assert_eq!(ppn, 0x8000_1);
        assert_eq!(rv64.pa_from_ppn(ppn), pa);
    }

    #[test]
    fn ppn_from_pa_strips_offset() {
        assert_eq!(rv64().ppn_from_pa(0x8000_1234), 0x8000_1);
    }

    #[test]
    fn pa_from_ppn_aligned() {
        let rv64 = rv64();
        let pa = rv64.pa_from_ppn(0x1234);
        assert_eq!(pa % rv64.page_size(), 0);
    }

    #[test]
    fn rv64_target_trait() {
        let target = rv64();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "64");
        assert_eq!(target.xlen_name(), "rv64");
        assert_eq!(target.vector_context_registers(), ["vl", "vstart", "vtype", "vcsr"]);
        // registers_of_interest 是 pre-state 与 post-state 的统一来源（全量并集）
        let regs = target.reg_list();
        assert!(regs.contains(&"x0".to_string()));
        assert!(regs.contains(&"PC".to_string()));
        assert!(regs.contains(&"vr0".to_string()));
        assert!(regs.contains(&"mstatus".to_string()));
        assert!(regs.contains(&"vtype".to_string()));
        assert!(regs.contains(&"vl".to_string()));
        assert!(regs.contains(&"vstart".to_string()));
        assert!(regs.contains(&"vcsr".to_string()));
        // pre-state 派生（setup_pre_state 内部）：排除 x0 和 PC（不做主动符号化）
        let pre_state: Vec<String> = regs.into_iter().filter(|r| r != "x0" && r != "PC").collect();
        assert!(!pre_state.contains(&"x0".to_string()));
        assert!(!pre_state.contains(&"PC".to_string()));
        assert!(pre_state.contains(&"vr0".to_string()));
        assert!(pre_state.contains(&"mstatus".to_string()));
        assert!(pre_state.contains(&"vtype".to_string()));
        assert!(pre_state.contains(&"vl".to_string()));
        assert!(pre_state.contains(&"vstart".to_string()));
        assert!(pre_state.contains(&"vcsr".to_string()));
    }

    #[test]
    fn rv32_target_trait() {
        let target = rv32();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "32");
        assert_eq!(target.xlen_name(), "rv32");
        assert!(target.vector_context_registers().is_empty());
        assert!(target.reg_list().contains(&"vtype".to_string()));
        assert!(target.reg_list().contains(&"vl".to_string()));
        assert!(target.reg_list().contains(&"vstart".to_string()));
        assert!(target.reg_list().contains(&"vcsr".to_string()));
    }

    #[test]
    fn setup_pre_state_resolves_vector_anybits_from_vlen() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let vr0_text = zencode::encode("vr0");
        let vlen_text = zencode::encode("vlen");
        let vr0_name = symtab.intern(&vr0_text);
        let vlen_name = symtab.intern(&vlen_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(vr0_name, Ty::AnyBits);
        let mut regs = RegisterBindings::new();
        let vr0_ty = Ty::AnyBits;
        regs.insert(vr0_name, false, UVal::Uninit(&vr0_ty));
        let mut lets = Bindings::default();
        lets.insert(vlen_name, UVal::Init(Val::I64(128)));
        let mut target = rv64();

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver).unwrap();

        let vr0 = match target.pre_state().get(&vr0_name).unwrap() {
            Val::Symbolic(sym) => *sym,
            value => panic!("防御性编程：vr0 未被符号化: {:?}", value),
        };
        assert_eq!(solver.length(vr0), Some(128));
    }

    #[test]
    fn setup_pre_state_overrides_initialized_non_anybits_register() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let mstatus_text = zencode::encode("mstatus");
        let mstatus_name = symtab.intern(&mstatus_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(mstatus_name, Ty::Bits(64));
        let mut regs = RegisterBindings::new();
        regs.insert(mstatus_name, false, UVal::Init(Val::Bits(B64::new(0x600, 64))));
        let lets = Bindings::default();
        let mut target = rv64();

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver).unwrap();

        let pre_state_symbol = match target.pre_state().get(&mstatus_name).unwrap() {
            Val::Symbolic(symbol) => *symbol,
            value => panic!("防御性编程：已初始化的 mstatus 未被主动符号化: {:?}", value),
        };
        let register_symbol = match regs.get_last_if_initialized(mstatus_name).unwrap() {
            Val::Symbolic(symbol) => *symbol,
            value => panic!("防御性编程：mstatus 寄存器未被符号值覆盖: {:?}", value),
        };
        assert_eq!(register_symbol, pre_state_symbol);
        assert_eq!(solver.length(pre_state_symbol), Some(64));
    }

    fn rv64_setup_pre_state_smt_result(vtype_value: u64, vl_value: u64) -> SmtResult {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let vtype_text = zencode::encode("vtype");
        let vl_text = zencode::encode("vl");
        let vlen_text = zencode::encode("vlen");
        let elen_text = zencode::encode("elen");
        let vtype_name = symtab.intern(&vtype_text);
        let vl_name = symtab.intern(&vl_text);
        let vlen_name = symtab.intern(&vlen_text);
        let elen_name = symtab.intern(&elen_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(vtype_name, Ty::Bits(64));
        shared_state.registers.insert(vl_name, Ty::Bits(64));
        let vtype_ty = Ty::Bits(64);
        let vl_ty = Ty::Bits(64);
        let mut regs = RegisterBindings::new();
        regs.insert(vtype_name, false, UVal::Uninit(&vtype_ty));
        regs.insert(vl_name, false, UVal::Uninit(&vl_ty));
        let mut lets = Bindings::default();
        lets.insert(vlen_name, UVal::Init(Val::I64(128)));
        lets.insert(elen_name, UVal::Init(Val::I64(64)));
        let mut target = rv64();

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver).unwrap();
        let vtype = match target.pre_state().get(&vtype_name).unwrap() {
            Val::Symbolic(sym) => *sym,
            value => panic!("防御性编程：vtype 未被符号化: {:?}", value),
        };
        let vl = match target.pre_state().get(&vl_name).unwrap() {
            Val::Symbolic(sym) => *sym,
            value => panic!("防御性编程：vl 未被符号化: {:?}", value),
        };
        solver.assert_eq(smtlib::Exp::Var(vtype), smtlib::bits64(vtype_value, 64));
        solver.assert_eq(smtlib::Exp::Var(vl), smtlib::bits64(vl_value, 64));
        solver.check_sat(SourceLoc::unknown())
    }

    #[test]
    fn vector_context_smt_constraint_accepts_only_legal_vtype_and_vl_pairs() {
        assert_eq!(rv64_setup_pre_state_smt_result(0, 16), SmtResult::Sat);
        assert_eq!(rv64_setup_pre_state_smt_result(0, 17), SmtResult::Unsat);
        assert_eq!(rv64_setup_pre_state_smt_result(0x17, 2), SmtResult::Sat);
        assert_eq!(rv64_setup_pre_state_smt_result(0x17, 3), SmtResult::Unsat);
        assert_eq!(rv64_setup_pre_state_smt_result(0x1f, 1), SmtResult::Unsat);
        assert_eq!(rv64_setup_pre_state_smt_result(0b10_0000, 0), SmtResult::Unsat);
        assert_eq!(rv64_setup_pre_state_smt_result(1_u64 << 63, 0), SmtResult::Sat);
        assert_eq!(rv64_setup_pre_state_smt_result(1_u64 << 63, 1), SmtResult::Unsat);
    }

    #[test]
    fn solve_pre_state_serializes_all_arbitrary_vector_context_registers() {
        let vector_context_registers = ["vl", "vstart", "vtype", "vcsr"];
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let mut target = rv64();
        let encoded_register_names: Vec<String> =
            vector_context_registers.iter().map(|register_name| zencode::encode(register_name)).collect();

        for encoded_register_name in &encoded_register_names {
            let register = symtab.intern(encoded_register_name);
            let value = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown()));
            target.pre_state.insert(register, value);
        }

        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        let state = target.solve_pre_state(&mut model, &shared_state).unwrap();

        assert_eq!(state.len(), vector_context_registers.len());
        for register_name in vector_context_registers {
            assert!(state.contains_key(register_name), "{} 必须被写入 isa-state", register_name);
        }
    }

    #[test]
    fn rv64_constants() {
        let r = rv64();
        assert_eq!(r.page_size(), 4096);
        assert_eq!(r.page_shift(), 12);
        assert_eq!(r.ptes_per_level(), 512);
        assert_eq!(r.page_table_size(), 512 * 8);
        assert_eq!(1u64 << r.page_shift(), r.page_size());
        assert_eq!(r.pte_v(), 1);
        assert_eq!(r.pte_r(), 2);
        assert_eq!(r.pte_w(), 4);
        assert_eq!(r.pte_x(), 8);
    }
}
