use std::collections::{BTreeMap, HashMap, HashSet};

use isla_lib::bitvector::BV;
use isla_lib::config::{
    InitialRegisterConfig, PmaAttributes, PmaMisalignedFault, PmaRegionConfig, PmaReservability, PmaSize, PmpConfig,
    PmpMode, SymbolicRegisterConfig,
};
use isla_lib::error::ExecError;
use isla_lib::executor::{execute_ir_function, Run};
use isla_lib::fmtval::FmtVal;
use isla_lib::ir::{Bindings, IRTypeInfo, Name, SharedState, Symtab, Ty, UVal, Val};
use isla_lib::primop_util::{smt_value, symbolic};
use isla_lib::register::RegisterBindings;
use isla_lib::smt::Model;
use isla_lib::smt::{smtlib, EnumId, EnumMember, Event, SmtResult, Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use std::sync::Mutex;

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

    /// S2（W17）：含符号边界的 [[pma_regions]] 配置（仅符号路径非空；配置期无
    /// solver，注入推迟到 solve-state 启动，见
    /// apply_symbolic_pma_regions_to_registers）。默认无符号 PMA。
    fn symbolic_pma_regions(&self) -> &[PmaRegionConfig] {
        &[]
    }

    /// 注入期记录的 (region 名, 符号 zsizze 常量)，solve_pre_state 据此输出
    /// 边界模型值。默认无记录。
    fn symbolic_pma_sizes(&self) -> &[(String, Sym)] {
        &[]
    }

    /// 执行期注入入口持有 &mut target 时写入记录；不支持符号 PMA 的目标走到
    /// 这里是调用方 bug，直接 panic。
    fn symbolic_pma_sizes_mut(&mut self) -> &mut Vec<(String, Sym)> {
        panic!("防御性编程：该目标不支持符号 PMA 边界注入")
    }

    /// W21：`[symbolic_registers]` 声明的 CSR 符号化条目。配置期无 solver，
    /// 注入推迟到 solve-state 启动（apply_symbolic_csrs_to_registers）。
    fn symbolic_csrs(&self) -> &[SymbolicRegisterConfig] {
        &[]
    }

    /// W21：CSR 符号化注入（setup_pre_state 之后、checkpoint 之前）。对每个
    /// 声明的 CSR 按其 IR 类型声明 solver 符号常量、附加位级钉死断言
    /// `(sym & pin_mask) == pin_value`、位组非零域断言（组内按位或 != 0）与
    /// 派生位等价断言（W22：target 位 ⇔ OR(每组组内全 1)，双向），
    /// 然后覆盖执行帧寄存器并同步 pre_state 记录（沿用 setup_pre_state 的
    /// "执行与输出同一变量"约定）。只支持底层 64 位以内位向量的
    /// 平铺形状：`Ty::Bits(w)` 或单 `bits(w)` 字段的 struct（mstatus
    /// `struct zMstatus { zbits: %bv64 }` 即后者）；其余形状硬 panic。
    fn apply_symbolic_csrs_to_registers<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        let csrs: Vec<SymbolicRegisterConfig> = self.symbolic_csrs().to_vec();
        for csr in &csrs {
            let symtab = &shared_state.symtab;
            let name = symtab
                .get(&zencode::encode(&csr.name))
                .unwrap_or_else(|| panic!("防御性编程：符号化 CSR {} 不在当前 IR symtab", csr.name));
            let ty = shared_state
                .registers
                .get(&name)
                .unwrap_or_else(|| panic!("防御性编程：符号化 CSR {} 不是寄存器", csr.name));
            // 平铺形状解包：struct{bits(w)} 与 bits(w) 统一到 (宽度, 包装字段名)
            let (width, wrap_field) = match ty {
                Ty::Bits(width) => (*width, None),
                Ty::Struct(struct_id) => {
                    let struct_def = shared_state.type_info.structs.get(struct_id).unwrap_or_else(|| {
                        panic!("防御性编程：符号化 CSR {} 的 struct {:?} 缺类型定义", csr.name, struct_id)
                    });
                    if struct_def.len() != 1 {
                        panic!(
                            "防御性编程：符号化 CSR {} 的 struct 有 {} 个字段，只支持单 bits 字段平铺形状",
                            csr.name,
                            struct_def.len()
                        );
                    }
                    let (field_name, field_ty) = struct_def.iter().next().expect("防御性编程：非空 struct 缺首字段");
                    match field_ty {
                        Ty::Bits(width) => (*width, Some(*field_name)),
                        other => panic!("防御性编程：符号化 CSR {} 的唯一字段类型 {:?} 不是位向量", csr.name, other),
                    }
                }
                other => panic!(
                    "防御性编程：符号化 CSR {} 的类型 {:?} 不支持（只支持 bits(w) 或单 bits 字段 struct）",
                    csr.name, other
                ),
            };
            if width == 0 || width > 64 {
                panic!("防御性编程：符号化 CSR {} 宽度 {} 超出 (0, 64] 支持范围", csr.name, width);
            }
            if width < 64 && csr.pin_mask >> width != 0 {
                panic!(
                    "防御性编程：符号化 CSR {} 的 pin_mask 0x{:x} 含超出 {} 位宽的钉死位",
                    csr.name, csr.pin_mask, width
                );
            }
            // setup_pre_state 已为同名寄存器建立符号值，并可能附加 initial_state
            // 位约束。这里复用该符号，避免 CSR 配置把位约束留在已废弃的变量上。
            let existing = self.pre_state().get(&name);
            let existing_bits = match existing {
                Some(Val::Struct(fields)) if fields.len() == 1 => fields.values().next(),
                value => value,
            };
            let sym = match existing_bits {
                Some(Val::Symbolic(sym)) => {
                    assert_eq!(solver.length(*sym), Some(width), "CSR 与初态符号位宽必须一致");
                    *sym
                }
                Some(other) => {
                    return Err(ExecError::Type(
                        format!("符号化 CSR {} 与具体初态 {:?} 冲突", csr.name, other),
                        SourceLoc::unknown(),
                    ));
                }
                None => solver.declare_const(smtlib::Ty::BitVec(width), SourceLoc::unknown()),
            };
            if csr.pin_mask != 0 {
                solver.assert(smtlib::Exp::Eq(
                    Box::new(smtlib::Exp::Bvand(
                        Box::new(smtlib::Exp::Var(sym)),
                        Box::new(smtlib::bits64(csr.pin_mask, width)),
                    )),
                    Box::new(smtlib::bits64(csr.pin_value, width)),
                ));
            }
            for group in &csr.nonzero_groups {
                for &bit in group {
                    if bit >= width {
                        panic!("防御性编程：符号化 CSR {} 的 nonzero 组位 {} 超出 {} 位宽", csr.name, bit, width);
                    }
                }
                let or_exp = group
                    .iter()
                    .map(|&bit| smtlib::Exp::Extract(bit, bit, Box::new(smtlib::Exp::Var(sym))))
                    .reduce(|lhs, rhs| smtlib::Exp::Bvor(Box::new(lhs), Box::new(rhs)))
                    .expect("防御性编程：配置解析已拒绝空 nonzero 组");
                solver.assert(smtlib::Exp::Not(Box::new(smtlib::Exp::Eq(
                    Box::new(or_exp),
                    Box::new(smtlib::bits64(0, 1)),
                ))));
            }
            // W22：派生位等价约束（双向，非单向蕴含）：
            //   target 位 == OR(每组组内 AND 全 1)
            // 任一组全 1 则 target 必 1，target 为 1 则必有某组全 1。用于只读
            // 镜像位（mstatus.SD ⇔ FS=11 ∨ VS=11 ∨ XS=11）：钉 0 与位组自由
            // 取值矛盾，等价约束保持模型值架构自洽（重放侧 WARL 同一投影）。
            if let Some(derive) = &csr.derive_bit {
                if derive.bit >= width {
                    panic!("防御性编程：符号化 CSR {} 的派生位 {} 超出 {} 位宽", csr.name, derive.bit, width);
                }
                for group in &derive.groups {
                    for &bit in group {
                        if bit >= width {
                            panic!("防御性编程：符号化 CSR {} 的派生组位 {} 超出 {} 位宽", csr.name, bit, width);
                        }
                    }
                }
                let target_exp = smtlib::Exp::Extract(derive.bit, derive.bit, Box::new(smtlib::Exp::Var(sym)));
                let or_exp = derive
                    .groups
                    .iter()
                    .map(|group| {
                        group
                            .iter()
                            .map(|&bit| smtlib::Exp::Extract(bit, bit, Box::new(smtlib::Exp::Var(sym))))
                            .reduce(|lhs, rhs| smtlib::Exp::Bvand(Box::new(lhs), Box::new(rhs)))
                            .expect("防御性编程：配置解析已拒绝空派生组")
                    })
                    .reduce(|lhs, rhs| smtlib::Exp::Bvor(Box::new(lhs), Box::new(rhs)))
                    .expect("防御性编程：配置解析已拒绝空派生 groups");
                solver.assert(smtlib::Exp::Eq(Box::new(target_exp), Box::new(or_exp)));
            }
            let value = match wrap_field {
                Some(field_name) => {
                    let mut fields: ahash::HashMap<Name, Val<B>> =
                        HashMap::with_capacity_and_hasher(1, ahash::RandomState::new());
                    fields.insert(field_name, Val::Symbolic(sym));
                    Val::Struct(fields)
                }
                None => Val::Symbolic(sym),
            };
            regs.assign(name, value.clone(), shared_state);
            self.pre_state_mut().insert(name, value);
        }
        Ok(())
    }

    /// W21：物化阶段的 encdec/assembly 门按具体 CSR 值评估（try_get_assembly_*
    /// 用独立 solver 执行 zencdec/zassembly，符号 CSR 必须先按当前路径模型
    /// 具体化，否则门会一直读到 defaults 的旧具体值或让守卫在门外 fork）。
    /// 克隆寄存器表并把每个符号 CSR 替换为其模型值。
    fn concretize_symbolic_csrs<'ir>(
        &self,
        regs: &RegisterBindings<'ir, B>,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'ir, B>,
    ) -> Result<RegisterBindings<'ir, B>, ExecError> {
        let mut cloned = regs.clone();
        for csr in self.symbolic_csrs() {
            let symtab = &shared_state.symtab;
            let name = symtab
                .get(&zencode::encode(&csr.name))
                .unwrap_or_else(|| panic!("防御性编程：符号化 CSR {} 不在当前 IR symtab", csr.name));
            let value = self
                .pre_state()
                .get(&name)
                .unwrap_or_else(|| panic!("防御性编程：符号化 CSR {} 缺少注入期 pre_state 记录", csr.name));
            let concrete = model.get_val(value)?;
            cloned.assign(name, concrete, shared_state);
        }
        Ok(cloned)
    }

    /// 必输出寄存器判定：即使当前路径未约束（模型取 Arbitrary），也必须以
    /// complete model 补齐具体值写入 isa-state 的寄存器。默认无必输出寄存器。
    ///
    /// 原 `vector_context_registers`（RV64 覆写 vl/vstart/vtype/vcsr）的扩展
    /// （F4，campaign24 30 例 ok 路径 post-mismatch）：f0-f31/vr0-vr31 与 V 上
    /// 下文同因——访存路径只把寄存器值织进 DefineConst 链、不产生断言，最终
    /// 模型不解释即被 arbitrary 过滤丢弃；而 JSON 的 post-memory 写数据又经
    /// complete model 补全输出具体值，重放侧没有 isa-state 初值可编程
    /// FPR/VPR，只能用 emu 自身复位值，post 期望不可比。寄存器值必须与 post
    /// 数据同源输出。
    fn must_output_register(&self, reg_name: &str) -> bool {
        false
    }

    fn initial_state(&self) -> &[InitialRegisterConfig] {
        &[]
    }

    fn setup_pre_state<'ir>(
        &mut self,
        regs: &mut RegisterBindings<'ir, B>,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        fixed_prestate: &HashMap<Name, Val<B>>,
    ) -> Result<(), ExecError> {
        // reg_list 是本次求解关注的寄存器集合；这里对集合中的每个寄存器建立独立的 pre-state 符号值。
        let mut reg_names = self.reg_list();
        let initial_state = self.initial_state().to_vec();
        for entry in &initial_state {
            let name = shared_state.symtab.get(&zencode::encode(&entry.name)).ok_or_else(|| {
                ExecError::Type(format!("initial_state.{} 不存在于 IR", entry.name), SourceLoc::unknown())
            })?;
            let mut ty = shared_state.registers.get(&name).ok_or_else(|| {
                ExecError::Type(format!("initial_state.{} 不是寄存器", entry.name), SourceLoc::unknown())
            })?;
            // 用户配置的类型错误必须在符号化和修改寄存器之前报告；Poison 断言仍用于内部不变量。
            while let Ty::Struct(id) = ty {
                let fields = shared_state.type_info.structs.get(id).expect("防御性编程：寄存器结构缺少类型定义");
                if fields.len() != 1 {
                    return Err(ExecError::Type(
                        format!("initial_state.{} 需要单字段位向量结构", entry.name),
                        SourceLoc::unknown(),
                    ));
                }
                ty = fields.values().next().unwrap();
            }
            match ty {
                Ty::Bits(width) if *width > 0 => (),
                Ty::Bit | Ty::I64 | Ty::I128 => (),
                Ty::AnyBits if is_vector_register_name(&entry.name) => (),
                _ => {
                    return Err(ExecError::Type(
                        format!("initial_state.{} 仅支持非零宽度位向量寄存器", entry.name),
                        SourceLoc::unknown(),
                    ))
                }
            }
            if !reg_names.contains(&entry.name) {
                reg_names.push(entry.name.clone());
            }
        }
        // pre_state 保存这些符号值，供执行路径结束后的 solve_pre_state 从模型中取回。
        let pre_state = self.pre_state_mut();
        let symtab = &shared_state.symtab;
        let mut assigned = HashSet::new();
        for reg_name_str in reg_names.into_iter() {
            // 某些目标配置可能列出了当前 IR 中不存在的寄存器；这种寄存器不参与本次执行。
            let Some(name) = symtab.get(&zencode::encode(&reg_name_str)) else { continue };
            // shared_state.registers 是寄存器类型表。名称存在但不在类型表中说明 IR 内部不变量被破坏。
            let ty =
                shared_state.registers.get(&name).unwrap_or_else(|| panic!("防御性编程：{} 不是寄存器", reg_name_str));
            let recorded = if let Some(value) = fixed_prestate.get(&name) {
                value.clone()
            } else {
                match ty {
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
                }
            };
            // Poison 表示该类型不能表达为求解器值；这是不可恢复的内部错误。
            if matches!(recorded, Val::Poison) {
                panic!("防御性编程：寄存器 {} 的类型 {:?} 无法表示为符号值", reg_name_str, ty);
            }
            // 同一个符号值既覆盖执行帧中的寄存器，也记录到 pre_state，保证执行和输出使用同一变量。
            regs.assign(name, recorded.clone(), shared_state);
            pre_state.insert(name, recorded);
            assigned.insert(name);
        }

        for (&name, value) in fixed_prestate {
            if assigned.insert(name) {
                regs.assign(name, value.clone(), shared_state);
                pre_state.insert(name, value.clone());
            }
        }

        for entry in &initial_state {
            let mut value = pre_state.get_from_str(&entry.name, symtab).unwrap();
            while let Val::Struct(fields) = value {
                if fields.len() != 1 {
                    return Err(ExecError::Type(
                        format!("initial_state.{} 需要单字段位向量结构", entry.name),
                        SourceLoc::unknown(),
                    ));
                }
                value = fields.values().next().unwrap();
            }
            let width = match value {
                Val::Symbolic(sym) => solver.length(*sym),
                Val::Bits(bits) => Some(bits.len()),
                _ => None,
            }
            .ok_or_else(|| {
                ExecError::Type(format!("initial_state.{} 仅支持位向量寄存器", entry.name), SourceLoc::unknown())
            })?;
            if width == 0 {
                return Err(ExecError::Type(
                    format!("initial_state.{} 不支持零位宽", entry.name),
                    SourceLoc::unknown(),
                ));
            }
            let exp = smt_value(value, SourceLoc::unknown())?;
            for (range, concrete) in &entry.fields {
                let (high, low) = range.unwrap_or((width - 1, 0));
                if high >= width {
                    return Err(ExecError::Type(
                        format!("initial_state.{} 字段超出 {} 位寄存器", entry.name, width),
                        SourceLoc::unknown(),
                    ));
                }
                if let Some(n) = concrete {
                    let field_width = high - low + 1;
                    if field_width < 64 && n >> field_width != 0 {
                        return Err(ExecError::Type(
                            format!("initial_state.{} 具体值超出寄存器宽度", entry.name),
                            SourceLoc::unknown(),
                        ));
                    }
                    solver.assert_eq(
                        smtlib::Exp::Extract(high, low, Box::new(exp.clone())),
                        smtlib::bits64(*n, field_width),
                    );
                }
            }
        }

        // 通用符号化完成后，再由具体 Target 为 pre-state 补充架构特有的合法性约束，例如向量 vtype/vl 配对。
        self.constrain_pre_state(lets, shared_state, solver)
    }

    // 默认没有额外约束；需要限制 pre-state 合法取值的架构自行覆写。
    fn constrain_pre_state<'ir>(
        &mut self,
        _: &Bindings<'ir, B>,
        _: &SharedState<'ir, B>,
        _: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        Ok(())
    }

    fn domain_manifest(&self) -> BTreeMap<String, String> {
        BTreeMap::from([("status".to_string(), "not-applicable".to_string())])
    }

    fn solve_pre_state<'state>(
        &self,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'state, B>,
    ) -> Result<BTreeMap<String, String>, ExecError> {
        let pre_state = self.pre_state();
        let symtab = &shared_state.symtab;
        let mut result = BTreeMap::new();
        let mut arbitrary_must_output_registers = Vec::new();
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
                    // 例外（must_output_register）：V 上下文与 f/v 寄存器堆（F4）即使
                    // 未约束也必须输出——重放侧需要用与 post-memory 同源的模型值编程
                    // FPR/VPR 初值，缺失会让 emu 退回自身复位值、post 期望不可比。
                    if fmt_val.is_arbitrary() {
                        if self.must_output_register(&reg_name) {
                            arbitrary_must_output_registers.push((*name, val));
                        }
                        continue;
                    }
                    // 当前路径约束过的寄存器直接写入结果。
                    result.insert(reg_name, fmt_val.to_str(shared_state));
                }
                Err(e) => {
                    // 状态字段失败时不能返回一个看似成功的部分 witness。
                    return Err(e);
                }
            }
        }

        if !arbitrary_must_output_registers.is_empty() {
            // 必输出寄存器即使未影响当前路径也必须输出，因此开启 complete model 补齐其具体值。
            model.set_complete_model(true);
            for (name, val) in arbitrary_must_output_registers {
                let reg_name = zencode::decode(symtab.to_str(name));
                let fmt_val = FmtVal::from_val(val, model)?;
                if fmt_val.is_arbitrary() {
                    panic!("防御性编程：complete model 未能具化必输出寄存器 {}", reg_name);
                }
                result.insert(reg_name, fmt_val.to_str(shared_state));
            }
        }

        // S2（W17）：符号 PMA 边界（pma_regions.<name>.size）的模型值输出。
        // 注入期记录的符号常量从最终模型取具体值，判读界内/界外路径的边界取值；
        // 与上方过滤规则一致，路径未触及（Arbitrary）的符号不输出。
        for (region_name, sym) in self.symbolic_pma_sizes() {
            match model.get_var(*sym) {
                Ok(model_val) => {
                    if let Some(fmt_val) = FmtVal::from_model_val(&model_val) {
                        if !fmt_val.is_arbitrary() {
                            result.insert(format!("pma_regions.{}.size", region_name), fmt_val.to_str(shared_state));
                        }
                    }
                }
                Err(error) => {
                    if matches!(error, ExecError::Smt(_)) {
                        return Err(error);
                    }
                }
            }
        }

        Ok(result)
    }

    fn solve_pre_state_complete<'state>(
        &self,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'state, B>,
    ) -> Result<BTreeMap<String, String>, ExecError> {
        model.set_complete_model(true);
        let mut result = BTreeMap::new();
        for (name, value) in self.pre_state().iter() {
            let register_name = zencode::decode(shared_state.symtab.to_str(*name));
            let formatted = FmtVal::from_val(value, model)?;
            if formatted.is_arbitrary() {
                panic!("防御性编程：complete model 未能具化 pre-state 寄存器 {}", register_name);
            }
            result.insert(register_name, formatted.to_str(shared_state));
        }
        Ok(result)
    }

    fn solve_post_state<'state>(
        &self,
        regs: &RegisterBindings<'state, B>,
        model: &mut Model<'_, B>,
        shared_state: &SharedState<'state, B>,
    ) -> Result<BTreeMap<String, String>, ExecError> {
        model.set_complete_model(true);
        let mut result = BTreeMap::new();
        for (name, _) in self.pre_state().iter() {
            let register_name = zencode::decode(shared_state.symtab.to_str(*name));
            let value = regs
                .get_last_if_initialized(*name)
                .unwrap_or_else(|| panic!("防御性编程：post-state 缺少已初始化的目标寄存器 {}", register_name));
            let formatted = FmtVal::from_val(value, model)?;
            if formatted.is_arbitrary() {
                panic!("防御性编程：complete model 未能具化 post-state 寄存器 {}", register_name);
            }
            result.insert(register_name, formatted.to_str(shared_state));
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

/// CLI 固定 pre-state 输入的严格结构校验。只接受具体值，且递归核对字段、枚举
/// 身份和向量长度；不能使用 Val::plausible 的浅检查替代。
pub fn validate_fixed_prestate_value<B: BV>(
    reg_name: &str,
    reg_id: Name,
    value: &Val<B>,
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    lets: &Bindings<B>,
    regs: &RegisterBindings<B>,
) -> Result<(), String> {
    fn validate<B: BV>(
        value: &Val<B>,
        ty: &Ty<Name>,
        shared_state: &SharedState<B>,
        anybits_width: Option<u32>,
    ) -> Result<(), String> {
        let valid = match (value, ty) {
            (Val::I64(_), Ty::I64)
            | (Val::I128(_), Ty::I128)
            | (Val::Bool(_), Ty::Bool)
            | (Val::Unit, Ty::Unit)
            | (Val::String(_), Ty::String) => true,
            (Val::Bits(bits), Ty::Bits(width)) => bits.len() == *width,
            (Val::Bits(bits), Ty::Bit) => bits.len() == 1,
            (Val::Bits(bits), Ty::AnyBits) => anybits_width == Some(bits.len()),
            (Val::MixedBits(segments), Ty::Bits(width)) => {
                let total: Option<u32> = segments.iter().try_fold(0u32, |length, segment| match segment {
                    isla_lib::ir::BitsSegment::Concrete(bits) => length.checked_add(bits.len()),
                    isla_lib::ir::BitsSegment::Symbolic(_) => None,
                });
                total == Some(*width)
            }
            (Val::Enum(member), Ty::Enum(enum_id)) => {
                member.enum_id.to_name() == *enum_id
                    && shared_state.type_info.enums.get(enum_id).is_some_and(|members| member.member < members.len())
            }
            (Val::Struct(fields), Ty::Struct(struct_id)) => {
                let field_types = shared_state
                    .type_info
                    .structs
                    .get(struct_id)
                    .ok_or_else(|| format!("IR 缺少结构体 {:?} 定义", struct_id))?;
                if fields.len() != field_types.len() {
                    return Err(format!("结构体字段数不匹配: 期望 {}，实际 {}", field_types.len(), fields.len()));
                }
                for (name, field_ty) in field_types {
                    let field = fields.get(name).ok_or_else(|| format!("结构体缺少字段 {:?}", name))?;
                    validate(field, field_ty, shared_state, None)?;
                }
                true
            }
            (Val::Vector(values), Ty::FixedVector(length, element_ty)) => {
                if values.len() != *length as usize {
                    return Err(format!("定长向量长度不匹配: 期望 {}，实际 {}", length, values.len()));
                }
                for element in values {
                    validate(element, element_ty, shared_state, None)?;
                }
                true
            }
            (Val::Vector(values), Ty::Vector(element_ty)) | (Val::List(values), Ty::List(element_ty)) => {
                for element in values {
                    validate(element, element_ty, shared_state, None)?;
                }
                true
            }
            (Val::Ctor(ctor, payload), Ty::Union(union_id)) => {
                let constructors = shared_state
                    .type_info
                    .unions
                    .get(union_id)
                    .ok_or_else(|| format!("IR 缺少 union {:?} 定义", union_id))?;
                let payload_ty = constructors
                    .iter()
                    .find_map(|(name, ty)| if name == ctor { Some(ty) } else { None })
                    .ok_or_else(|| format!("union {:?} 不含构造子 {:?}", union_id, ctor))?;
                validate(payload, payload_ty, shared_state, None)?;
                true
            }
            _ => false,
        };
        if valid {
            Ok(())
        } else {
            Err(format!("固定值 {:?} 与寄存器类型 {:?} 不匹配", value, ty))
        }
    }

    let anybits_width = if matches!(ty, Ty::AnyBits) {
        if is_vector_register_name(reg_name) {
            Some(
                u32::try_from(integer_let_from_lets(lets, &shared_state.symtab, "vlen"))
                    .map_err(|error| format!("vlen 不能作寄存器宽度: {}", error))?,
            )
        } else {
            match regs.get_last_if_initialized(reg_id) {
                Some(Val::Bits(bits)) => Some(bits.len()),
                _ => None,
            }
        }
    } else {
        None
    };
    validate(value, ty, shared_state, anybits_width).map_err(|error| format!("{}: {}", reg_name, error))
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
    pub symbolic_pma_regions: Vec<PmaRegionConfig>,
    pub symbolic_pma_sizes: Vec<(String, Sym)>,
    pub symbolic_csrs: Vec<SymbolicRegisterConfig>,
    pub pre_state: PreStateCtx<B>,
}

impl<B: BV> Default for RV32<B> {
    fn default() -> Self {
        RV32 {
            pmp_symbolic: false,
            symbolic_pma_regions: Vec::new(),
            symbolic_pma_sizes: Vec::new(),
            symbolic_csrs: Vec::new(),
            pre_state: PreStateCtx::new(),
        }
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
    fn symbolic_pma_regions(&self) -> &[PmaRegionConfig] {
        &self.symbolic_pma_regions
    }
    fn symbolic_pma_sizes(&self) -> &[(String, Sym)] {
        &self.symbolic_pma_sizes
    }
    fn symbolic_pma_sizes_mut(&mut self) -> &mut Vec<(String, Sym)> {
        &mut self.symbolic_pma_sizes
    }
    fn symbolic_csrs(&self) -> &[SymbolicRegisterConfig] {
        &self.symbolic_csrs
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (0..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("fcsr".to_string());
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

#[derive(Clone, Copy)]
struct Rv64Domain {
    supports_s: bool,
    supports_u: bool,
    supports_h: bool,
}

impl Rv64Domain {
    fn mpp_values(&self) -> Vec<u64> {
        // 现行 Sail 的 reset 将 MPP 初始化为 0，即使 U 未实现也不能删去该模型状态。
        let mut allowed = vec![0];
        if self.supports_s {
            allowed.push(1);
        }
        allowed.push(3);
        allowed
    }

    fn probe_hart_support<'ir, B: BV>(
        extension: &str,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
    ) -> bool {
        let member = EnumMember::from_name(shared_state.symtab.lookup(extension), shared_state);
        let outcomes: Mutex<Vec<Result<bool, String>>> = Mutex::new(Vec::new());
        execute_ir_function(
            "zhartSupports",
            &[Val::Enum(member)],
            shared_state,
            &RegisterBindings::new(),
            lets,
            &outcomes,
            &|_, _, execution, _, mut solver, outcomes| {
                let result = match execution {
                    Ok((Run::Finished(Val::Bool(value)), frame)) => {
                        if frame.forks() != 0 || frame.has_sampled_branch() {
                            Err(format!("zhartSupports({}) 出现 fork 或采样", extension))
                        } else if solver.trace().to_vec().into_iter().any(|event| {
                            matches!(
                                event,
                                Event::ReadReg(..)
                                    | Event::WriteReg(..)
                                    | Event::ReadMem { .. }
                                    | Event::WriteMem { .. }
                                    | Event::Abstract { .. }
                            )
                        }) {
                            Err(format!("zhartSupports({}) 依赖寄存器、内存或抽象事件", extension))
                        } else {
                            match solver.check_sat(SourceLoc::unknown()) {
                                SmtResult::Sat => Ok(value),
                                other => Err(format!("zhartSupports({}) 最终 SMT 状态为 {:?}", extension, other)),
                            }
                        }
                    }
                    Ok((_, _)) => Err(format!("zhartSupports({}) 非具体 Bool 正常结束", extension)),
                    Err((error, _)) => Err(format!("zhartSupports({}) 执行失败: {}", extension, error)),
                };
                outcomes.lock().unwrap().push(result);
            },
        );
        let mut outcomes = outcomes.into_inner().unwrap();
        if outcomes.len() != 1 {
            panic!("防御性编程：zhartSupports({}) 应有唯一终态，实际 {}", extension, outcomes.len());
        }
        outcomes.pop().unwrap().unwrap_or_else(|error| panic!("防御性编程：{}", error))
    }
}

pub struct RV64<B: BV> {
    pub pmp_symbolic: bool,
    pub symbolic_pma_regions: Vec<PmaRegionConfig>,
    pub symbolic_pma_sizes: Vec<(String, Sym)>,
    pub symbolic_csrs: Vec<SymbolicRegisterConfig>,
    pub pre_state: PreStateCtx<B>,
    domain: Option<Rv64Domain>,
    pub initial_state: Vec<InitialRegisterConfig>,
    pub initial_state_rv64_domain: bool,
}

impl<B: BV> Default for RV64<B> {
    fn default() -> Self {
        RV64 {
            pmp_symbolic: false,
            symbolic_pma_regions: Vec::new(),
            symbolic_pma_sizes: Vec::new(),
            symbolic_csrs: Vec::new(),
            pre_state: PreStateCtx::new(),
            domain: None,
            initial_state: Vec::new(),
            initial_state_rv64_domain: false,
        }
    }
}

impl<B: BV> Target<B> for RV64<B> {
    fn initial_state(&self) -> &[InitialRegisterConfig] {
        &self.initial_state
    }

    fn arch_name(&self) -> &'static str {
        "riscv"
    }
    fn xlen_name(&self) -> &'static str {
        "rv64"
    }
    fn xlen(&self) -> &'static str {
        "64"
    }
    fn symbolic_pma_regions(&self) -> &[PmaRegionConfig] {
        &self.symbolic_pma_regions
    }
    fn symbolic_pma_sizes(&self) -> &[(String, Sym)] {
        &self.symbolic_pma_sizes
    }
    fn symbolic_pma_sizes_mut(&mut self) -> &mut Vec<(String, Sym)> {
        &mut self.symbolic_pma_sizes
    }
    fn symbolic_csrs(&self) -> &[SymbolicRegisterConfig] {
        &self.symbolic_csrs
    }
    fn reg_list(&self) -> Vec<String> {
        let mut regs: Vec<String> = (1..32).map(|r| format!("x{}", r)).collect();
        regs.extend((0..32).map(|r| format!("f{}", r)));
        regs.extend((0..32).map(|r| format!("vr{}", r)));
        // regs.push("PC".to_string());
        regs.push("cur_privilege".to_string());
        regs.push("mstatus".to_string());
        regs.push("fcsr".to_string());
        regs.push("vl".to_string());
        regs.push("vstart".to_string());
        regs.push("vtype".to_string());
        regs.push("vcsr".to_string());
        regs
    }
    fn must_output_register(&self, reg_name: &str) -> bool {
        // V 上下文寄存器沿用原必输出集合；f0-f31/vr0-vr31 为 F4 扩展（见 trait
        // 默认实现的注释），复用 is_vector_register_name 的 vr 判定形态。
        if matches!(reg_name, "vl" | "vstart" | "vtype" | "vcsr") {
            return true;
        }
        let digits = reg_name.strip_prefix("vr").or_else(|| reg_name.strip_prefix('f')).unwrap_or("");
        !digits.is_empty()
            && digits.len() <= 2
            && digits.bytes().all(|byte| byte.is_ascii_digit())
            && digits.parse::<u32>().map(|index| index < 32).unwrap_or(false)
    }
    fn constrain_pre_state<'ir>(
        &mut self,
        lets: &Bindings<'ir, B>,
        shared_state: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
    ) -> Result<(), ExecError> {
        let symtab = &shared_state.symtab;
        let privilege = self.pre_state.get_from_str("cur_privilege", symtab);
        let mstatus = self.pre_state.get_from_str("mstatus", symtab);
        match (privilege, mstatus) {
            _ if !self.initial_state_rv64_domain => self.domain = None,
            (Some(_), Some(_)) => {
                if integer_let_from_lets(lets, symtab, "xlen") != 64 {
                    panic!("防御性编程：RV64 pre-state 的 let xlen 不是 64");
                }
                let domain = Rv64Domain {
                    supports_s: Rv64Domain::probe_hart_support("zExt_S", lets, shared_state),
                    supports_u: Rv64Domain::probe_hart_support("zExt_U", lets, shared_state),
                    supports_h: Rv64Domain::probe_hart_support("zExt_H", lets, shared_state),
                };
                self.domain = Some(domain);
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
            (None, None) => self.domain = None,
            _ => panic!("防御性编程：RV64 cur_privilege 与 mstatus 必须同时存在于 pre-state"),
        }

        // RV64 的向量状态要求 vtype 与 vl 成对合法，因此从已符号化的 pre-state 中取出二者。
        let pre_state = self.pre_state();
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
    fn domain_manifest(&self) -> BTreeMap<String, String> {
        let Some(domain) = self.domain else {
            return BTreeMap::from([("status".to_string(), "not-applicable".to_string())]);
        };
        let mut allowed = vec!["Machine"];
        if domain.supports_s {
            allowed.push("Supervisor");
        }
        if domain.supports_u {
            allowed.push("User");
        }
        if domain.supports_h && domain.supports_s {
            allowed.push("VirtualSupervisor");
        }
        if domain.supports_h && domain.supports_u {
            allowed.push("VirtualUser");
        }
        BTreeMap::from([
            ("status".to_string(), "validated".to_string()),
            ("xlen".to_string(), "64".to_string()),
            ("hart-supports-S".to_string(), domain.supports_s.to_string()),
            ("hart-supports-U".to_string(), domain.supports_u.to_string()),
            ("hart-supports-H".to_string(), domain.supports_h.to_string()),
            ("allowed-privileges".to_string(), allowed.join(",")),
            ("mstatus-sxl".to_string(), if domain.supports_s { "2" } else { "0" }.to_string()),
            ("mstatus-uxl".to_string(), if domain.supports_u { "2" } else { "0" }.to_string()),
            ("mstatus-mpp".to_string(), domain.mpp_values().iter().map(u64::to_string).collect::<Vec<_>>().join(",")),
            ("mstatus-mpp-reset-exception".to_string(), if domain.supports_u { "none" } else { "0" }.to_string()),
            ("reserved-mpp".to_string(), "2-excluded".to_string()),
            ("capability-source".to_string(), "zhartSupports".to_string()),
            ("rule-source".to_string(), "sail-riscv/model/core/sys_regs.sail reset/legalize".to_string()),
        ])
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

/// 枚举成员的 IR 名（z 前缀）到 Val::Enum 的转换：symtab 查成员名，enum_members
/// 拿 (序号, 所在枚举)，构造与 IR 枚举身份一致的 EnumMember。
fn pma_enum_member<B: BV>(
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    member_ir_name: &str,
    context: &str,
) -> Result<Val<B>, String> {
    let member_name = symtab
        .get(&zencode::encode(member_ir_name))
        .ok_or_else(|| format!("IR 缺少枚举成员 {}（{}）", member_ir_name, context))?;
    let (member, _size, enum_name) = type_info
        .enum_members
        .get(&member_name)
        .ok_or_else(|| format!("type_info 缺少枚举成员 {}（{}）", member_ir_name, context))?;
    Ok(Val::Enum(EnumMember { enum_id: EnumId::from_name(*enum_name), member: *member }))
}

/// 按 zPMA record 的字段定义，把配置属性构造成 Val::Struct。字段名从
/// type_info 取（decode 回原始名后匹配配置），IR 新增字段没有对应配置时
/// 硬报错，避免静默产出缺字段的错误地图。
fn pma_attributes_value<B: BV>(
    attributes: &PmaAttributes,
    pma_struct_name: Name,
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<Val<B>, String> {
    let struct_def = type_info
        .structs
        .get(&pma_struct_name)
        .ok_or_else(|| format!("type_info 缺少 struct {}（PMA 属性 record）", symtab.to_str(pma_struct_name)))?;

    let mut fields: ahash::HashMap<Name, Val<B>> =
        HashMap::with_capacity_and_hasher(struct_def.len(), ahash::RandomState::new());
    for (field_name, field_ty) in struct_def {
        let field = zencode::decode(symtab.to_str(*field_name));
        let value = match (field.as_str(), field_ty) {
            ("cacheable", Ty::Bool) => Val::Bool(attributes.cacheable),
            ("coherent", Ty::Bool) => Val::Bool(attributes.coherent),
            ("executable", Ty::Bool) => Val::Bool(attributes.executable),
            ("read_idempotent", Ty::Bool) => Val::Bool(attributes.read_idempotent),
            ("readable", Ty::Bool) => Val::Bool(attributes.readable),
            ("supports_cbo_zero", Ty::Bool) => Val::Bool(attributes.supports_cbo_zzero),
            ("writable", Ty::Bool) => Val::Bool(attributes.writable),
            ("write_idempotent", Ty::Bool) => Val::Bool(attributes.write_idempotent),
            ("misaligned_fault", Ty::Enum(_)) => match attributes.misaligned_fault {
                PmaMisalignedFault::NoFault => pma_enum_member(symtab, type_info, "NoFault", "misaligned_fault")?,
                PmaMisalignedFault::AccessFault => {
                    pma_enum_member(symtab, type_info, "AccessFault", "misaligned_fault")?
                }
                PmaMisalignedFault::AlignmentFault => {
                    pma_enum_member(symtab, type_info, "AlignmentFault", "misaligned_fault")?
                }
            },
            ("reservability", Ty::Enum(_)) => match attributes.reservability {
                PmaReservability::None => pma_enum_member(symtab, type_info, "RsrvNone", "reservability")?,
                PmaReservability::NonEventual => {
                    pma_enum_member(symtab, type_info, "RsrvNonEventual", "reservability")?
                }
                PmaReservability::Eventual => pma_enum_member(symtab, type_info, "RsrvEventual", "reservability")?,
            },
            _ => return Err(format!("zPMA 字段 {}（类型 {:?}）无法从 [[pma_regions]] 配置映射", field, field_ty)),
        };
        fields.insert(*field_name, value);
    }
    Ok(Val::Struct(fields))
}

/// 把配置的 [[pma_regions]] 构造成 zpma_regions 寄存器的值：
/// `Val::List(vec![Val::Struct(zPMA_Region {...})])`。字段名/类型全部从
/// symtab + type_info 查（结构同 generate_default_value 的按 Ty 递归构造，
/// 但取配置值）；配置列表的次序（解析时已按 base 降序）原样保留。
/// zsizze 字段值由调用方逐 region 提供（size_values，与 regions 一一对应）：
/// 具体路径给 Val::Bits，符号路径给声明好的 Val::Symbolic。
fn pma_regions_list_value<B: BV>(
    regions: &[PmaRegionConfig],
    size_values: &[Val<B>],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
) -> Result<Val<B>, String> {
    if regions.len() != size_values.len() {
        panic!("防御性编程：size_values 长度 {} 与 regions 长度 {} 不一致", size_values.len(), regions.len());
    }
    let region_struct_name = symtab
        .get(&zencode::encode("PMA_Region"))
        .ok_or_else(|| "symtab 缺少 struct PMA_Region：当前 IR 不含 zpma_regions 模型".to_string())?;
    let struct_def = type_info
        .structs
        .get(&region_struct_name)
        .ok_or_else(|| "type_info 缺少 struct PMA_Region 定义".to_string())?;

    let mut items = Vec::with_capacity(regions.len());
    for (region, size_value) in regions.iter().zip(size_values) {
        let mut fields: ahash::HashMap<Name, Val<B>> =
            HashMap::with_capacity_and_hasher(struct_def.len(), ahash::RandomState::new());
        for (field_name, field_ty) in struct_def {
            let field = zencode::decode(symtab.to_str(*field_name));
            let value = match (field.as_str(), field_ty) {
                ("attributes", Ty::Struct(pma_struct_name)) => {
                    pma_attributes_value(&region.attributes, *pma_struct_name, symtab, type_info)?
                }
                ("base", Ty::Bits(64)) => Val::Bits(B::new(region.base, 64)),
                ("size", Ty::Bits(64)) => size_value.clone(),
                ("include_in_device_tree", Ty::Bool) => Val::Bool(region.attributes.include_in_device_tree),
                _ => {
                    return Err(format!(
                        "zPMA_Region 字段 {}（类型 {:?}）无法从 [[pma_regions]] 配置映射",
                        field, field_ty
                    ))
                }
            };
            fields.insert(*field_name, value);
        }
        items.push(Val::Struct(fields));
    }
    Ok(Val::List(items))
}

/// W10（S1）：[[pma_regions]] 配置注入。把配置地图构造成 list-of-records 值写入
/// default_registers 的 zpma_regions 键——solve-state 启动时
/// initialize_architecture/initialize_register 用它替代 IR 固化默认地图，模型
/// 的 zpmaCheck/zmatching_pma 逻辑零改动。未配置时调用方不调本函数，沿用 IR
/// 固化默认。只接受全具体 size（符号边界走执行期注入
/// apply_symbolic_pma_regions_to_registers）。
pub fn apply_pma_regions_to_config<B: BV>(
    regions: &[PmaRegionConfig],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    default_registers: &mut HashMap<Name, Val<B>>,
) -> Result<(), String> {
    let size_values: Vec<Val<B>> = regions
        .iter()
        .map(|region| match region.size {
            PmaSize::Concrete(size) => Val::Bits(B::new(size, 64)),
            PmaSize::Symbolic { .. } => {
                panic!("防御性编程：具体注入路径不得收到 symbolic size（region {}）", region.name)
            }
        })
        .collect();
    let list = pma_regions_list_value(regions, &size_values, symtab, type_info)?;
    // IR 寄存器名 zpma_regions 即 zencode("pma_regions")，insert_register 内部按 zencode 查找
    insert_register(symtab, default_registers, "pma_regions", list)
}

/// S2（W17）：含符号边界的 [[pma_regions]] 执行期注入。符号 zsizze 必须活在
/// 本次求解的 solver 里（config 期没有 solver 上下文），因此不走
/// default_registers，而是在 solve-state 启动、checkpoint 之前把整张地图
/// （具体/符号字段混合）直接赋给执行帧的 zpma_regions 寄存器（镜像符号 PMP
/// 的 apply_symbolic_pmp_to_registers 装配方式）。符号 size 的取值域
/// [min, max]（闭区间）以 bvule 断言附加在主 solver 上，checkpoint 之后所有
/// 路径共享同一组符号声明与域约束。返回 (region 名, Sym) 记录，供
/// solve_pre_state 从最终模型输出边界值。
pub fn apply_symbolic_pma_regions_to_registers<'ir, B: BV>(
    regions: &[PmaRegionConfig],
    symtab: &Symtab,
    type_info: &IRTypeInfo,
    regs: &mut RegisterBindings<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<Vec<(String, Sym)>, String> {
    let mut records = Vec::new();
    let mut size_values: Vec<Val<B>> = Vec::with_capacity(regions.len());
    for region in regions {
        match region.size {
            PmaSize::Concrete(size) => size_values.push(Val::Bits(B::new(size, 64))),
            PmaSize::Symbolic { min, max } => {
                let sym = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
                // 闭区间 [min, max]：min <= size 且 size <= max
                solver.assert(smtlib::Exp::And(
                    Box::new(smtlib::Exp::Bvule(Box::new(smtlib::bits64(min, 64)), Box::new(smtlib::Exp::Var(sym)))),
                    Box::new(smtlib::Exp::Bvule(Box::new(smtlib::Exp::Var(sym)), Box::new(smtlib::bits64(max, 64)))),
                ));
                records.push((region.name.clone(), sym));
                size_values.push(Val::Symbolic(sym));
            }
        }
    }
    let list = pma_regions_list_value(regions, &size_values, symtab, type_info)?;
    let Some(name) = symtab.get(&zencode::encode("pma_regions")) else {
        return Err("Could not find register pma_regions when applying PMA configuration".to_string());
    };
    regs.assign(name, list, shared_state);
    Ok(records)
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
    use isla_lib::ir::{Exp, Instr, Loc, Op, RETURN};
    use isla_lib::smt::{Config, Context, SmtResult};

    fn rv64() -> RV64<B64> {
        RV64::default()
    }
    fn rv32() -> RV32<B64> {
        RV32::default()
    }

    fn rv64_domain_smt_result(
        supports_s: bool,
        supports_u: bool,
        supports_h: bool,
        privilege_name: &str,
        mstatus_bits: u64,
    ) -> (SmtResult, BTreeMap<String, String>) {
        rv64_domain_smt_result_with_probe_error(
            supports_s,
            supports_u,
            supports_h,
            privilege_name,
            mstatus_bits,
            false,
            false,
        )
    }

    fn rv64_domain_smt_result_with_probe_error(
        supports_s: bool,
        supports_u: bool,
        supports_h: bool,
        privilege_name: &str,
        mstatus_bits: u64,
        probe_reads_register: bool,
        probe_returns_symbolic: bool,
    ) -> (SmtResult, BTreeMap<String, String>) {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let texts: Vec<String> = [
            "zhartSupports",
            "zextension",
            "zExt_S",
            "zExt_U",
            "zExt_H",
            "zextension_arg",
            "zPrivilege",
            "zUser",
            "zVirtualUser",
            "zSupervisor",
            "zVirtualSupervisor",
            "zMachine",
            "zcur_privilege",
            "zmstatus",
            "zMstatus",
            "zbits",
            "zxlen",
            "zprobe_register",
        ]
        .iter()
        .map(|text| text.to_string())
        .collect();
        let mut symtab = Symtab::new();
        let names: Vec<Name> = texts.iter().map(|text| symtab.intern(text)).collect();
        let name = |text: &str| {
            let index = texts.iter().position(|candidate| candidate == text).unwrap();
            names[index]
        };
        let extension_ty = Ty::Enum(name("zextension"));
        let return_ty = Ty::Bool;
        let support_exp = [(supports_s, "zExt_S"), (supports_u, "zExt_U"), (supports_h, "zExt_H")]
            .into_iter()
            .filter_map(|(supported, member)| {
                supported.then(|| Exp::Call(Op::Eq, vec![Exp::Id(name("zextension_arg")), Exp::Id(name(member))]))
            })
            .reduce(|lhs, rhs| Exp::Call(Op::Or, vec![lhs, rhs]))
            .unwrap_or(Exp::Bool(false));
        let body = vec![
            Instr::Copy(
                Loc::Id(RETURN),
                if probe_reads_register {
                    Exp::Id(name("zprobe_register"))
                } else if probe_returns_symbolic {
                    Exp::Undefined(Ty::Bool)
                } else {
                    support_exp
                },
                SourceLoc::unknown(),
            ),
            Instr::End,
        ];
        let mut shared_state = SharedState::empty(symtab);
        for (enum_name, members) in [
            ("zextension", vec!["zExt_S", "zExt_U", "zExt_H"]),
            ("zPrivilege", vec!["zUser", "zVirtualUser", "zSupervisor", "zVirtualSupervisor", "zMachine"]),
        ] {
            let enum_id = name(enum_name);
            let enum_members: Vec<Name> = members.iter().map(|member| name(member)).collect();
            for (index, member) in enum_members.iter().enumerate() {
                shared_state.type_info.enum_members.insert(*member, (index, enum_members.len(), enum_id));
            }
            shared_state.type_info.enums.insert(enum_id, enum_members);
        }
        shared_state
            .functions
            .insert(name("zhartSupports"), (vec![(name("zextension_arg"), &extension_ty)], &return_ty, &body));
        shared_state.registers.insert(name("zcur_privilege"), Ty::Enum(name("zPrivilege")));
        shared_state.registers.insert(name("zmstatus"), Ty::Struct(name("zMstatus")));
        shared_state.registers.insert(name("zprobe_register"), Ty::Bool);
        shared_state.type_info.structs.insert(name("zMstatus"), BTreeMap::from([(name("zbits"), Ty::Bits(64))]));
        let mut regs = RegisterBindings::new();
        let privilege_enum = solver.get_enum(name("zPrivilege"), 5);
        let privilege_symbol = solver.declare_const(smtlib::Ty::Enum(privilege_enum), SourceLoc::unknown());
        let mstatus_symbol = solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
        let mut mstatus_fields = ahash::HashMap::default();
        mstatus_fields.insert(name("zbits"), Val::Symbolic(mstatus_symbol));
        regs.insert(name("zcur_privilege"), false, UVal::Init(Val::Symbolic(privilege_symbol)));
        regs.insert(name("zmstatus"), false, UVal::Init(Val::Struct(mstatus_fields)));
        let mut lets = Bindings::default();
        lets.insert(name("zxlen"), UVal::Init(Val::I64(64)));
        let mut target = rv64();
        target.initial_state_rv64_domain = true;

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver, &HashMap::new()).unwrap();
        let privilege = match target.pre_state().get(&name("zcur_privilege")).unwrap() {
            Val::Symbolic(symbol) => *symbol,
            value => panic!("防御性编程：privilege 未符号化: {:?}", value),
        };
        let mstatus = match target.pre_state().get(&name("zmstatus")).unwrap() {
            Val::Struct(fields) => match fields.get(&name("zbits")).unwrap() {
                Val::Symbolic(symbol) => *symbol,
                value => panic!("防御性编程：mstatus.bits 未符号化: {:?}", value),
            },
            value => panic!("防御性编程：mstatus 未保持 struct: {:?}", value),
        };
        let enum_member = EnumMember::from_name(name(privilege_name), &shared_state);
        solver.assert_eq(smtlib::Exp::Var(privilege), smtlib::Exp::Enum(enum_member));
        solver.assert_eq(smtlib::Exp::Var(mstatus), smtlib::bits64(mstatus_bits, 64));
        (solver.check_sat(SourceLoc::unknown()), target.domain_manifest())
    }

    #[test]
    fn rv64_domain_allows_real_modes_and_rejects_virtual_modes() {
        let mstatus = (2_u64 << 34) | (2_u64 << 32);
        for privilege in ["zMachine", "zSupervisor", "zUser"] {
            assert_eq!(rv64_domain_smt_result(true, true, false, privilege, mstatus).0, SmtResult::Sat);
        }
        for privilege in ["zVirtualSupervisor", "zVirtualUser"] {
            assert_eq!(rv64_domain_smt_result(true, true, false, privilege, mstatus).0, SmtResult::Unsat);
        }
    }

    #[test]
    fn rv64_domain_keeps_fs_vs_runtime_variation_and_rejects_bad_xlen_fields() {
        let xlen_fields = (2_u64 << 34) | (2_u64 << 32);
        for runtime_bits in [0_u64, 1_u64 << 13, 3_u64 << 13, 1_u64 << 9, 3_u64 << 9] {
            assert_eq!(
                rv64_domain_smt_result(true, true, false, "zMachine", xlen_fields | runtime_bits).0,
                SmtResult::Sat
            );
        }
        assert_eq!(rv64_domain_smt_result(true, true, false, "zMachine", 0).0, SmtResult::Unsat);
    }

    #[test]
    fn rv64_domain_excludes_only_reserved_mpp_encoding() {
        let xlen_fields = (2_u64 << 34) | (2_u64 << 32);
        for mpp in [0_u64, 1_u64, 3_u64] {
            assert_eq!(
                rv64_domain_smt_result(true, true, false, "zMachine", xlen_fields | (mpp << 11)).0,
                SmtResult::Sat
            );
        }
        assert_eq!(
            rv64_domain_smt_result(true, true, false, "zMachine", xlen_fields | (2_u64 << 11)).0,
            SmtResult::Unsat
        );
        assert_eq!(
            rv64_domain_smt_result(true, true, false, "zMachine", xlen_fields | (3_u64 << 11) | (3_u64 << 13)).0,
            SmtResult::Sat
        );
    }

    #[test]
    fn rv64_mpp_domain_matches_hart_capabilities_and_manifest() {
        for supports_s in [false, true] {
            for supports_u in [false, true] {
                let xlen_fields =
                    (if supports_s { 2_u64 << 34 } else { 0 }) | (if supports_u { 2_u64 << 32 } else { 0 });
                let expected_mpp: Vec<u64> = [0, 1, 3]
                    .into_iter()
                    .filter(|mpp| match mpp {
                        0 => true,
                        1 => supports_s,
                        3 => true,
                        _ => unreachable!(),
                    })
                    .collect();
                let expected_manifest = expected_mpp.iter().map(u64::to_string).collect::<Vec<_>>().join(",");
                for mpp in 0..4 {
                    let (actual, manifest) =
                        rv64_domain_smt_result(supports_s, supports_u, false, "zMachine", xlen_fields | (mpp << 11));
                    assert_eq!(
                        actual,
                        if expected_mpp.contains(&mpp) { SmtResult::Sat } else { SmtResult::Unsat },
                        "S={supports_s}, U={supports_u}, MPP={mpp}"
                    );
                    assert_eq!(manifest["mstatus-mpp"], expected_manifest);
                    assert_eq!(manifest["mstatus-mpp-reset-exception"], if supports_u { "none" } else { "0" });
                }
            }
        }
    }

    #[test]
    fn rv64_domain_respects_absent_s_and_u_capabilities() {
        // 现行 Sail 从零初始化 mstatus，无 U 时仍存在 MPP=0 的 reset 初态。
        let machine_mpp = 0;
        let (result, manifest) = rv64_domain_smt_result(false, false, false, "zMachine", machine_mpp);
        assert_eq!(result, SmtResult::Sat);
        assert_eq!(manifest["hart-supports-S"], "false");
        assert_eq!(manifest["hart-supports-U"], "false");
        assert_eq!(manifest["allowed-privileges"], "Machine");
        assert_eq!(rv64_domain_smt_result(false, false, false, "zSupervisor", machine_mpp).0, SmtResult::Unsat);
        assert_eq!(rv64_domain_smt_result(false, false, false, "zUser", machine_mpp).0, SmtResult::Unsat);
        assert_eq!(
            rv64_domain_smt_result(false, false, false, "zMachine", (2_u64 << 34) | machine_mpp).0,
            SmtResult::Unsat
        );
    }

    #[test]
    #[should_panic(expected = "zhartSupports")]
    fn rv64_domain_rejects_capability_probe_with_register_dependency() {
        rv64_domain_smt_result_with_probe_error(true, true, false, "zMachine", 0, true, false);
    }

    #[test]
    #[should_panic(expected = "非具体 Bool")]
    fn rv64_domain_rejects_symbolic_capability_result() {
        rv64_domain_smt_result_with_probe_error(true, true, false, "zMachine", 0, false, true);
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
        for register_name in ["vl", "vstart", "vtype", "vcsr"] {
            assert!(target.must_output_register(register_name));
        }
        // F4：f/v 寄存器堆同样必输出
        for index in [0, 9, 31] {
            assert!(target.must_output_register(&format!("f{index}")));
            assert!(target.must_output_register(&format!("vr{index}")));
        }
        // 边界负例：x 寄存器、越界编号、非寄存器名不在此列
        for register_name in ["x1", "f32", "f100", "vr32", "fx", "fr", "fcsr", "vlx"] {
            assert!(!target.must_output_register(register_name), "{} 不应是必输出寄存器", register_name);
        }
        // fd92696 起 reg_list 即 setup_pre_state 的待符号化集合：
        // x0（恒零）与 PC（取指驱动）不符号化，排除逻辑在数据源完成
        assert_eq!(["vl", "vstart", "vtype", "vcsr"], ["vl", "vstart", "vtype", "vcsr"]);
        // reg_list 是主动符号化的状态清单；固定的 x0 与入口 PC 不在其中。
        let regs = target.reg_list();
        assert!(!regs.contains(&"x0".to_string()));
        assert!(!regs.contains(&"PC".to_string()));
        assert!(regs.contains(&"vr0".to_string()));
        assert!(regs.contains(&"mstatus".to_string()));
        assert!(regs.contains(&"vtype".to_string()));
        assert!(regs.contains(&"vl".to_string()));
        assert!(regs.contains(&"vstart".to_string()));
        assert!(regs.contains(&"vcsr".to_string()));
        // pre-state 仅由清单中实际存在的寄存器构成。
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
    fn riscv_state_registers_include_fcsr() {
        assert!(rv64().reg_list().contains(&"fcsr".to_string()));
        assert!(rv32().reg_list().contains(&"fcsr".to_string()));
    }

    #[test]
    fn struct_setup_and_symbolic_post_write_preserve_pre_state() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr_text = zencode::encode("fcsr");
        let fcsr_ty_text = zencode::encode("Fcsr");
        let bits_text = zencode::encode("bits");
        let fcsr_name = symtab.intern(&fcsr_text);
        let fcsr_ty_name = symtab.intern(&fcsr_ty_text);
        let bits_name = symtab.intern(&bits_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(fcsr_name, Ty::Struct(fcsr_ty_name));
        shared_state.type_info.structs.insert(fcsr_ty_name, BTreeMap::from([(bits_name, Ty::Bits(32))]));
        let mut regs = RegisterBindings::new();
        let mut original_fields = ahash::HashMap::default();
        original_fields.insert(bits_name, Val::Bits(B64::new(0, 32)));
        regs.insert(fcsr_name, false, UVal::Init(Val::Struct(original_fields)));
        let mut target = rv64();

        target.setup_pre_state(&mut regs, &Bindings::default(), &shared_state, &mut solver, &HashMap::new()).unwrap();
        let before = target.pre_state().get(&fcsr_name).unwrap();
        let pre_bits = match before {
            Val::Struct(fields) => match fields.get(&bits_name).unwrap() {
                Val::Symbolic(symbol) => *symbol,
                value => panic!("防御性编程：Fcsr.bits 未符号化: {:?}", value),
            },
            value => panic!("防御性编程：fcsr 未保留 Sail struct: {:?}", value),
        };
        // 表达写回：原有 flags 与新 flags 取并，再写入同一目标寄存器。
        let post_bits = solver.define_const(
            smtlib::Exp::Bvor(Box::new(smtlib::Exp::Var(pre_bits)), Box::new(smtlib::bits64(0x01, 32))),
            SourceLoc::unknown(),
        );
        let mut post_fields = ahash::HashMap::default();
        post_fields.insert(bits_name, Val::Symbolic(post_bits));
        regs.assign(fcsr_name, Val::Struct(post_fields), &shared_state);
        solver.assert_eq(smtlib::Exp::Var(pre_bits), smtlib::bits64(0x20, 32));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);

        let pre = FmtVal::from_val(target.pre_state().get(&fcsr_name).unwrap(), &mut model).unwrap();
        let post = FmtVal::from_val(regs.get_last_if_initialized(fcsr_name).unwrap(), &mut model).unwrap();
        assert_eq!(pre.to_str(&shared_state), "32'h0000_0020");
        assert_eq!(post.to_str(&shared_state), "32'h0000_0021");
    }

    #[test]
    fn fcsr_rounding_mode_and_flags_are_not_fixed_by_setup() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for fcsr_bits in [0x00_u64, 0x9f_u64] {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let mut symtab = Symtab::new();
            let fcsr_name_text = zencode::encode("fcsr");
            let fcsr_name = symtab.intern(&fcsr_name_text);
            let mut shared_state = SharedState::empty(symtab);
            shared_state.registers.insert(fcsr_name, Ty::Bits(32));
            let mut regs = RegisterBindings::new();
            regs.insert(fcsr_name, false, UVal::Init(Val::Bits(B64::new(0, 32))));
            let mut target = rv64();

            target
                .setup_pre_state(&mut regs, &Bindings::default(), &shared_state, &mut solver, &HashMap::new())
                .unwrap();

            let fcsr = match target.pre_state().get(&fcsr_name).unwrap() {
                Val::Symbolic(symbol) => *symbol,
                value => panic!("防御性编程：fcsr 未保持符号性: {:?}", value),
            };
            solver.assert_eq(smtlib::Exp::Var(fcsr), smtlib::bits64(fcsr_bits, 32));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        }
    }

    #[test]
    fn rv32_target_trait() {
        let target = rv32();
        assert_eq!(target.arch_name(), "riscv");
        assert_eq!(target.xlen(), "32");
        assert_eq!(target.xlen_name(), "rv32");
        assert!(!target.must_output_register("vl"));
        assert!(!target.must_output_register("f0"));
        assert!(target.reg_list().contains(&"vtype".to_string()));
        assert!(target.reg_list().contains(&"vl".to_string()));
        assert!(target.reg_list().contains(&"vstart".to_string()));
        assert!(target.reg_list().contains(&"vcsr".to_string()));
    }

    #[test]
    fn complete_pre_state_keeps_arbitrary_fcsr_and_mstatus() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let mut target = rv64();
        let register_names: Vec<String> = ["fcsr", "mstatus"].iter().map(|name| zencode::encode(name)).collect();
        for register_name in &register_names {
            let name = symtab.intern(register_name);
            let value = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown()));
            target.pre_state.insert(name, value);
        }
        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);

        let legacy = target.solve_pre_state(&mut model, &shared_state).unwrap();
        assert!(!legacy.contains_key("fcsr"));
        assert!(!legacy.contains_key("mstatus"));
        let complete = target.solve_pre_state_complete(&mut model, &shared_state).unwrap();
        assert!(complete.contains_key("fcsr"));
        assert!(complete.contains_key("mstatus"));
    }

    #[test]
    fn complete_pre_and_post_state_share_one_model() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr_name = zencode::encode("fcsr");
        let name = symtab.intern(&fcsr_name);
        let before = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown()));
        let mut target = rv64();
        target.pre_state.insert(name, before.clone());
        let mut regs = RegisterBindings::new();
        regs.insert(name, false, UVal::Init(before));
        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        let pre = target.solve_pre_state_complete(&mut model, &shared_state).unwrap();
        let unchanged = target.solve_post_state(&regs, &mut model, &shared_state).unwrap();
        assert_eq!(pre["fcsr"], unchanged["fcsr"]);

        regs.assign(name, Val::Bits(B64::new(0x1f, 64)), &shared_state);
        let changed = target.solve_post_state(&regs, &mut model, &shared_state).unwrap();
        assert_ne!(pre["fcsr"], changed["fcsr"]);
    }

    #[test]
    fn complete_state_formats_sail_bitfield_structs() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr_name_text = zencode::encode("fcsr");
        let mstatus_name_text = zencode::encode("mstatus");
        let bits_name_text = zencode::encode("bits");
        let fcsr_name = symtab.intern(&fcsr_name_text);
        let mstatus_name = symtab.intern(&mstatus_name_text);
        let bits_name = symtab.intern(&bits_name_text);
        let mut target = rv64();
        let mut regs = RegisterBindings::new();
        for (name, width) in [(fcsr_name, 32), (mstatus_name, 64)] {
            let bits = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(width), SourceLoc::unknown()));
            let mut fields = ahash::HashMap::default();
            fields.insert(bits_name, bits);
            let value = Val::Struct(fields);
            target.pre_state.insert(name, value.clone());
            regs.insert(name, false, UVal::Init(value));
        }
        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);

        let pre = target.solve_pre_state_complete(&mut model, &shared_state).unwrap();
        let post = target.solve_post_state(&regs, &mut model, &shared_state).unwrap();
        assert_eq!(pre, post);
        assert!(pre.contains_key("fcsr"));
        assert!(pre.contains_key("mstatus"));
    }

    #[test]
    #[should_panic(expected = "post-state 缺少已初始化的目标寄存器 fcsr")]
    fn post_state_requires_initialized_target_register() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr_name_text = zencode::encode("fcsr");
        let fcsr_name = symtab.intern(&fcsr_name_text);
        let mut target = rv64();
        target.pre_state.insert(fcsr_name, Val::Bits(B64::new(0, 32)));
        let shared_state = SharedState::empty(symtab);
        let regs = RegisterBindings::new();
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        target.solve_post_state(&regs, &mut model, &shared_state).unwrap();
    }

    #[test]
    fn complete_state_rejects_unformattable_register() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr_name_text = zencode::encode("fcsr");
        let fcsr_name = symtab.intern(&fcsr_name_text);
        let mut target = rv64();
        target.pre_state.insert(fcsr_name, Val::I64(1));
        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        assert!(target.solve_pre_state_complete(&mut model, &shared_state).is_err());
    }

    #[test]
    fn setup_pre_state_resolves_vector_anybits_from_vlen() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver, &HashMap::new()).unwrap();

        let vr0 = match target.pre_state().get(&vr0_name).unwrap() {
            Val::Symbolic(sym) => *sym,
            value => panic!("防御性编程：vr0 未被符号化: {:?}", value),
        };
        assert_eq!(solver.length(vr0), Some(128));
    }

    #[test]
    fn setup_pre_state_overrides_initialized_non_anybits_register() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        // 这里只验证通用 Target 符号化；RV64 的完整特权域另有双寄存器 fixture。
        let mut target = rv32();

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver, &HashMap::new()).unwrap();

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

    #[test]
    fn setup_pre_state固定值覆盖寄存器且同步输出() {
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let x1_text = zencode::encode("x1");
        let satp_text = zencode::encode("satp");
        let name = symtab.intern(&x1_text);
        let satp_name = symtab.intern(&satp_text);
        let mut shared_state = SharedState::empty(symtab);
        shared_state.registers.insert(name, Ty::Bits(64));
        shared_state.registers.insert(satp_name, Ty::Bits(64));
        let mut regs = RegisterBindings::new();
        let ty = Ty::Bits(64);
        regs.insert(name, false, UVal::Uninit(&ty));
        regs.insert(satp_name, false, UVal::Uninit(&ty));
        let fixed = Val::Bits(B64::new(0x8000_1000, 64));
        let satp_fixed = Val::Bits(B64::new(0, 64));
        let overrides = HashMap::from([(name, fixed.clone()), (satp_name, satp_fixed.clone())]);
        let mut target = rv64();

        target.setup_pre_state(&mut regs, &Bindings::default(), &shared_state, &mut solver, &overrides).unwrap();
        assert_eq!(target.pre_state().get(&name), Some(&fixed));
        assert_eq!(regs.get_last_if_initialized(name), Some(&fixed));
        assert_eq!(target.pre_state().get(&satp_name), Some(&satp_fixed));
        assert_eq!(regs.get_last_if_initialized(satp_name), Some(&satp_fixed));
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

        target.setup_pre_state(&mut regs, &lets, &shared_state, &mut solver, &HashMap::new()).unwrap();
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
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
    fn solve_pre_state_serializes_arbitrary_fpr_and_vpr_registers() {
        // F4（campaign24，30 例 ok 路径 post-mismatch）：f/v 寄存器在 pre_state
        // 有符号，但访存路径只把它们的值织进 DefineConst 链、不产生断言，最终
        // 模型不解释 → arbitrary 过滤把它们从 isa-state 丢弃 → 重放无法编程
        // FPR/VPR，emu 用自身复位值与 JSON post（经 complete model 补全的值）
        // 不可比。f0-f31 / vr0-vr31 必须与 V 上下文寄存器同机制必输出。
        let float_registers: Vec<String> = (0..32).map(|index| format!("f{index}")).collect();
        let vector_registers: Vec<String> = (0..32).map(|index| format!("vr{index}")).collect();
        let expected_registers: Vec<String> =
            float_registers.iter().cloned().chain(vector_registers.iter().cloned()).collect();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let mut target = rv64();

        let encoded_register_names: Vec<String> =
            expected_registers.iter().map(|register_name| zencode::encode(register_name)).collect();
        for (register_name, encoded_register_name) in expected_registers.iter().zip(encoded_register_names.iter()) {
            let register = symtab.intern(encoded_register_name);
            let width = if register_name.starts_with("f") { 64 } else { 128 };
            let value = Val::Symbolic(solver.declare_const(smtlib::Ty::BitVec(width), SourceLoc::unknown()));
            target.pre_state.insert(register, value);
        }

        let shared_state = SharedState::empty(symtab);
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        let state = target.solve_pre_state(&mut model, &shared_state).unwrap();

        for register_name in &expected_registers {
            assert!(state.contains_key(register_name), "{} 必须被写入 isa-state", register_name);
            let expected_prefix = if register_name.starts_with('f') { "64'h" } else { "128'h" };
            assert!(
                state[register_name].starts_with(expected_prefix),
                "{} 必须是具体位向量值，实际 {}",
                register_name,
                state[register_name]
            );
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

    /// W10（S1）[[pma_regions]] → zpma_regions 寄存器值构造的测试夹具：
    /// 手工搭出与 rv64d.ir 相同形状的 symtab/type_info（struct zPMA_Region、
    /// struct zPMA、enum zmisaligned_fault、enum zReservability、寄存器名
    /// zpma_regions），使构造逻辑可在单测中全量验证；真实 IR 的形状保真由
    /// 端到端测试（zSTORE 圈外 fault）兜底。
    fn pma_type_fixture() -> (Symtab<'static>, IRTypeInfo) {
        let mut symtab = Symtab::new();
        let pma_region_name = symtab.intern("zPMA_Region");
        let pma_name = symtab.intern("zPMA");
        let misaligned_enum = symtab.intern("zmisaligned_fault");
        let reservability_enum = symtab.intern("zReservability");

        let mut pma_fields = BTreeMap::new();
        pma_fields.insert(symtab.intern("zcacheable"), Ty::Bool);
        pma_fields.insert(symtab.intern("zcoherent"), Ty::Bool);
        pma_fields.insert(symtab.intern("zexecutable"), Ty::Bool);
        pma_fields.insert(symtab.intern("zmisaligned_fault"), Ty::Enum(misaligned_enum));
        pma_fields.insert(symtab.intern("zread_idempotent"), Ty::Bool);
        pma_fields.insert(symtab.intern("zreadable"), Ty::Bool);
        pma_fields.insert(symtab.intern("zreservability"), Ty::Enum(reservability_enum));
        pma_fields.insert(symtab.intern("zsupports_cbo_zzero"), Ty::Bool);
        pma_fields.insert(symtab.intern("zwritable"), Ty::Bool);
        pma_fields.insert(symtab.intern("zwrite_idempotent"), Ty::Bool);

        let mut region_fields = BTreeMap::new();
        region_fields.insert(symtab.intern("zattributes"), Ty::Struct(pma_name));
        region_fields.insert(symtab.intern("zbase"), Ty::Bits(64));
        region_fields.insert(symtab.intern("zinclude_in_device_tree"), Ty::Bool);
        region_fields.insert(symtab.intern("zsizze"), Ty::Bits(64));

        let mut structs = HashMap::new();
        structs.insert(pma_name, pma_fields);
        structs.insert(pma_region_name, region_fields);

        let mut enums = HashMap::new();
        let misaligned_members =
            vec![symtab.intern("zNoFault"), symtab.intern("zAccessFault"), symtab.intern("zAlignmentFault")];
        let reservability_members =
            vec![symtab.intern("zRsrvNone"), symtab.intern("zRsrvNonEventual"), symtab.intern("zRsrvEventual")];
        enums.insert(misaligned_enum, misaligned_members.clone());
        enums.insert(reservability_enum, reservability_members.clone());

        let mut enum_members = HashMap::new();
        for (pos, member) in misaligned_members.iter().enumerate() {
            enum_members.insert(*member, (pos, misaligned_members.len(), misaligned_enum));
        }
        for (pos, member) in reservability_members.iter().enumerate() {
            enum_members.insert(*member, (pos, reservability_members.len(), reservability_enum));
        }

        let type_info =
            IRTypeInfo { structs, enums, enum_members, unions: HashMap::new(), union_ctors: HashSet::new() };
        (symtab, type_info)
    }

    fn pma_region(base: u64, size: u64, attr: &str) -> isla_lib::config::PmaRegionConfig {
        use isla_lib::config::{PmaAttributes, PmaMisalignedFault, PmaRegionConfig, PmaReservability, PmaSize};
        // 别名取值与 config.rs 的 pma_regions_alias_mapping 测试锁定的映射一致；
        // 这里直接构造，聚焦验证 Val 构造侧。
        let attributes = match attr {
            "ram" => PmaAttributes {
                readable: true,
                writable: true,
                executable: true,
                cacheable: true,
                coherent: true,
                read_idempotent: true,
                write_idempotent: true,
                supports_cbo_zzero: true,
                misaligned_fault: PmaMisalignedFault::NoFault,
                reservability: PmaReservability::Eventual,
                include_in_device_tree: true,
            },
            "mmio" => PmaAttributes {
                readable: true,
                writable: true,
                executable: false,
                cacheable: false,
                coherent: true,
                read_idempotent: false,
                write_idempotent: false,
                supports_cbo_zzero: false,
                misaligned_fault: PmaMisalignedFault::AlignmentFault,
                reservability: PmaReservability::None,
                include_in_device_tree: false,
            },
            other => panic!("测试不支持别名 {}", other),
        };
        PmaRegionConfig { name: attr.to_string(), base, size: PmaSize::Concrete(size), attributes }
    }

    /// 构造出的 zpma_regions 值必须是 Val::List(Val::Struct...)，record 的
    /// base/size（注意 IR 字段名 zsizze 是 size 的 zencode）与别名属性逐字段
    /// 正确，枚举成员身份（enum_id + 序号）与 IR 定义一致。
    #[test]
    fn pma_regions_list_value_alias_fields() {
        let (symtab, type_info) = pma_type_fixture();
        let regions = vec![pma_region(0x8000_0000, 0x1000_0000, "ram"), pma_region(0x0200_0000, 0x0200_0000, "mmio")];

        let size_values: Vec<Val<B64>> = regions
            .iter()
            .map(|r| match r.size {
                isla_lib::config::PmaSize::Concrete(size) => Val::Bits(B64::new(size, 64)),
                isla_lib::config::PmaSize::Symbolic { .. } => panic!("本测试只用具体 size"),
            })
            .collect();
        let value = pma_regions_list_value::<B64>(&regions, &size_values, &symtab, &type_info).unwrap();
        let Val::List(items) = &value else { panic!("zpma_regions 值必须是 Val::List，实际 {:?}", value) };
        assert_eq!(items.len(), 2);

        let ram = match &items[0] {
            Val::Struct(fields) => fields,
            other => panic!("region 必须是 Struct，实际 {:?}", other),
        };
        let field = |name: &str| {
            let id = symtab.get(&zencode::encode(name)).unwrap_or_else(|| panic!("夹具缺字段 {}", name));
            ram.get(&id).unwrap_or_else(|| panic!("构造值缺字段 {}", name))
        };
        match field("base") {
            Val::Bits(bv) => assert_eq!(bv.lower_u64(), 0x8000_0000),
            other => panic!("base 必须是 Bits，实际 {:?}", other),
        }
        match field("size") {
            Val::Bits(bv) => assert_eq!(bv.lower_u64(), 0x1000_0000, "IR 字段 zsizze 应取配置 size"),
            other => panic!("size 必须是 Bits，实际 {:?}", other),
        }
        assert!(matches!(field("include_in_device_tree"), Val::Bool(true)));

        let attributes = match field("attributes") {
            Val::Struct(fields) => fields,
            other => panic!("attributes 必须是 Struct，实际 {:?}", other),
        };
        let attr_field = |name: &str| {
            let id = symtab.get(&zencode::encode(name)).unwrap();
            attributes.get(&id).unwrap_or_else(|| panic!("attributes 缺字段 {}", name))
        };
        assert!(matches!(attr_field("readable"), Val::Bool(true)));
        assert!(matches!(attr_field("writable"), Val::Bool(true)));
        assert!(matches!(attr_field("executable"), Val::Bool(true)));
        assert!(matches!(attr_field("cacheable"), Val::Bool(true)));
        assert!(matches!(attr_field("read_idempotent"), Val::Bool(true)));
        assert!(matches!(attr_field("write_idempotent"), Val::Bool(true)));
        assert!(matches!(attr_field("supports_cbo_zero"), Val::Bool(true)));
        let misaligned_enum = symtab.get(&zencode::encode("misaligned_fault")).unwrap();
        match attr_field("misaligned_fault") {
            Val::Enum(member) => {
                assert_eq!(member.enum_id.to_name(), misaligned_enum);
                assert_eq!(member.member, 0, "ram 的 misaligned 应是 zNoFault（首成员）");
            }
            other => panic!("misaligned_fault 必须是 Enum，实际 {:?}", other),
        }
        let reservability_enum = symtab.get(&zencode::encode("Reservability")).unwrap();
        match attr_field("reservability") {
            Val::Enum(member) => {
                assert_eq!(member.enum_id.to_name(), reservability_enum);
                assert_eq!(member.member, 2, "ram 的 reservability 应是 zRsrvEventual（第 3 成员）");
            }
            other => panic!("reservability 必须是 Enum，实际 {:?}", other),
        }

        // mmio：misaligned=AlignmentFault（第 3 成员）、reservability=RsrvNone（首成员）
        let mmio = match &items[1] {
            Val::Struct(fields) => fields,
            other => panic!("region 必须是 Struct，实际 {:?}", other),
        };
        let attributes = match mmio.get(&symtab.get(&zencode::encode("attributes")).unwrap()) {
            Some(Val::Struct(fields)) => fields,
            other => panic!("attributes 必须是 Struct，实际 {:?}", other),
        };
        let misaligned = symtab.get(&zencode::encode("misaligned_fault")).unwrap();
        match attributes.get(&symtab.get(&zencode::encode("misaligned_fault")).unwrap()) {
            Some(Val::Enum(member)) => {
                assert_eq!(member.enum_id.to_name(), misaligned);
                assert_eq!(member.member, 2, "mmio 的 misaligned 应是 zAlignmentFault");
            }
            other => panic!("misaligned_fault 必须是 Enum，实际 {:?}", other),
        }
    }

    /// 注入：apply_pma_regions_to_config 把构造值写入 default_registers 的
    /// zpma_regions 键；symtab 缺 zpma_regions 寄存器名（IR 不含 PMA 模型）时
    /// 报错而非静默注入。
    #[test]
    fn pma_regions_apply_to_config_registers() {
        let regions = vec![pma_region(0x8000_0000, 0x1000_0000, "ram")];

        // 夹具 symtab 尚未 intern zpma_regions：等价于"IR 无该寄存器"
        let (symtab, type_info) = pma_type_fixture();
        let mut default_registers = HashMap::new();
        assert!(
            apply_pma_regions_to_config::<B64>(&regions, &symtab, &type_info, &mut default_registers).is_err(),
            "缺 zpma_regions 寄存器名应报错"
        );
        assert!(default_registers.is_empty(), "失败时不得注入任何值");

        // intern 寄存器名后注入成功
        let (mut symtab, type_info) = pma_type_fixture();
        let zpma = symtab.intern("zpma_regions");
        let mut default_registers = HashMap::new();
        apply_pma_regions_to_config::<B64>(&regions, &symtab, &type_info, &mut default_registers).unwrap();
        assert!(matches!(default_registers.get(&zpma), Some(Val::List(_))), "zpma_regions 应已注入");
    }

    /// S2（W17）：符号边界执行期注入。apply_symbolic_pma_regions_to_registers
    /// 对 Symbolic size 的 region 声明 64 位常量、附加闭区间域约束、把混合
    /// （具体+符号）地图赋给执行帧 zpma_regions，并返回 (region 名, Sym) 记录。
    /// 具体字段（base/属性/具体 size）保持 W10 构造形状。
    #[test]
    fn pma_regions_symbolic_injection_assigns_register_and_records_syms() {
        use isla_lib::config::PmaSize;
        use isla_lib::ir::SharedState;
        use isla_lib::register::RegisterBindings;
        use isla_lib::smt::{Config, Context, Solver};

        let (mut symtab, type_info) = pma_type_fixture();
        let zpma = symtab.intern("zpma_regions");
        let mut symbolic = pma_region(0x8000_0000, 0, "ram");
        symbolic.size = PmaSize::Symbolic { min: 0x1000, max: 0x80000000000 };
        let mut concrete = pma_region(0x0200_0000, 0x0200_0000, "mmio");
        concrete.name = "mmio0".to_string();
        let regions = vec![symbolic, concrete];

        // 夹具 SharedState：注入只用到 symtab，构造最小空架构即可。
        let arch: &'static [isla_lib::ir::Def<Name, B64>] = Box::leak(Vec::new().into_boxed_slice());
        let shared_state = SharedState::new(
            symtab,
            arch,
            type_info.clone(),
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        let mut regs = RegisterBindings::new();
        // 生产路径里寄存器表由 initialize_architecture 建立（assign 只写已存在的键），
        // 夹具手动补 zpma_regions 的未初始化槽位。PMA_Region 结构名在夹具
        // symtab 中已 intern，直接按名取。
        let region_struct = shared_state
            .type_info
            .structs
            .keys()
            .find(|name| shared_state.symtab.to_str(**name) == "zPMA_Region")
            .copied()
            .expect("夹具缺 struct zPMA_Region");
        let region_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::List(Box::new(Ty::Struct(region_struct)))));
        regs.insert(zpma, false, UVal::Uninit(region_ty));
        let ctx = Context::new(Config::new());
        let mut solver = Solver::new(&ctx);

        let records = apply_symbolic_pma_regions_to_registers::<B64>(
            &regions,
            &shared_state.symtab,
            &shared_state.type_info,
            &mut regs,
            &shared_state,
            &mut solver,
        )
        .unwrap();

        // 记录只含符号 region
        assert_eq!(records.len(), 1, "只有符号 size 的 region 被记录");
        assert_eq!(records[0].0, "ram");

        // 寄存器已赋值，zsizze 是符号常量、base/具体字段保持具体
        let Some(Val::List(items)) = regs.get_last_if_initialized(zpma) else {
            panic!("zpma_regions 应已初始化为 Val::List")
        };
        assert_eq!(items.len(), 2);
        let ram = match &items[0] {
            Val::Struct(fields) => fields,
            other => panic!("region 必须是 Struct，实际 {:?}", other),
        };
        let size_id = shared_state.symtab.get(&zencode::encode("size")).unwrap();
        match ram.get(&size_id) {
            Some(Val::Symbolic(sym)) => assert_eq!(*sym, records[0].1, "zsizze 应取声明并记录的符号常量"),
            other => panic!("符号 region 的 zsizze 必须是 Symbolic，实际 {:?}", other),
        }
        let base_id = shared_state.symtab.get(&zencode::encode("base")).unwrap();
        match ram.get(&base_id) {
            Some(Val::Bits(bv)) => assert_eq!(bv.lower_u64(), 0x8000_0000),
            other => panic!("base 必须保持具体，实际 {:?}", other),
        }
        let mmio = match &items[1] {
            Val::Struct(fields) => fields,
            other => panic!("region 必须是 Struct，实际 {:?}", other),
        };
        match mmio.get(&size_id) {
            Some(Val::Bits(bv)) => assert_eq!(bv.lower_u64(), 0x0200_0000, "具体 region 的 zsizze 保持具体"),
            other => panic!("具体 region 的 zsizze 必须是 Bits，实际 {:?}", other),
        }

        // 域约束已进入 solver：Sat 且模型值落在 [0x1000, 0x80000000000] 内
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);
        match model.get_var(records[0].1).unwrap() {
            isla_lib::smt::ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits64(bv)) => {
                let size = bv.lower_u64();
                assert!(size >= 0x1000 && size <= 0x80000000000, "模型 size={:#x} 应在声明域内", size);
            }
            other => panic!("size 模型值必须是 64 位位向量，实际 {:?}", other),
        }
    }

    /// W21：mstatus 形状（struct zMstatus { zbits: bits(64) }）的最小夹具——
    /// symtab/type_info/registers 建出与 rv64d.ir 同形的平铺 CSR。
    struct SymbolicCsrFixture {
        shared_state: SharedState<'static, B64>,
        mstatus_name: Name,
        satp_name: Name,
    }

    fn intern_static(text: &str) -> &'static str {
        Box::leak(text.to_string().into_boxed_str())
    }

    fn symbolic_csr_fixture() -> SymbolicCsrFixture {
        let mut symtab = Symtab::new();
        let mstatus_name = symtab.intern(intern_static(&zencode::encode("mstatus")));
        let satp_name = symtab.intern(intern_static(&zencode::encode("satp")));
        let zbits_field = symtab.intern(intern_static(&zencode::encode("bits")));
        let mstatus_struct = symtab.intern(intern_static("zMstatus"));

        let mut structs = HashMap::new();
        let mut mstatus_fields = BTreeMap::new();
        mstatus_fields.insert(zbits_field, Ty::Bits(64));
        structs.insert(mstatus_struct, mstatus_fields);
        let type_info = IRTypeInfo {
            structs,
            enums: HashMap::new(),
            enum_members: HashMap::new(),
            unions: HashMap::new(),
            union_ctors: HashSet::new(),
        };

        let arch: &'static [isla_lib::ir::Def<Name, B64>] = Box::leak(Vec::new().into_boxed_slice());
        let mut shared_state = SharedState::new(
            symtab,
            arch,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        shared_state.registers.insert(mstatus_name, Ty::Struct(mstatus_struct));
        shared_state.registers.insert(satp_name, Ty::Bits(64));
        SymbolicCsrFixture { shared_state, mstatus_name, satp_name }
    }

    fn symbolic_csr(
        name: &str,
        pin_mask: u64,
        pin_value: u64,
        groups: Vec<Vec<u32>>,
        derive: Option<isla_lib::config::DerivedBitConfig>,
    ) -> SymbolicRegisterConfig {
        SymbolicRegisterConfig {
            name: name.to_string(),
            pin_mask,
            pin_value,
            nonzero_groups: groups,
            derive_bit: derive,
        }
    }

    /// mstatus.SD 派生形状（W22）：SD(63) ⇔ FS[14:13]=11 ∨ VS[10:9]=11 ∨ XS[16:15]=11。
    fn sd_derive() -> isla_lib::config::DerivedBitConfig {
        isla_lib::config::DerivedBitConfig { bit: 63, groups: vec![vec![14, 13], vec![10, 9], vec![16, 15]] }
    }

    /// FS/VS/XS 三个位组是否全非 11（Dirty）——派生等价测试的"干净态"判定。
    fn all_groups_clean(value: u64) -> bool {
        ![(13, 14), (9, 10), (15, 16)]
            .iter()
            .any(|&(lo, hi)| value >> lo & ((1 << (hi - lo + 1)) - 1) == (1 << (hi - lo + 1)) - 1)
    }

    fn mstatus_symbolic_val(target: &RV64<B64>, name: &Name) -> Sym {
        match target.pre_state().get(name).expect("mstatus 应有 pre_state 记录") {
            Val::Struct(fields) => match fields.values().next().expect("单字段 struct") {
                Val::Symbolic(sym) => *sym,
                other => panic!("mstatus.bits 应是 Symbolic，实际 {:?}", other),
            },
            other => panic!("mstatus 应包装为 Struct，实际 {:?}", other),
        }
    }

    /// 注入：struct 包装形状正确、执行帧与 pre_state 同一符号、satp 平铺形状
    /// 直接 Symbolic；pin 与 nonzero 断言都真实进入 solver（违反即 Unsat）。
    #[test]
    fn symbolic_csrs_injection_shapes_and_constraints() {
        let fixture = symbolic_csr_fixture();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut regs = RegisterBindings::new();
        let mstatus_ty = Ty::Struct(Name::from_u32(u32::MAX));
        regs.insert(fixture.mstatus_name, false, UVal::Uninit(&mstatus_ty));
        regs.insert(fixture.satp_name, false, UVal::Uninit(&Ty::Bits(64)));
        let mut target = rv64();
        target.symbolic_csrs = vec![
            symbolic_csr("mstatus", 0x8000_0030_0000_0000, 0, vec![vec![13, 14]], None),
            symbolic_csr("satp", 0, 0, vec![], None),
        ];

        target.apply_symbolic_csrs_to_registers(&mut regs, &fixture.shared_state, &mut solver).unwrap();

        let mstatus_sym = mstatus_symbolic_val(&target, &fixture.mstatus_name);
        // 执行帧与 pre_state 共用同一符号
        match regs.get_last_if_initialized(fixture.mstatus_name).unwrap() {
            Val::Struct(fields) => match fields.values().next().unwrap() {
                Val::Symbolic(sym) => assert_eq!(*sym, mstatus_sym),
                other => panic!("执行帧 mstatus.bits 应是 Symbolic，实际 {:?}", other),
            },
            other => panic!("执行帧 mstatus 应是 Struct，实际 {:?}", other),
        }
        let satp_sym = match target.pre_state().get(&fixture.satp_name).unwrap() {
            Val::Symbolic(sym) => *sym,
            other => panic!("satp 平铺形状应直接 Symbolic，实际 {:?}", other),
        };
        assert_ne!(mstatus_sym, satp_sym, "两个 CSR 的符号常量必须独立");

        // pin 断言：SD(63)|MBE(37)|SBE(36) 钉 0，置任一位即 Unsat
        for violating_bit in [63, 37, 36] {
            let c2 = Context::new(Config::new());
            let mut s2 = Solver::<B64>::new(&c2);
            let sym = s2.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
            let mask = 0x8000_0030_0000_0000u64;
            s2.assert(smtlib::Exp::Eq(
                Box::new(smtlib::Exp::Bvand(Box::new(smtlib::Exp::Var(sym)), Box::new(smtlib::bits64(mask, 64)))),
                Box::new(smtlib::bits64(0, 64)),
            ));
            s2.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(1 << violating_bit, 64));
            assert_eq!(s2.check_sat(SourceLoc::unknown()), SmtResult::Unsat, "钉死位 {} 不应可置 1", violating_bit);
        }

        // nonzero 断言：FS(13,14) 组非零，FS=00 即 Unsat
        let c3 = Context::new(Config::new());
        let mut s3 = Solver::<B64>::new(&c3);
        let sym = s3.declare_const(smtlib::Ty::BitVec(64), SourceLoc::unknown());
        s3.assert(smtlib::Exp::Not(Box::new(smtlib::Exp::Eq(
            Box::new(smtlib::Exp::Bvor(
                Box::new(smtlib::Exp::Extract(14, 14, Box::new(smtlib::Exp::Var(sym)))),
                Box::new(smtlib::Exp::Extract(13, 13, Box::new(smtlib::Exp::Var(sym)))),
            )),
            Box::new(smtlib::bits64(0, 1)),
        ))));
        s3.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(0, 64));
        assert_eq!(s3.check_sat(SourceLoc::unknown()), SmtResult::Unsat, "FS=00 应被 nonzero 组断言排除");

        // 注入后的主 solver 仍 Sat（合法域非空）
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    }

    /// W22：SD 派生等价（双向）。构造与 csr_sym 配置同形的注入（pin 掉
    /// MBE/SBE/UXL/SXL、FS≠0 域、SD 派生），验证四个方向：
    /// ① FS=11 且组外位非 11 → SD 必须 1（等值 Sat + 模型位核对）；
    /// ② FS=11 ∧ SD=0 → Unsat（正向蕴含）；
    /// ③ FS/VS/XS 全非 11 ∧ SD=1 → Unsat（反向蕴含：SD=1 推某组=11）；
    /// ④ 全组干净 ∧ SD=0 → Sat（合法域非空）。
    #[test]
    fn symbolic_csrs_derive_bit_equivalence_is_bidirectional() {
        let pin_mask = 0x0000_183C_0000_0000u64;
        let pin_value = 0x0000_1008_0000_0000u64;
        let fixture = symbolic_csr_fixture();
        // Solver 借用局部 Context，不能跨闭包返回，改回调式：装配 + 可选整值
        // 强制 + 断言回调在 Context 存活期内执行。
        let inject = |forced: Option<u64>, check: &dyn Fn(&mut Solver<B64>, Sym)| {
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            let mut regs = RegisterBindings::new();
            let mstatus_ty = Ty::Struct(Name::from_u32(u32::MAX));
            regs.insert(fixture.mstatus_name, false, UVal::Uninit(&mstatus_ty));
            let mut target = rv64();
            target.symbolic_csrs =
                vec![symbolic_csr("mstatus", pin_mask, pin_value, vec![vec![13, 14]], Some(sd_derive()))];
            target.apply_symbolic_csrs_to_registers(&mut regs, &fixture.shared_state, &mut solver).unwrap();
            let sym = mstatus_symbolic_val(&target, &fixture.mstatus_name);
            if let Some(value) = forced {
                solver.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(value, 64));
            }
            check(&mut solver, sym);
        };

        // FS=11（Dirty）、VS/XS 非 11、SD=1、钉死位=11 的合法值
        let fs_dirty_sd1 = 1 << 63 | 0x6000 | pin_value;
        assert_eq!(fs_dirty_sd1 >> 13 & 0b11, 0b11, "前置：FS=11");

        // ① 正向：FS=11 的合法值应 Sat，且模型 SD 位 = 1
        inject(Some(fs_dirty_sd1), &|solver, sym| {
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat, "FS=11 且 SD=1 应满足派生等价");
            let mut model = Model::new(solver);
            match model.get_var(sym).unwrap() {
                isla_lib::smt::ModelVal::Exp(smtlib::Exp::Bits64(bv)) => {
                    assert_eq!(bv.lower_u64() >> 63 & 1, 1, "FS=11 时模型 SD 必 1");
                }
                other => panic!("模型值应为 64 位位向量，实际 {:?}", other),
            }
        });

        // ② 正向违反：FS=11 ∧ SD=0 → Unsat
        inject(Some(fs_dirty_sd1 & !(1 << 63)), &|solver, _sym| {
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat, "FS=11 时 SD=0 应 Unsat");
        });

        // ③ 反向违反：全组干净（FS/VS/XS 均 ≠11）∧ SD=1 → Unsat
        let clean_sd1 = 1 << 63 | (1 << 13) | pin_value; // FS=01（非 0 域）其余组非 11
        assert!(all_groups_clean(clean_sd1), "前置：三组均非 11");
        inject(Some(clean_sd1), &|solver, _sym| {
            assert_eq!(
                solver.check_sat(SourceLoc::unknown()),
                SmtResult::Unsat,
                "全组非 11 时 SD=1 应 Unsat（反向蕴含）"
            );
        });

        // ④ 全组干净 ∧ SD=0 → Sat
        let clean_sd0 = (1 << 13) | pin_value;
        inject(Some(clean_sd0), &|solver, _sym| {
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat, "全组非 11 且 SD=0 应满足派生等价");
        });

        // ⑤ 仅约束 SD=1（不固定具体值）：模型必须自选某组 = 11
        inject(None, &|solver, sym| {
            solver.assert_eq(smtlib::Exp::Extract(63, 63, Box::new(smtlib::Exp::Var(sym))), smtlib::bits64(1, 1));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let mut model = Model::new(solver);
            match model.get_var(sym).unwrap() {
                isla_lib::smt::ModelVal::Exp(smtlib::Exp::Bits64(bv)) => {
                    let value = bv.lower_u64();
                    assert!(!all_groups_clean(value), "SD=1 的模型必须有某位组全 1：{:#x}", value);
                }
                other => panic!("模型值应为 64 位位向量，实际 {:?}", other),
            }
        });
    }

    /// W22：派生位/组位超出实际寄存器位宽是配置与 IR 的矛盾，注入期硬 panic。
    #[test]
    fn symbolic_csrs_derive_bit_rejects_out_of_width_bits() {
        let fixture = symbolic_csr_fixture();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut symtab = Symtab::new();
            let narrow_name = symtab.intern(intern_static(&zencode::encode("narrow_csr")));
            let mut structs = HashMap::new();
            let zbits_field = symtab.intern(intern_static(&zencode::encode("bits")));
            let struct_id = symtab.intern(intern_static("zNarrow"));
            let mut fields = BTreeMap::new();
            fields.insert(zbits_field, Ty::Bits(32));
            structs.insert(struct_id, fields);
            let type_info = IRTypeInfo {
                structs,
                enums: HashMap::new(),
                enum_members: HashMap::new(),
                unions: HashMap::new(),
                union_ctors: HashSet::new(),
            };
            let arch: &'static [isla_lib::ir::Def<Name, B64>] = Box::leak(Vec::new().into_boxed_slice());
            let mut shared_state = SharedState::new(
                symtab,
                arch,
                type_info,
                HashSet::new(),
                HashSet::new(),
                HashSet::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            );
            shared_state.registers.insert(narrow_name, Ty::Bits(32));
            let mut target = rv64();
            // 派生位 40 在 32 位寄存器外
            target.symbolic_csrs = vec![symbolic_csr(
                "narrow_csr",
                0,
                0,
                vec![],
                Some(isla_lib::config::DerivedBitConfig { bit: 40, groups: vec![vec![1, 0]] }),
            )];
            let mut regs = RegisterBindings::new();
            regs.insert(narrow_name, false, UVal::Uninit(&Ty::Bits(32)));
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            target.apply_symbolic_csrs_to_registers(&mut regs, &shared_state, &mut solver).unwrap();
        }));
        assert!(result.is_err(), "派生位超出位宽应 panic");
        let _ = fixture;
    }

    /// 具象化：concretize_symbolic_csrs 按模型把符号 CSR 换成具体值，供 encdec
    /// 门使用；未注入记录（空 pre_state）是调用序错误，硬 panic。
    #[test]
    fn symbolic_csrs_concretize_for_gate() {
        let fixture = symbolic_csr_fixture();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut regs = RegisterBindings::new();
        let mstatus_ty = Ty::Struct(Name::from_u32(u32::MAX));
        regs.insert(fixture.mstatus_name, false, UVal::Uninit(&mstatus_ty));
        let mut target = rv64();
        target.symbolic_csrs = vec![symbolic_csr("mstatus", 0x8000_0030_0000_0000, 0, vec![vec![13, 14]], None)];
        target.apply_symbolic_csrs_to_registers(&mut regs, &fixture.shared_state, &mut solver).unwrap();
        let sym = mstatus_symbolic_val(&target, &fixture.mstatus_name);

        // 钉一个合法模型值：FS=01（Initial），钉死位全 0
        let model_value = 1_u64 << 13;
        solver.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(model_value, 64));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        let mut model = Model::new(&solver);

        let gate_regs = target.concretize_symbolic_csrs(&regs, &mut model, &fixture.shared_state).unwrap();
        match gate_regs.get_last_if_initialized(fixture.mstatus_name).unwrap() {
            Val::Struct(fields) => match fields.values().next().unwrap() {
                Val::Bits(bv) => assert_eq!(bv.lower_u64(), model_value, "门的 mstatus 应是模型值"),
                other => panic!("具象化后 mstatus.bits 应是 Bits，实际 {:?}", other),
            },
            other => panic!("具象化后 mstatus 应保持 Struct 形状，实际 {:?}", other),
        }
        // 原表不被污染（门只读克隆）
        assert!(matches!(regs.get_last_if_initialized(fixture.mstatus_name).unwrap(), Val::Struct(_)));
    }

    /// 不支持形状（两字段 struct）与超宽 pin_mask 均硬 panic（防御式）。
    #[test]
    fn symbolic_csrs_rejects_unsupported_shapes() {
        let mut symtab = Symtab::new();
        let wide_name = symtab.intern(intern_static(&zencode::encode("wide_csr")));
        let two_field_name = symtab.intern(intern_static(&zencode::encode("two_field_csr")));
        let struct_id = symtab.intern(intern_static("zTwoField"));
        let f0 = symtab.intern(intern_static(&zencode::encode("a")));
        let f1 = symtab.intern(intern_static(&zencode::encode("b")));
        let mut structs = HashMap::new();
        let mut fields = BTreeMap::new();
        fields.insert(f0, Ty::Bits(32));
        fields.insert(f1, Ty::Bits(32));
        structs.insert(struct_id, fields);
        let type_info = IRTypeInfo {
            structs,
            enums: HashMap::new(),
            enum_members: HashMap::new(),
            unions: HashMap::new(),
            union_ctors: HashSet::new(),
        };
        let arch: &'static [isla_lib::ir::Def<Name, B64>] = Box::leak(Vec::new().into_boxed_slice());
        let mut shared_state = SharedState::new(
            symtab,
            arch,
            type_info,
            HashSet::new(),
            HashSet::new(),
            HashSet::new(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        shared_state.registers.insert(wide_name, Ty::Bits(32));
        shared_state.registers.insert(two_field_name, Ty::Struct(struct_id));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut target = rv64();
            target.symbolic_csrs = vec![symbolic_csr("wide_csr", 1 << 40, 0, vec![], None)];
            let mut regs = RegisterBindings::new();
            regs.insert(wide_name, false, UVal::Uninit(&Ty::Bits(32)));
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            target.apply_symbolic_csrs_to_registers(&mut regs, &shared_state, &mut solver).unwrap();
        }));
        assert!(result.is_err(), "pin_mask 超宽应 panic");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut target = rv64();
            target.symbolic_csrs = vec![symbolic_csr("two_field_csr", 0, 0, vec![], None)];
            let mut regs = RegisterBindings::new();
            let two_field_ty: &'static Ty<Name> = Box::leak(Box::new(Ty::Struct(struct_id)));
            regs.insert(two_field_name, false, UVal::Uninit(two_field_ty));
            let context = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&context);
            target.apply_symbolic_csrs_to_registers(&mut regs, &shared_state, &mut solver).unwrap();
        }));
        assert!(result.is_err(), "两字段 struct 应 panic");
    }

    /// 端到端输出：注入后 pre_state 的符号 CSR 在模型下求解，solve_pre_state
    /// 输出含具体模型值（FS≠0 可见），与 W17 符号 PMA size 的侧通道输出互补
    /// （CSR 走 pre_state 主通道，无需额外记录）。
    #[test]
    fn solve_pre_state_outputs_symbolic_csr_model_value() {
        let fixture = symbolic_csr_fixture();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut target = rv64();
        target.symbolic_csrs = vec![symbolic_csr("mstatus", 0x8000_0030_0000_0000, 0, vec![vec![13, 14]], None)];
        let mut regs = RegisterBindings::new();
        let mstatus_ty = Ty::Struct(Name::from_u32(u32::MAX));
        regs.insert(fixture.mstatus_name, false, UVal::Uninit(&mstatus_ty));
        target.apply_symbolic_csrs_to_registers(&mut regs, &fixture.shared_state, &mut solver).unwrap();
        let sym = mstatus_symbolic_val(&target, &fixture.mstatus_name);
        solver.assert_eq(smtlib::Exp::Var(sym), smtlib::bits64(1 << 14, 64));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);

        let mut model = Model::new(&solver);
        let state = target.solve_pre_state(&mut model, &fixture.shared_state).unwrap();
        let mstatus = state.get("mstatus").expect("mstatus 模型值应输出");
        assert!(mstatus.contains("4000"), "FS=10 应体现在输出中：{}", mstatus);
    }
}

#[cfg(test)]
mod initial_state_tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::{Config, Context};

    #[test]
    fn initial_state_and_symbolic_csr_share_the_same_fcsr_value() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let fcsr = symtab.intern("zfcsr");
        let mut shared = SharedState::empty(symtab);
        shared.registers.insert(fcsr, Ty::Bits(32));
        let mut regs = RegisterBindings::new();
        regs.insert(fcsr, false, UVal::Init(Val::Bits(B64::new(0, 32))));
        let mut target = RV64::<B64>::default();
        target.initial_state =
            vec![InitialRegisterConfig { name: "fcsr".into(), fields: vec![(Some((7, 7)), Some(1))] }];
        target.symbolic_csrs = vec![SymbolicRegisterConfig {
            name: "fcsr".into(),
            pin_mask: 1,
            pin_value: 1,
            nonzero_groups: Vec::new(),
            derive_bit: None,
        }];
        target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new()).unwrap();
        target.apply_symbolic_csrs_to_registers(&mut regs, &shared, &mut solver).unwrap();
        let current = target.pre_state().get(&fcsr).unwrap();
        let exp = smt_value(current, SourceLoc::unknown()).unwrap();
        solver.assert_eq(smtlib::Exp::Extract(7, 7, Box::new(exp.clone())), smtlib::bits64(0, 1));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
        let mut solver = Solver::<B64>::new(&context);
        let mut target = RV64::<B64>::default();
        target.initial_state =
            vec![InitialRegisterConfig { name: "fcsr".into(), fields: vec![(Some((7, 7)), Some(1))] }];
        let mut fixed = HashMap::new();
        fixed.insert(fcsr, Val::Bits(B64::new(0x80, 32)));
        target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &fixed).unwrap();
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
    }

    #[test]
    fn initial_state_pins_only_selected_bits() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for fs in 0..4 {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut symtab = Symtab::new();
            let name = symtab.intern("zmstatus");
            let wrapper = symtab.intern("zMstatus");
            let bits = symtab.intern("zbits");
            let mut shared = SharedState::empty(symtab);
            shared.registers.insert(name, Ty::Struct(wrapper));
            shared.type_info.structs.insert(wrapper, BTreeMap::from([(bits, Ty::Bits(64))]));
            let mut target = RV64::<B64>::default();
            target.initial_state = vec![InitialRegisterConfig {
                name: "mstatus".into(),
                fields: vec![(Some((10, 9)), Some(3)), (Some((14, 13)), None), (Some((12, 11)), None)],
            }];
            let mut regs = RegisterBindings::new();
            regs.insert(name, false, UVal::Init(Val::Poison));
            target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new()).unwrap();
            let Val::Struct(fields) = target.pre_state.get(&name).unwrap() else { panic!() };
            let exp = smt_value(fields.get(&bits).unwrap(), SourceLoc::unknown()).unwrap();
            solver.assert_eq(smtlib::Exp::Extract(14, 13, Box::new(exp.clone())), smtlib::bits64(fs, 2));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            solver.assert_eq(smtlib::Exp::Extract(10, 9, Box::new(exp)), smtlib::bits64(0, 2));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
        }
    }
    #[test]
    fn initial_state_whole_register_and_validation() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for (width, range, concrete, valid) in [
            (8, None, Some(42), true),
            (64, None, Some(u64::MAX), true),
            (8, None, Some(256), false),
            (8, Some((8, 7)), None, false),
            (8, Some((7, 5)), Some(7), true),
            (8, None, None, true),
        ] {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut symtab = Symtab::new();
            let name = symtab.intern("zfcsr");
            let mut shared = SharedState::empty(symtab);
            shared.registers.insert(name, Ty::Bits(width));
            let mut regs = RegisterBindings::new();
            regs.insert(name, false, UVal::Init(Val::Bits(B64::new(0, width))));
            let mut target = RV64::<B64>::default();
            target.initial_state = vec![InitialRegisterConfig { name: "fcsr".into(), fields: vec![(range, concrete)] }];
            let result = target.setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new());
            assert_eq!(result.is_ok(), valid);
            if !valid {
                continue;
            }
            let Val::Symbolic(symbol) = target.pre_state.get(&name).unwrap() else { panic!() };
            assert!(matches!(regs.get_last_if_initialized(name), Some(Val::Symbolic(read)) if read == symbol));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let (high, low) = range.unwrap_or((width - 1, 0));
            let check = smtlib::Exp::Extract(high, low, Box::new(smtlib::Exp::Var(*symbol)));
            if let Some(n) = concrete {
                solver.assert_eq(check, smtlib::bits64(n ^ 1, high - low + 1));
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat);
            } else {
                solver.assert_eq(check, smtlib::bits64(255, width));
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            }
        }
    }

    #[test]
    fn initial_state_rejects_missing_register() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let shared = SharedState::empty(Symtab::new());
        let mut target = RV64::<B64>::default();
        target.initial_state = vec![InitialRegisterConfig { name: "missing".into(), fields: vec![(None, None)] }];
        assert!(target
            .setup_pre_state(&mut RegisterBindings::new(), &Bindings::default(), &shared, &mut solver, &HashMap::new())
            .is_err());
    }
    #[test]
    fn initial_state_rejects_unsupported_types_before_symbolization() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        for ty in
            [Ty::List(Box::new(Ty::Bits(64))), Ty::AnyBits, Ty::Bool, Ty::Bits(0), Ty::Struct(Name::from_u32(999))]
        {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut symtab = Symtab::new();
            let name = symtab.intern("ztest_register");
            let wrapper = symtab.intern("zWrapper");
            let a = symtab.intern("za");
            let b = symtab.intern("zb");
            let mut shared = SharedState::empty(symtab);
            let ty = if matches!(ty, Ty::Struct(_)) { Ty::Struct(wrapper) } else { ty };
            shared.type_info.structs.insert(wrapper, BTreeMap::from([(a, Ty::Bits(32)), (b, Ty::Bits(32))]));
            shared.registers.insert(name, ty);
            let mut target = RV64::<B64>::default();
            target.initial_state =
                vec![InitialRegisterConfig { name: "test_register".into(), fields: vec![(None, None)] }];
            let mut regs = RegisterBindings::new();
            let error = target
                .setup_pre_state(&mut regs, &Bindings::default(), &shared, &mut solver, &HashMap::new())
                .unwrap_err();
            assert!(
                matches!(error, ExecError::Type(ref message, _) if message.contains("initial_state.test_register"))
            );
            assert_eq!(target.pre_state.len(), 0);
            assert!(regs.get_last_if_initialized(name).is_none());
        }
    }
}
