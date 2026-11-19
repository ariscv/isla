//! solve-state 的样本配置与终态适配；算法由 isla-lib 两种模式共用。
use super::target::Target;
use isla_lib::bitvector::BV;
use isla_lib::config::{MergeEnumerationConfig, MergeEnumerationMode, SampleOutputConfig, SampleOutputFormat};
use isla_lib::executor::samples::outputs::SampleOutputs;
use isla_lib::executor::samples::{SampleChecker, SamplePath};
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{SharedState, Val};
use isla_lib::register::RegisterBindings;
use std::collections::BTreeMap;
use std::path::PathBuf;

#[derive(Default)]
pub struct SampleOptions {
    pub witness_randomization_seed: Option<u64>,
    pub filter_model_exceptions: Vec<String>,
    pub path_cache: super::path_cache::Options,
    pub fuzz: Option<super::fuzz::Options>,
    pub check: Option<PathBuf>,
    pub limit: Option<usize>,
    pub report: Option<PathBuf>,
    pub judge: Option<PathBuf>,
    pub resident: Option<PathBuf>,
    pub resident_out: Option<PathBuf>,
    pub resident_fast: bool,
    pub resident_batch_size: Option<usize>,
}

impl SampleOptions {
    pub fn validate(&self) -> Result<(), String> {
        if self.resident_batch_size == Some(0) {
            return Err("judge resident 批大小必须大于零".into());
        }
        if self.resident_batch_size.is_some() && (self.resident.is_none() || self.resident_fast) {
            return Err("judge resident 批大小仅适用于普通 --judge-resident".into());
        }
        if self.filter_model_exceptions.iter().any(|name| name.trim().is_empty() || name != name.trim()) {
            return Err("异常过滤必须使用非空构造子名称，且不得有首尾空格".into());
        }
        if self.path_cache.dag_only
            && (self.path_cache.write.is_none()
                || self.fuzz.is_some()
                || self.check.is_some()
                || self.resident.is_some())
        {
            return Err("--path-cache-only 只支持独立缓存写出；请读回缓存后导出或认证".into());
        }
        if self.path_cache.write.is_some() && self.resident.is_some() {
            return Err("缓存写出不能与常驻 judge 同时运行".into());
        }
        if self.resident_fast && self.resident.is_none() {
            return Err("--judge-resident-fast 需要 --judge-resident".into());
        }
        if self.resident.is_some() != self.resident_out.is_some() {
            return Err("--judge-resident 与 --judge-resident-out 必须同时指定".into());
        }
        if let Some(input) = &self.resident {
            if self.resident_out.as_ref() == Some(input) || self.check.is_some() || self.judge.is_some() {
                return Err("常驻 judge 必须使用独立输入输出，且不得与 J1 同时运行".into());
            }
        }
        if self.check.is_none() && (self.limit.is_some() || self.report.is_some()) {
            return Err("--check-samples-limit/--check-samples-report 需要 --check-samples".into());
        }
        if self.check.is_none() && self.judge.is_some() {
            return Err("--check-samples-judge 需要 --check-samples".into());
        }
        if self.limit == Some(0) {
            return Err("--check-samples-limit 必须大于零".into());
        }
        if let Some(path) = &self.check {
            if self.report.as_ref() == Some(path) {
                return Err("检查报告不得覆盖样本输入".into());
            }
        }
        if let Some(judge) = &self.judge {
            if self.check.as_ref() == Some(judge) || self.report.as_ref() == Some(judge) {
                return Err("judge 输出不得覆盖样本输入或检查报告".into());
            }
        }
        Ok(())
    }
}

pub struct SampleSession {
    pub witness_randomization_seed: Option<u64>,
    pub filter_model_exceptions: Vec<String>,
    pub path_cache: super::path_cache::Options,
    pub fuzz: Option<super::fuzz::Session>,
    pub writer: Option<SampleOutputs>,
    pub checker: Option<SampleChecker>,
    pub resident: Option<SampleChecker>,
    pub retain_solutions: bool,
    pub resident_fast: bool,
    pub resident_batch_size: Option<usize>,
}
impl SampleSession {
    pub fn new(options: &SampleOptions, enumeration: Option<&MergeEnumerationConfig>) -> Result<Self, String> {
        options.validate()?;
        let counting = enumeration.is_some_and(|config| config.enabled && config.mode != MergeEnumerationMode::Samples);
        let outputs = enumeration.map_or(&[][..], |config| config.outputs.as_slice());
        let mut configured = if counting { Vec::new() } else { outputs.to_vec() };
        if let Some(path) = std::env::var_os("ISLA_EXPORT_SAMPLES").filter(|_| !counting) {
            let path = PathBuf::from(path);
            if configured.iter().any(|output| output.format == SampleOutputFormat::V1Jsonl || output.path == path) {
                return Err("ISLA_EXPORT_SAMPLES 不得与 TOML 输出路径或 v1_jsonl 后端重复".into());
            }
            configured.push(SampleOutputConfig { format: SampleOutputFormat::V1Jsonl, path });
        }
        if options.path_cache.dag_only && !configured.is_empty() {
            return Err("--path-cache-only 不同时导出样本；请读回缓存后枚举".into());
        }
        if options.check.as_ref().is_some_and(|input| configured.iter().any(|output| &output.path == input)) {
            return Err("样本输出不得覆盖检查输入".into());
        }
        if options.report.as_ref().is_some_and(|report| configured.iter().any(|output| &output.path == report)) {
            return Err("检查报告不得覆盖样本输出".into());
        }
        if options.judge.as_ref().is_some_and(|judge| configured.iter().any(|output| &output.path == judge)) {
            return Err("judge 输出不得覆盖样本输出".into());
        }
        for path in [&options.resident, &options.resident_out].into_iter().flatten() {
            if configured.iter().any(|output| &output.path == path) {
                return Err("常驻 judge 输入输出不得与样本输出重叠".into());
            }
        }
        let resident = options
            .resident
            .as_ref()
            .map(|path| {
                SampleChecker::load_judge_inputs(path)?.with_judge_output(options.resident_out.as_ref().unwrap())
            })
            .transpose()?;
        let checker = options
            .check
            .as_ref()
            .map(|path| {
                let checker = SampleChecker::load(path, options.limit)?;
                match &options.judge {
                    Some(judge) => checker.with_judge_output(judge),
                    None => Ok(checker),
                }
            })
            .transpose()?;
        let limit = enumeration.and_then(|config| config.max_output_bytes);
        if limit.is_some_and(|limit| limit < 1024) {
            return Err("max_output_bytes 至少为1024，必须容纳文件头和正常结束标记".into());
        }
        let streaming = configured.len() == 1 && enumeration.is_some_and(MergeEnumerationConfig::streams_binary);
        if limit.is_some() && !counting && !streaming {
            return Err("max_output_bytes 要求只启用一个 binary 后端且 sample_stride=1".into());
        }
        let writer = (!configured.is_empty()).then(|| {
            if streaming {
                SampleOutputs::open_streaming(&configured[0].path, limit)
            } else {
                SampleOutputs::open(&configured)
            }
        });
        Ok(Self {
            witness_randomization_seed: options.witness_randomization_seed,
            filter_model_exceptions: options.filter_model_exceptions.clone(),
            path_cache: options.path_cache.clone(),
            fuzz: options.fuzz.as_ref().map(super::fuzz::Session::new).transpose()?,
            writer,
            checker,
            resident,
            retain_solutions: outputs.is_empty(),
            resident_fast: options.resident_fast,
            resident_batch_size: options.resident_batch_size,
        })
    }
    pub fn enabled(&self) -> bool {
        self.path_cache.enabled()
            || self.fuzz.is_some()
            || self.writer.is_some()
            || self.checker.is_some()
            || self.resident.is_some()
    }
    pub fn finish(&self, options: &SampleOptions, completed: bool) {
        if let Some(writer) = &self.writer {
            writer.finish();
        }
        if let Some(checker) = &self.checker {
            let mut report = checker.report();
            report["completed"] = serde_json::json!(completed);
            let text = serde_json::to_string_pretty(&report).expect("报告序列化失败");
            if let Some(path) = &options.report {
                std::fs::write(path, &text).expect("写入样本报告失败");
            }
            eprintln!("[SAMPLE_CHECK_REPORT] {}", serde_json::to_string(&report).unwrap());
        }
    }
}

/// 从真实完成检查点导出，现场帧和缓存使用同一守卫枚举器。
pub fn export_cached_path<B: BV>(
    path: &super::resident::ResidentPath<B>,
    solver: &mut isla_lib::smt::Solver<B>,
    shared: &SharedState<B>,
    target: &dyn Target<B>,
    limits: &isla_lib::executor::ExecutionLimits,
    writer: Option<&SampleOutputs>,
    checker: Option<&SampleChecker>,
) -> Result<Option<serde_json::Value>, isla_lib::error::ExecError> {
    use isla_lib::error::ExecError;
    use isla_lib::executor::{MergeEnumeration, TaskState};
    if let Some(checker) = checker {
        checker.check_path_with_judge(&path.path, solver, shared, path.signature, &path.records, |sample, model| {
            sample.isa_state = isa_state(target, sample, model, shared)?;
            Ok(())
        })?;
    }
    let Some(writer) = writer else { return Ok(None) };
    let output_path = writer.start_path(path.signature);
    let complete = |class, metadata: &serde_json::Value| {
        writer.finish_class(output_path, Some(class), metadata);
        Ok(())
    };
    let state = TaskState::new().with_execution_limits(limits.clone());
    let enumeration = MergeEnumeration {
        records: &path.records,
        pure_definitions: &path.pure_definitions,
        signature: path.signature,
    }
    .enumerate_merges_output_with(
        solver,
        &state,
        shared,
        &path.path.result,
        &|class, solution, slices, truncated, model| {
            if let Some(reason) = writer.stop_reason() {
                return Err(ExecError::SampleOutputStopped(reason));
            }
            let mut sample = path.path.materialize(model, shared, "merge", path.signature, Some(class))?;
            sample.isa_state = isa_state(target, &sample, model, shared)?;
            sample.truncated = truncated;
            if !writer.append(output_path, solution, slices, sample) {
                return Err(ExecError::SampleOutputStopped(writer.stop_reason().unwrap()));
            }
            Ok(())
        },
        if writer.grouped() { Some(&complete) } else { None },
        false,
    )?;
    // 关闭枚举时只输出每条缓存路径的一个模型。judge 已使用上方的原路径约束。
    if enumeration.is_none() && writer.stop_reason().is_none() {
        assert_eq!(
            solver.check_sat(isla_lib::source_loc::SourceLoc::unknown()),
            isla_lib::smt::SmtResult::Sat,
            "缓存完成路径必须可满足"
        );
        let mut model = isla_lib::smt::Model::new(solver);
        model.set_complete_model(true);
        let mut sample = path.path.materialize(&mut model, shared, "merge", path.signature, None)?;
        sample.isa_state = isa_state(target, &sample, &mut model, shared)?;
        let accepted = writer.append(output_path, 0, &[], sample);
        if writer.grouped() && accepted {
            writer.finish_class(
                output_path,
                None,
                &serde_json::json!({"solution_count":1,"guard_assignment":{},"tested_slices":[],"truncated":false}),
            );
        }
    }
    writer
        .finish_path(output_path, enumeration.as_ref().is_some_and(|value| value["path_truncated"].as_bool().unwrap()));
    Ok(enumeration)
}

pub fn path<B: BV>(
    target: &dyn Target<B>,
    initial: &RegisterBindings<B>,
    frame: &LocalFrame<B>,
    shared: &SharedState<B>,
    instruction: &Val<B>,
    result: &Val<B>,
    trace: &isla_lib::smt::Trace<B>,
) -> SamplePath<B> {
    let mut pre: BTreeMap<_, _> = initial
        .iter()
        .filter_map(|(name, register)| {
            register
                .read_last_if_initialized()
                .map(|value| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
        })
        .collect();
    for (name, value) in target.pre_state().iter() {
        pre.insert(isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone());
    }
    // 入口没有初始化的寄存器可能在执行途中首次读取。事件保存的是完整寄存器值，
    // 即使访问了字段也能补齐前态；写入之后的读取不得倒灌成输入。
    let events = trace.to_vec();
    let mut written = std::collections::HashSet::new();
    for event in events.iter().rev() {
        match event {
            isla_lib::smt::Event::WriteReg(name, ..) => {
                written.insert(*name);
            }
            isla_lib::smt::Event::ReadReg(name, _, value) if !written.contains(name) => {
                pre.entry(isla_lib::zencode::decode(shared.symtab.to_str(*name))).or_insert_with(|| value.clone());
            }
            isla_lib::smt::Event::AssumeReg(name, accessor, value)
                if accessor.is_empty() && !written.contains(name) =>
            {
                pre.entry(isla_lib::zencode::decode(shared.symtab.to_str(*name))).or_insert_with(|| value.clone());
            }
            _ => (),
        }
    }
    let memory = events.into_iter().rev().filter(|event| event.is_memory_read_or_write()).cloned().collect();
    let post = frame
        .regs()
        .iter()
        .filter_map(|(name, register)| {
            register
                .read_last_if_initialized()
                .map(|value| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
        })
        .collect();
    pre.insert("$instruction".into(), instruction.clone());
    // 注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。
    // 样本按保存的 guard 过滤未执行臂；实际发生的每次读仍绑定 pre_memory，
    // 沿用既有初始内存规则及“写后读不同值”限制。原始主迹本身仍是并集。
    let memory_guards = frame
        .region_merge_records()
        .iter()
        .flat_map(|record| record.memory_reads.iter().map(|(index, guard, _)| (*index, guard.clone())))
        .chain(frame.arm_error_memory_guards().iter().cloned())
        .collect();
    SamplePath {
        terminal: if let Some(error) = frame.arm_error() {
            use isla_lib::error::IslaError;
            isla_lib::executor::samples::Terminal::ExecutionError {
                message: error.to_string(),
                location: error.source_loc().location_string(shared.symtab.files()),
            }
        } else {
            match frame.get_exception() {
                Some((_, location)) => {
                    isla_lib::executor::samples::Terminal::SailException { throw_location: location.into() }
                }
                None => isla_lib::executor::samples::Terminal::Normal,
            }
        },
        pre,
        post,
        result: result.clone(),
        memory,
        memory_guards,
    }
}

/// 样本已物化完整前态；复用其值格式化 ISA 状态，避免再抽取同一模型。
pub fn isa_state<B: BV>(
    target: &dyn Target<B>,
    sample: &isla_lib::executor::samples::Sample,
    model: &mut isla_lib::smt::Model<B>,
    shared: &SharedState<B>,
) -> Result<BTreeMap<String, String>, isla_lib::error::ExecError> {
    use isla_lib::error::ExecError;
    use isla_lib::fmtval::FmtVal;
    use isla_lib::smt::smtlib::Exp;
    use isla_lib::zencode;
    fn formatted<B: BV>(
        original: &Val<B>,
        value: &serde_json::Value,
        model: &mut isla_lib::smt::Model<B>,
        shared: &SharedState<B>,
    ) -> Result<Option<FmtVal>, ExecError> {
        match original {
            Val::Symbolic(_) => {
                let expression = if let Some(bits) = value.get("bits") {
                    Exp::Bits(bits.as_str().unwrap().bytes().rev().map(|bit| bit == b'1').collect())
                } else if let Some(value) = value.get("bool") {
                    Exp::Bool(value.as_bool().unwrap())
                } else if let Some(value) = value.get("enum") {
                    let name = shared.symtab.lookup(&zencode::encode(value.as_str().unwrap()));
                    let (member, _, enum_name) = shared.type_info.enum_members[&name];
                    Exp::Enum(isla_lib::smt::EnumMember {
                        enum_id: isla_lib::smt::EnumId::from_name(enum_name),
                        member,
                    })
                } else {
                    panic!("符号标量必须物化为位向量、布尔或枚举");
                };
                Ok(FmtVal::from_exp(&expression))
            }
            Val::Struct(fields) if fields.len() == 1 => {
                let (name, original) = fields.iter().next().unwrap();
                formatted(original, &value["struct"][zencode::decode(shared.symtab.to_str(*name))], model, shared)
            }
            Val::Ctor(_, original) => formatted(original, &value["value"], model, shared),
            // 具体值与混合位串沿用既有格式化，以保留原来的片段语义。
            Val::Bits(_) | Val::Bool(_) | Val::Enum(_) | Val::MixedBits(_) => {
                FmtVal::from_val(original, model).map(Some)
            }
            _ => FmtVal::from_val(original, model).map(Some),
        }
    }
    let mut state = BTreeMap::new();
    for (name, original) in target.pre_state().iter() {
        let name = zencode::decode(shared.symtab.to_str(*name));
        let value = sample.pre_registers.get(&name).expect("完整样本必须包含前态寄存器");
        if let Some(value) = formatted(original, value, model, shared)? {
            state.insert(name, value.to_str(shared));
        }
    }
    // target 的额外标量不在 pre_registers 中，按通用模型绑定查询。
    for (name, symbol) in target.model_bindings() {
        let value = model.get_var(*symbol)?;
        if let Some(value) = FmtVal::from_model_val(&value) {
            if !value.is_arbitrary() {
                state.insert(name.clone(), value.to_str(shared));
            }
        }
    }
    Ok(state)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn samples_preserve_lazy_register_input_without_treating_writes_as_input() {
        use isla_lib::bitvector::b64::B64;
        use isla_lib::ir::{Bindings, Symtab, Ty, UVal, TOP_LEVEL_LET};
        use isla_lib::smt::{Config, Context, Event, Model, SmtResult, Solver};
        use isla_lib::source_loc::SourceLoc;
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let mut symtab = Symtab::new();
        let encoded = isla_lib::zencode::encode("lazy_input");
        let register = symtab.intern(&encoded);
        let mut shared = SharedState::<B64>::empty(symtab);
        shared.registers.insert(register, Ty::Bits(64));
        for (read, assume, write) in
            [(true, false, false), (true, false, true), (false, true, true), (false, false, true)]
        {
            let context = Context::new(Config::new());
            let mut solver = Solver::new(&context);
            let mut initial = RegisterBindings::new();
            initial.insert(register, false, UVal::Uninit(&Ty::Bits(64)));
            let mut frame = LocalFrame::new(TOP_LEVEL_LET, &[], &Ty::Unit, None, &[]);
            frame.add_regs(&initial);
            frame.add_lets(&Bindings::default());
            let before = if read || assume {
                let value = frame
                    .regs_mut()
                    .get(register, &shared, &mut solver, SourceLoc::unknown())
                    .unwrap()
                    .unwrap()
                    .clone();
                solver.add_event(if assume {
                    Event::AssumeReg(register, vec![], value.clone())
                } else {
                    Event::ReadReg(register, vec![], value.clone())
                });
                Some(value)
            } else {
                None
            };
            if write {
                let value = Val::Bits(B64::new(7, 64));
                frame.regs_mut().assign(register, value.clone(), &shared);
                solver.add_event(Event::WriteReg(register, vec![], value));
            }
            let target = super::super::target::RV64::<B64>::default();
            let sample = path(&target, &initial, &frame, &shared, &Val::Unit, &Val::Unit, solver.trace());
            assert_eq!(sample.pre.get("lazy_input"), before.as_ref(), "懒初始化读取的原值必须进入样本前态");
            if write {
                assert_eq!(sample.post["lazy_input"], Val::Bits(B64::new(7, 64)));
            }
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let concrete = sample.materialize(&mut Model::new(&solver), &shared, "regression", 0, None).unwrap();
            assert_eq!(sample.check(&mut solver, &shared, &concrete).unwrap(), Some(true));
        }
    }

    #[test]
    fn resident_allows_cache_read_but_rejects_cache_write() {
        let mut options = SampleOptions {
            resident: Some("in.jsonl".into()),
            resident_out: Some("out.jsonl".into()),
            ..Default::default()
        };
        options.path_cache.read = Some("cache".into());
        assert!(options.validate().is_ok());
        options.path_cache.write = Some("new-cache".into());
        assert!(options.validate().is_err());
    }

    #[test]
    fn resident_fast_requires_resident_input() {
        assert!(SampleOptions { resident_fast: true, ..Default::default() }.validate().is_err());
        assert!(SampleOptions {
            resident_fast: true,
            resident: Some("in.jsonl".into()),
            resident_out: Some("out.jsonl".into()),
            ..Default::default()
        }
        .validate()
        .is_ok());
    }

    #[test]
    fn samples_f5_复用前态格式化字节与模型查询一致() {
        use isla_lib::bitvector::b129::B129;
        use isla_lib::ir::Symtab;
        use isla_lib::smt::{smtlib, Config, Context, Model, Solver};
        use isla_lib::source_loc::SourceLoc;
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B129>::new(&context);
        let mut symtab = Symtab::new();
        let flag = symtab.intern("zflag");
        let wide = symtab.intern("zwide");
        let wrapped = symtab.intern("zwrapped");
        let field = symtab.intern("zbits");
        let list = symtab.intern("zlist");
        let mut target = super::super::target::RV64::<B129>::default();
        target
            .pre_state_mut()
            .insert(flag, Val::Symbolic(solver.declare_const(smtlib::Ty::Bool, SourceLoc::unknown())));
        target.pre_state_mut().insert(wide, Val::Symbolic(solver.declare_bitvector(256, SourceLoc::unknown())));
        target.pre_state_mut().insert(
            wrapped,
            Val::Struct(std::collections::HashMap::from_iter([(
                field,
                Val::Symbolic(solver.declare_bitvector(64, SourceLoc::unknown())),
            )])),
        );
        // 非零高位与枚举覆盖格式化位序；符号 PMA 大小仍走模型接口。
        let Val::Symbolic(wide_symbol) = target.pre_state().get(&wide).unwrap() else {
            panic!("宽值必须符号化");
        };
        solver.assert(smtlib::Exp::Eq(
            Box::new(smtlib::Exp::Var(*wide_symbol)),
            Box::new(smtlib::Exp::Bits((0..256).map(|bit| bit % 7 == 0).collect())),
        ));
        let enum_name = symtab.intern("zF5Enum");
        let enum_member = symtab.intern("zF5Member");
        let enum_register = symtab.intern("zenum_reg");
        let mut shared = SharedState::empty(symtab);
        shared.type_info.enum_members.insert(enum_member, (0, 1, enum_name));
        shared.type_info.enums.insert(enum_name, vec![enum_member]);
        solver.add(smtlib::Def::DefineEnum(enum_name, 1));
        let enum_value =
            solver.declare_const(smtlib::Ty::Enum(isla_lib::smt::EnumId::from_name(enum_name)), SourceLoc::unknown());
        target.pre_state_mut().insert(enum_register, Val::Symbolic(enum_value));
        let pma_size = solver.declare_bitvector(64, SourceLoc::unknown());
        target.model_bindings.push(("pma_regions.test.size".into(), pma_size));

        let pre = target
            .pre_state()
            .iter()
            .map(|(name, value)| (isla_lib::zencode::decode(shared.symtab.to_str(*name)), value.clone()))
            .collect();
        let path = SamplePath {
            terminal: Default::default(),
            pre,
            post: BTreeMap::new(),
            result: Val::Unit,
            memory: Vec::new(),
            memory_guards: BTreeMap::new(),
        };
        assert_eq!(solver.check_sat(SourceLoc::unknown()), isla_lib::smt::SmtResult::Sat);
        let mut model = Model::new(&solver);
        let sample = path.materialize(&mut model, &shared, "merge", 0, Some(0)).unwrap();
        let expected = target.solve_pre_state(&mut model, &shared).unwrap();
        let actual = isa_state(&target, &sample, &mut model, &shared).unwrap();
        assert_eq!(serde_json::to_vec(&actual).unwrap(), serde_json::to_vec(&expected).unwrap());
        target.pre_state_mut().insert(list, Val::List(vec![Val::Unit]));
        let mut sample = sample;
        sample.pre_registers.insert("list".into(), serde_json::json!({"list":[{"unit":true}]}));
        assert!(target.solve_pre_state(&mut model, &shared).is_err());
        assert!(isa_state(&target, &sample, &mut model, &shared).is_err(), "样本也必须传播无法格式化的前态错误");
    }

    #[test]
    fn samples_predict_配置后端也不创建样本文件() {
        let root = std::env::temp_dir().join(format!("f12-no-samples-{}", std::process::id()));
        let config = MergeEnumerationConfig {
            enabled: true,
            mode: MergeEnumerationMode::Predict,
            outputs: vec![SampleOutputConfig { format: SampleOutputFormat::Binary, path: root.join("never.bin") }],
            ..Default::default()
        };
        let session = SampleSession::new(&SampleOptions::default(), Some(&config)).unwrap();
        assert!(session.writer.is_none());
        assert!(!root.exists());
    }

    #[test]
    fn samples_a1_单二进制无预算时仍使用流式文件() {
        let root = std::env::temp_dir().join(format!("samples-a1-stream-{}", std::process::id()));
        let path = root.join("samples.bin");
        let config = MergeEnumerationConfig {
            enabled: true,
            outputs: vec![SampleOutputConfig { format: SampleOutputFormat::Binary, path: path.clone() }],
            ..Default::default()
        };
        let options = SampleOptions::default();
        let session = SampleSession::new(&options, Some(&config)).unwrap();
        session.finish(&options, true);
        let summary: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path.with_extension("summary.json")).unwrap()).unwrap();
        assert_eq!(summary["max_output_bytes"], serde_json::Value::Null);
        assert_eq!(summary["truncated"], false);
        let bytes = std::fs::read(path).unwrap();
        assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 2);
        assert_eq!(&bytes[bytes.len() - 8..], &u64::MAX.to_le_bytes());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn samples_f9_报告不得覆盖后端文件() {
        let outputs = MergeEnumerationConfig {
            outputs: vec![SampleOutputConfig { format: SampleOutputFormat::Binary, path: "same.bin".into() }],
            ..Default::default()
        };
        let options = SampleOptions {
            check: Some("unused-input.jsonl".into()),
            limit: None,
            report: Some("same.bin".into()),
            judge: None,
            ..Default::default()
        };
        let error = SampleSession::new(&options, Some(&outputs)).err().unwrap();
        assert!(error.contains("检查报告不得覆盖样本输出"));
        let counting = MergeEnumerationConfig { enabled: true, mode: MergeEnumerationMode::Count, ..outputs };
        let session = SampleSession::new(&SampleOptions::default(), Some(&counting)).unwrap();
        assert!(session.writer.is_none(), "count 不得打开任何输出后端");
    }

    #[test]
    fn samples_judge_options_require_check_and_distinct_outputs() {
        assert!(SampleOptions { judge: Some("judged.jsonl".into()), ..Default::default() }.validate().is_err());
        for (judge, report, valid) in [
            ("input.jsonl", "report.json", false),
            ("report.json", "report.json", false),
            ("judged.jsonl", "report.json", true),
        ] {
            assert_eq!(
                SampleOptions {
                    check: Some("input.jsonl".into()),
                    report: Some(report.into()),
                    judge: Some(judge.into()),
                    ..Default::default()
                }
                .validate()
                .is_ok(),
                valid
            );
        }
        let outputs = MergeEnumerationConfig {
            outputs: vec![SampleOutputConfig { format: SampleOutputFormat::Binary, path: "same.bin".into() }],
            ..Default::default()
        };
        let options =
            SampleOptions { check: Some("unused.jsonl".into()), judge: Some("same.bin".into()), ..Default::default() };
        assert!(SampleSession::new(&options, Some(&outputs)).err().unwrap().contains("judge 输出不得覆盖样本输出"));
    }

    #[test]
    fn samples_options_validate_dependencies_and_limits() {
        assert!(SampleOptions::default().validate().is_ok());
        assert!(SampleOptions { limit: Some(10), ..Default::default() }.validate().is_err());
        assert!(SampleOptions {
            check: Some("samples.jsonl".into()),
            limit: Some(0),
            report: None,
            judge: None,
            ..Default::default()
        }
        .validate()
        .is_err());
        assert!(SampleOptions {
            check: Some("samples.jsonl".into()),
            limit: Some(10),
            report: Some("samples.jsonl".into()),
            judge: None,
            ..Default::default()
        }
        .validate()
        .is_err());
        assert!(SampleOptions {
            check: Some("samples.jsonl".into()),
            limit: Some(10),
            report: Some("report.json".into()),
            judge: None,
            ..Default::default()
        }
        .validate()
        .is_ok());
    }
    #[test]
    fn samples_f4_array_reads_keep_constraints_under_arm_guard() {
        use isla_lib::bitvector::b64::B64;
        use isla_lib::memory::Memory;
        use isla_lib::primop_util::smt_value;
        use isla_lib::smt::smtlib::{bits64, Exp, Ty};
        use isla_lib::smt::{Config, Context, ReadOpts, Solver};
        use isla_lib::source_loc::SourceLoc;
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let info = SourceLoc::unknown();
        let mut memory = Memory::new();
        memory.add_symbolic_region(0x1000..0x1010);
        super::super::memory_model::install_seq_memory(&mut memory, 64, &mut solver);
        let g = solver.declare_const(Ty::Bool, info);
        solver.start_transaction();
        let mut values = Vec::new();
        for (guard, byte) in [(Exp::Var(g), 7), (Exp::Not(Box::new(Exp::Var(g))), 9)] {
            solver.start_transaction_with_guard(Some(guard));
            let value = memory
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            solver.assert(Exp::Eq(Box::new(smt_value(&value, info).unwrap()), Box::new(bits64(byte, 8))));
            values.push(value);
            solver.commit_transaction();
        }
        solver.commit_transaction();
        // 同址两臂要求不同内容，只有各自 guard 生效；无条件提交会使整个路径 Unsat。
        for (direction, byte) in [(true, 7), (false, 9)] {
            let guard = Exp::Eq(Box::new(Exp::Var(g)), Box::new(Exp::Bool(direction)));
            assert!(solver.check_sat_with(&guard, info).is_sat().unwrap());
            let tx = solver.start_transaction_with_guard(Some(guard));
            let current = memory
                .read(Val::Unit, Val::Bits(B64::new(0x1000, 64)), Val::I128(1), &mut solver, false, ReadOpts::default())
                .unwrap();
            assert!(solver
                .check_sat_with(
                    &Exp::Neq(Box::new(smt_value(&current, info).unwrap()), Box::new(bits64(byte, 8))),
                    info
                )
                .is_unsat()
                .unwrap());
            solver.rollback_transaction(tx);
        }
        assert_ne!(values[0], values[1], "两次读取必须使用不同的新鲜符号");
    }
}

#[cfg(test)]
mod cache_fuzz_tests {
    use super::*;
    #[test]
    fn cache_fuzz_cached_solve_can_export_and_check() {
        let mut options = SampleOptions::default();
        options.path_cache.read = Some("cache".into());
        options.check = Some("samples.jsonl".into());
        assert!(options.validate().is_ok());
    }
}
