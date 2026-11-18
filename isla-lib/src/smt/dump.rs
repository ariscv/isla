//! SMT timeout 诊断 dump 的构造与 SMT-LIB2 文本生成。

use std::convert::TryInto;
use std::ffi::{CStr, CString};
use std::sync::Arc;

use libc::c_int;
use z3_sys::*;

use super::smtlib::Exp;
use super::{Checkpoint, Config, Context, Solver, Sym, Trace};
use crate::bitvector::BV;
use crate::ir::{Name, SharedState};
use crate::timeout::{SmtDumpNames, SmtDumpSource, TimeoutSmtDump};
use crate::zencode;

pub(super) enum Z3SymbolNamer {
    Integer,
    Smtlib2(SmtDumpNames),
}

impl Z3SymbolNamer {
    pub(super) fn symbol(&self, ctx: &Context, symbol: Sym) -> Z3_symbol {
        match self {
            Z3SymbolNamer::Integer => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, symbol.id as c_int) },
            Z3SymbolNamer::Smtlib2(names) => {
                let name = CString::new(names.symbol_name(symbol.id)).unwrap();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, name.as_ptr()) }
            }
        }
    }

    pub(super) fn enum_sort(&self, ctx: &Context, name: Name) -> Z3_symbol {
        match self {
            Z3SymbolNamer::Integer => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, name.as_u32() as c_int) },
            Z3SymbolNamer::Smtlib2(names) => {
                let name = CString::new(names.enum_sort_name(name.as_u32())).unwrap();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, name.as_ptr()) }
            }
        }
    }

    pub(super) fn enum_member(
        &self,
        ctx: &Context,
        enum_name: Name,
        member: usize,
        generated_symbol: Sym,
    ) -> Z3_symbol {
        match self {
            Z3SymbolNamer::Integer => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, generated_symbol.id as c_int) },
            Z3SymbolNamer::Smtlib2(names) => {
                let name =
                    CString::new(names.enum_member_name(enum_name.as_u32(), member, generated_symbol.id)).unwrap();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, name.as_ptr()) }
            }
        }
    }
}

impl Context {
    fn new_smtlib2_dump(cfg: Config) -> Self {
        let context = Context::new(cfg);
        unsafe { Z3_set_ast_print_mode(context.z3_ctx, AstPrintMode::SmtLib2Compliant) };
        context
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    fn from_checkpoint_for_smtlib2_dump(
        ctx: &'ctx Context,
        Checkpoint { num, next_var, trace }: Checkpoint<B>,
        names: SmtDumpNames,
    ) -> Self {
        let mut solver =
            Self::new_with_mode(ctx, Z3SymbolNamer::Smtlib2(names), None, super::on_demand::SolverMode::Incremental);
        solver.replay(num, trace);
        solver.next_var = next_var;
        solver
    }

    pub(super) fn checkpoint_snapshot(&self) -> Checkpoint<B> {
        // 诊断快照不能只复制已发布的迹：事务内查询还使用缓冲断言和活动臂条件。
        // 条件放在定义之后，允许旧臂作用域引用同一保存点内刚声明的符号。
        let mut head = self.trace.head.clone();
        head.extend(self.transaction_events.iter().cloned());
        head.extend(self.transaction_conditions.iter().cloned().map(|condition| {
            super::Event::Smt(super::Def::Assert(condition), super::DefAttrs::default(), super::SourceLoc::unknown())
        }));
        let trace = Arc::new(Some(Trace { checkpoints: self.trace.checkpoints, head, tail: self.trace.tail.clone() }));
        Checkpoint { num: self.trace.checkpoints + 1, next_var: self.next_var, trace }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::ir::{Name, SharedState, Symtab};
    use crate::smt::smtlib::{Def::*, Exp::*, Ty};
    use crate::smt::{checkpoint, EnumMember};
    use crate::source_loc::SourceLoc;

    #[test]
    fn slow_query_dump_assertion_indices_match_unconditional_check() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.assert(Var(x));
        for target in [None, Some(Bool(true))] {
            let (text, metadata) = slow_query_artifact(solver.checkpoint_snapshot(), target.as_ref());
            assert_eq!(text.matches("(assert").count(), metadata["assertions"].as_array().unwrap().len());
        }
    }

    #[test]
    fn slow_query_dump_threshold_limit_and_complete_formula() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.assert(Var(x));
        let state = SlowQueryDump::new(std::path::PathBuf::new(), std::time::Duration::from_secs(2), 2);
        assert_eq!(state.reserve(std::time::Duration::from_secs(1)), None);
        assert_eq!(state.reserve(std::time::Duration::from_secs(2)), Some(0));
        assert_eq!(state.reserve(std::time::Duration::from_secs(3)), Some(1));
        assert_eq!(state.reserve(std::time::Duration::from_secs(3)), None);
        let (text, metadata) = slow_query_artifact(solver.checkpoint_snapshot(), Some(&Not(Box::new(Var(x)))));
        assert_eq!(metadata["assertions"].as_array().unwrap().len(), 2);
        assert_eq!(metadata["assertions"][1]["role"], "query");
        assert!(metadata["expanded_ast_nodes"].as_u64().unwrap() >= 3);
        assert_eq!(text.matches("(assert").count(), 2);
        assert!(text.contains("(check-sat)"));
        assert!(text.contains("declare-fun"));
        let replay = Solver::<B64>::new(&ctx);
        let parsed = CString::new(text).unwrap();
        unsafe {
            Z3_solver_from_string(ctx.z3_ctx, replay.z3_solver, parsed.as_ptr());
            assert_eq!(Z3_solver_check(ctx.z3_ctx, replay.z3_solver), Z3_L_FALSE);
        }
        let tx = solver.start_transaction_with_guard(Some(Not(Box::new(Var(x)))));
        solver.assert(Var(x));
        let (text, metadata) = slow_query_artifact(solver.checkpoint_snapshot(), Some(&Bool(true)));
        assert_eq!(metadata["assertions"].as_array().unwrap().len(), 4);
        let replay = Solver::<B64>::new(&ctx);
        unsafe {
            Z3_solver_from_string(ctx.z3_ctx, replay.z3_solver, CString::new(text).unwrap().as_ptr());
            assert_eq!(Z3_solver_check(ctx.z3_ctx, replay.z3_solver), Z3_L_FALSE);
        }
        solver.rollback_transaction(tx);
        assert!(solver.check_sat(SourceLoc::unknown()).is_sat().unwrap());
    }

    #[test]
    fn checkpoint_dump_preserves_temporary_assumption_as_replayable_command() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let var = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        let checkpoint = checkpoint(&mut solver);
        let dump = timeout_dump_from_checkpoint(checkpoint, SmtDumpRequest::CheckSatWith(Var(var)));

        assert!(!dump.is_materialized());
        let text = dump.materialize().unwrap();
        assert!(text.contains("check-sat"), "unexpected SMT2 dump:\n{}", text);
        assert!(text.contains("declare-fun"), "unexpected SMT2 dump:\n{}", text);
        assert!(text.contains("assert"), "temporary assumption missing from SMT2 dump:\n{}", text);
    }

    #[test]
    fn query_replay_dump_keeps_buffered_assertions_and_active_guard() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let info = SourceLoc::unknown();
        let x = solver.declare_const(Ty::Bool, info);
        let tx = solver.start_transaction_with_guard(Some(Var(x)));
        solver.assert(Not(Box::new(Var(x))));
        let dump = timeout_dump_from_checkpoint(solver.checkpoint_snapshot(), SmtDumpRequest::CheckSatWith(Bool(true)));
        let text = dump.materialize().unwrap();
        let parsed = CString::new(text.as_bytes()).unwrap();
        let replay = Solver::<B64>::new(&ctx);
        unsafe {
            Z3_solver_from_string(ctx.z3_ctx, replay.z3_solver, parsed.as_ptr());
            assert_eq!(
                Z3_solver_check(ctx.z3_ctx, replay.z3_solver),
                Z3_L_FALSE,
                "回放必须同时保留互相矛盾的活动守卫和缓冲断言"
            );
        }
        solver.rollback_transaction(tx);
        assert!(solver.check_sat(info).is_sat().unwrap());
    }

    #[test]
    fn checkpoint_dump_default_names_separate_enum_members_from_symbols() {
        let names = SmtDumpNames::default();
        for i in 0..5 {
            assert_ne!(names.symbol_name(i), names.enum_member_name(2097, i as usize, i));
            assert_ne!(names.symbol_name(i), names.enum_sort_name(i));
        }
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let x = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
        let enumeration = solver.get_enum(Name::from_u32(2097), 5);
        let e = solver.declare_const(Ty::Enum(enumeration), SourceLoc::unknown());
        solver.assert(Eq(Box::new(Var(e)), Box::new(Enum(EnumMember { enum_id: enumeration, member: 0 }))));
        solver.assert(Eq(Box::new(Var(x)), Box::new(Bits64(B64::new(7, 64)))));
        let dump = timeout_dump_from_checkpoint(solver.checkpoint_snapshot(), SmtDumpRequest::CheckSat);
        let text = dump.materialize().unwrap();
        let parsed = CString::new(text.as_bytes()).unwrap();
        let replay = Solver::<B64>::new(&ctx);
        unsafe {
            Z3_solver_from_string(ctx.z3_ctx, replay.z3_solver, parsed.as_ptr());
            assert_eq!(Z3_solver_check(ctx.z3_ctx, replay.z3_solver), Z3_L_TRUE);
        }
    }

    #[test]
    fn checkpoint_dump_without_worker_uses_replayable_datatype_symbols() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let enum_id = solver.get_enum(Name::from_u32(2097), 5);
        let symbol = solver.declare_const(Ty::Enum(enum_id), SourceLoc::unknown());
        solver.add(Assert(Neq(Box::new(Var(symbol)), Box::new(Enum(EnumMember { enum_id, member: 4 })))));
        let dump = timeout_dump_from_checkpoint(checkpoint(&mut solver), SmtDumpRequest::CheckSat);

        let text = dump.materialize().unwrap();

        assert!(
            text.contains("(declare-datatypes ((isla_enum_n2097 0))"),
            "unexpected datatype declaration:\n{}",
            text
        );
        assert!(text.contains("() isla_enum_n2097)"), "datatype reference does not match declaration:\n{}", text);
    }

    #[test]
    fn checkpoint_dump_uses_shared_state_names_without_changing_local_symbols() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let local_text = crate::zencode::encode("local_value");
        let enum_text = crate::zencode::encode("colour");
        let red_text = crate::zencode::encode("red");
        let blue_text = crate::zencode::encode("blue");
        let mut symtab = Symtab::new();
        let local = symtab.intern(&local_text);
        let enum_name = symtab.intern(&enum_text);
        let red = symtab.intern(&red_text);
        let blue = symtab.intern(&blue_text);
        let mut shared_state: SharedState<B64> = SharedState::empty(symtab);
        shared_state.type_info.enums.insert(enum_name, vec![red, blue]);

        let symbol = Sym::from_u32(41);
        let mut names = SmtDumpNames::from_shared_state(&shared_state);
        names.bind_symbol_to_ir_name(symbol.id, local.as_u32());

        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let enum_id = solver.get_enum(enum_name, 2);
        solver.add(DeclareConst(symbol, Ty::Enum(enum_id)));
        solver.add(Assert(Neq(Box::new(Var(symbol)), Box::new(Enum(enum_id.first_member())))));
        let dump = timeout_dump_from_checkpoint(checkpoint(&mut solver), SmtDumpRequest::CheckSat);
        dump.configure_names(names);

        let text = dump.materialize().unwrap();

        for name in ["local_value", "colour", "red", "blue"] {
            assert!(text.contains(name), "SMT2 dump lost IR name {name}:\n{text}");
        }
    }
}

impl SmtDumpNames {
    pub(crate) fn from_shared_state<B: BV>(shared_state: &SharedState<B>) -> Self {
        let mut names = Self::default();
        for name in shared_state.symtab.all_names() {
            names.insert_ir_name(name.as_u32(), zencode::decode(shared_state.symtab.to_str(name)));
        }
        for (enum_id, members) in &shared_state.type_info.enums {
            names.insert_enum_members(
                enum_id.as_u32(),
                members.iter().map(|member| zencode::decode(shared_state.symtab.to_str(*member))).collect(),
            );
        }
        names
    }
}

#[derive(Clone)]
pub(super) enum SmtDumpRequest {
    CheckSat,
    CheckSatWith(Exp<Sym>),
    GetValues { expressions: Vec<Exp<Sym>> },
}

struct TypedCheckpointDumpSource<B: BV> {
    checkpoint: Checkpoint<B>,
    request: SmtDumpRequest,
}

impl<B: BV> SmtDumpSource for TypedCheckpointDumpSource<B> {
    fn materialize(&self) -> Result<String, String> {
        self.materialize_with_names(&SmtDumpNames::default())
    }

    fn materialize_with_names(&self, names: &SmtDumpNames) -> Result<String, String> {
        let ctx = Context::new_smtlib2_dump(Config::new());
        let mut solver = Solver::from_checkpoint_for_smtlib2_dump(&ctx, self.checkpoint.clone(), names.clone());
        Ok(solver.smt2_for_request(&self.request))
    }
}

pub(super) fn timeout_dump_from_checkpoint<B: BV>(
    checkpoint: Checkpoint<B>,
    request: SmtDumpRequest,
) -> Arc<TimeoutSmtDump> {
    Arc::new(TimeoutSmtDump::new(Arc::new(TypedCheckpointDumpSource { checkpoint, request })))
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    fn benchmark_to_smt2(&mut self, assumption: Option<&Exp<Sym>>) -> String {
        let assumption_ast = assumption.map(|assumption| self.translate_exp(assumption));
        unsafe {
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, self.z3_solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let assertion_count = Z3_ast_vector_size(self.ctx.z3_ctx, assertions);
            let assertion_asts: Vec<Z3_ast> =
                (0..assertion_count).map(|index| Z3_ast_vector_get(self.ctx.z3_ctx, assertions, index)).collect();
            let formula = match assertion_asts.len() {
                0 => Z3_mk_true(self.ctx.z3_ctx),
                1 => assertion_asts[0],
                _ => Z3_mk_and(self.ctx.z3_ctx, assertion_count, assertion_asts.as_ptr()),
            };

            let name = CString::new("isla-timeout").unwrap();
            let empty = CString::new("").unwrap();
            let status = CString::new("unknown").unwrap();
            let assumptions: Vec<Z3_ast> = assumption_ast.iter().map(|ast| ast.z3_ast).collect();
            let assumption_count = assumptions.len().try_into().expect("too many SMT dump assumptions");
            let output = Z3_benchmark_to_smtlib_string(
                self.ctx.z3_ctx,
                name.as_ptr(),
                empty.as_ptr(),
                status.as_ptr(),
                empty.as_ptr(),
                assumption_count,
                assumptions.as_ptr(),
                formula,
            );
            assert!(!output.is_null(), "Z3_benchmark_to_smtlib_string returned null");
            let result = CStr::from_ptr(output).to_string_lossy().into_owned();
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            result
        }
    }

    fn smt2_for_request(&mut self, request: &SmtDumpRequest) -> String {
        let assumption = match request {
            SmtDumpRequest::CheckSat => None,
            SmtDumpRequest::CheckSatWith(assumption) => Some(assumption),
            SmtDumpRequest::GetValues { .. } => None,
        };
        let mut smt2 = self.benchmark_to_smt2(assumption);
        if !smt2.ends_with('\n') {
            smt2.push('\n');
        }

        match request {
            SmtDumpRequest::CheckSat | SmtDumpRequest::CheckSatWith(_) => (),
            SmtDumpRequest::GetValues { expressions, .. } => {
                smt2.push_str("(get-value (");
                for (index, expression) in expressions.iter().enumerate() {
                    if index > 0 {
                        smt2.push(' ');
                    }
                    smt2.push_str(&self.exp_to_str(expression));
                }
                smt2.push_str("))\n");
            }
        }
        smt2
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(super) fn diagnostic_query_dump(&self, exp: &Exp<Sym>) -> Option<serde_json::Value> {
        let mut point = crate::executor::stats::region_progress::query_dump_point()?;
        let directory =
            crate::config::RegionOptions::current().query_dump_dir.as_ref().expect("指定导出位置时必须指定数据目录");
        std::fs::create_dir_all(&directory).expect("创建查询导出目录失败");
        let filename = format!(
            "round-{}-{}-query-{}.smt2",
            point["round"],
            point["site"].as_str().unwrap().replace('@', "-"),
            point["query_ordinal"]
        );
        let path = std::path::Path::new(&directory).join(filename);
        let dump = timeout_dump_from_checkpoint(self.checkpoint_snapshot(), SmtDumpRequest::CheckSatWith(exp.clone()));
        let text = dump.materialize().expect("生成完整查询回放失败");
        std::fs::write(&path, text.as_bytes()).expect("写出查询回放失败");
        point["path"] = serde_json::json!(path);
        Some(point)
    }
}

/// 默认关闭；只在已经选中的导出点做一次同Context对照，不参与执行决策。
pub(super) fn wants_same_context_pair(point: &serde_json::Value) -> bool {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let sites = &crate::config::RegionOptions::current().same_context_sites;
    let Some(index) = sites.iter().position(|s| Some(s.as_str()) == point["site"].as_str()) else {
        return false;
    };
    assert!(sites.len() <= 2, "有界配对最多选择两个位置");
    let round = point["round"].as_u64().expect("导出点必须包含轮号") as usize;
    assert!(round <= 8, "有界配对轮号超限");
    static DONE: AtomicUsize = AtomicUsize::new(0);
    let bit = 1usize << (round * 2 + index);
    DONE.fetch_or(bit, Ordering::Relaxed) & bit == 0
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(super) fn diagnostic_solver_stats(&self, solver: Z3_solver) -> serde_json::Value {
        unsafe {
            let stats = Z3_solver_get_statistics(self.ctx.z3_ctx, solver);
            Z3_stats_inc_ref(self.ctx.z3_ctx, stats);
            let text = CStr::from_ptr(Z3_stats_to_string(self.ctx.z3_ctx, stats)).to_string_lossy().into_owned();
            Z3_stats_dec_ref(self.ctx.z3_ctx, stats);
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, solver);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let count = Z3_ast_vector_size(self.ctx.z3_ctx, assertions);
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            serde_json::json!({"text":text,"assertions":count,"scopes":Z3_solver_get_num_scopes(self.ctx.z3_ctx,solver)})
        }
    }

    /// 用原查询solver的全部断言与真实assumptions装配新solver；不重新翻译/命名/建Context。
    pub(super) fn diagnostic_fresh_query(
        &self,
        original: Z3_solver,
        assumptions: &[Z3_ast],
        timeout_ms: u32,
    ) -> serde_json::Value {
        let setup = std::time::Instant::now();
        let config = super::SMT_CONFIG.get().expect("诊断前必须初始化SMT");
        unsafe {
            let fresh = super::new_z3_solver(
                self.ctx.z3_ctx,
                config.tactic.as_c_str(),
                self.seed.map(|seed| (config.seed_param, seed)),
            );
            let params = Z3_mk_params(self.ctx.z3_ctx);
            Z3_params_inc_ref(self.ctx.z3_ctx, params);
            Z3_params_set_uint(
                self.ctx.z3_ctx,
                params,
                Z3_mk_string_symbol(self.ctx.z3_ctx, b"timeout\0".as_ptr().cast()),
                timeout_ms,
            );
            Z3_solver_set_params(self.ctx.z3_ctx, fresh, params);
            Z3_params_dec_ref(self.ctx.z3_ctx, params);
            let assertions = Z3_solver_get_assertions(self.ctx.z3_ctx, original);
            Z3_ast_vector_inc_ref(self.ctx.z3_ctx, assertions);
            let count = Z3_ast_vector_size(self.ctx.z3_ctx, assertions);
            for i in 0..count {
                Z3_solver_assert(self.ctx.z3_ctx, fresh, Z3_ast_vector_get(self.ctx.z3_ctx, assertions, i));
            }
            for assumption in assumptions {
                Z3_solver_assert(self.ctx.z3_ctx, fresh, *assumption);
            }
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx, assertions);
            let before = self.diagnostic_solver_stats(fresh);
            let setup_ms = setup.elapsed().as_secs_f64() * 1000.0;
            let started = std::time::Instant::now();
            // 诊断单独有原生timeout；不用执行侧包装器，避免把诊断计入路径查询/SMT计数。
            let result = Z3_solver_check(self.ctx.z3_ctx, fresh);
            let wall_ms = started.elapsed().as_secs_f64() * 1000.0;
            let after = self.diagnostic_solver_stats(fresh);
            let reason = if result == Z3_L_UNDEF {
                CStr::from_ptr(Z3_solver_get_reason_unknown(self.ctx.z3_ctx, fresh)).to_string_lossy().into_owned()
            } else {
                String::new()
            };
            Z3_solver_dec_ref(self.ctx.z3_ctx, fresh);
            serde_json::json!({"result":if result==Z3_L_TRUE {"sat"} else if result==Z3_L_FALSE {"unsat"} else {"unknown"},"check_milliseconds":wall_ms,"setup_milliseconds":setup_ms,"statistics_before":before,"statistics_after":after,"reason_unknown":reason,"timeout_ms":timeout_ms,"seed":self.seed,"assertions":count as usize + assumptions.len(),"scopes":0,"same_context":true,"same_ast":true})
        }
    }
}

/// 可重放的反例诊断：额外断言先作为自由别名定义，不施加真假限制，离线再逐条加回。
pub(super) fn write_obligation_diagnostic<B: BV>(
    point: Checkpoint<B>,
    goal: &Exp<Sym>,
    extras: &[(Exp<Sym>, crate::source_loc::SourceLoc)],
    values: &[(Sym, crate::source_loc::SourceLoc)],
    directory: &std::path::Path,
    ordinal: usize,
    replay_seconds: f64,
    check_seconds: f64,
) {
    use super::{
        smtlib::{Def, Ty},
        SourceLoc,
    };
    let ctx = Context::new_smtlib2_dump(Config::new());
    let mut solver = Solver::from_checkpoint_for_smtlib2_dump(&ctx, point, SmtDumpNames::default());
    let mut metadata = Vec::new();
    for (exp, loc) in extras {
        let sym = solver.declare_const(Ty::Bool, SourceLoc::unknown());
        solver.assert(Exp::Eq(Box::new(Exp::Var(sym)), Box::new(exp.clone())));
        metadata.push(serde_json::json!({"symbol":solver.exp_to_str(&Exp::Var(sym)),"expression":solver.exp_to_str(exp),"source_loc":loc}));
    }
    let mut fields = Vec::new();
    for (sym, loc) in values {
        let alias = solver.declare_const(Ty::BitVec(2), SourceLoc::unknown());
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(alias)), Box::new(Exp::Var(*sym)))));
        fields.push(serde_json::json!({"symbol":solver.exp_to_str(&Exp::Var(alias)),"expression":solver.exp_to_str(&Exp::Var(*sym)),"source_loc":loc}));
    }
    let smt = solver.benchmark_to_smt2(Some(goal));
    std::fs::create_dir_all(directory).unwrap();
    let prefix = directory.join(format!("obligation-{ordinal}"));
    std::fs::write(prefix.with_extension("smt2"), smt).unwrap();
    std::fs::write(prefix.with_extension("json"),serde_json::to_vec_pretty(&serde_json::json!({"excluded_assertions":metadata,"two_bit_values":fields,"replay_seconds":replay_seconds,"check_seconds":check_seconds})).unwrap()).unwrap();
}

/// 返回后的慢查询取样；只用显式 CLI 配置，不改变执行判断。
struct SlowQueryDump {
    directory: std::path::PathBuf,
    threshold: std::time::Duration,
    limit: usize,
    next: std::sync::atomic::AtomicUsize,
}

impl SlowQueryDump {
    fn new(directory: std::path::PathBuf, threshold: std::time::Duration, limit: usize) -> Self {
        assert!(limit > 0 && !threshold.is_zero(), "慢查询导出阈值和上限必须大于零");
        Self { directory, threshold, limit, next: std::sync::atomic::AtomicUsize::new(0) }
    }

    fn reserve(&self, elapsed: std::time::Duration) -> Option<usize> {
        if elapsed < self.threshold {
            return None;
        }
        self.next
            .fetch_update(std::sync::atomic::Ordering::Relaxed, std::sync::atomic::Ordering::Relaxed, |next| {
                (next < self.limit).then_some(next + 1)
            })
            .ok()
    }
}

static SLOW_QUERY_DUMP: std::sync::OnceLock<SlowQueryDump> = std::sync::OnceLock::new();

pub fn configure_slow_query_dump(directory: std::path::PathBuf, threshold: std::time::Duration, limit: usize) {
    std::fs::create_dir_all(&directory).expect("创建慢查询目录失败");
    assert!(SLOW_QUERY_DUMP.set(SlowQueryDump::new(directory, threshold, limit)).is_ok(), "慢查询诊断重复初始化");
}

/// 展开 DefineConst 后的 DAG/树大小；树节点数饱和到 u64::MAX 并明确标记。
fn ast_size(ctx: Z3_context, roots: &[Z3_ast]) -> serde_json::Value {
    use std::collections::HashMap;
    let mut sizes: HashMap<Z3_ast, u64> = HashMap::new();
    let mut saturated = false;
    let mut stack: Vec<_> = roots.iter().map(|root| (*root, false)).collect();
    while let Some((node, visited)) = stack.pop() {
        if sizes.contains_key(&node) {
            continue;
        }
        let children: Vec<_> = unsafe {
            match Z3_get_ast_kind(ctx, node) {
                AstKind::App => {
                    let app = Z3_to_app(ctx, node);
                    (0..Z3_get_app_num_args(ctx, app)).map(|i| Z3_get_app_arg(ctx, app, i)).collect()
                }
                AstKind::Quantifier => vec![Z3_get_quantifier_body(ctx, node)],
                _ => vec![],
            }
        };
        if !visited {
            stack.push((node, true));
            stack.extend(children.iter().rev().map(|child| (*child, false)));
        } else {
            let size = children.iter().fold(1u64, |n, child| {
                let (sum, overflow) = n.overflowing_add(sizes[child]);
                saturated |= overflow;
                if overflow {
                    u64::MAX
                } else {
                    sum
                }
            });
            sizes.insert(node, size);
        }
    }
    let expanded = roots.iter().fold(0u64, |n, root| {
        let (sum, overflow) = n.overflowing_add(sizes[root]);
        saturated |= overflow;
        if overflow {
            u64::MAX
        } else {
            sum
        }
    });
    serde_json::json!({"dag_nodes":sizes.len(),"expanded_ast_nodes":expanded,"expanded_ast_saturated":saturated})
}

/// 完整快照复用已有命名和重放。逐条保留断言以支持离线分量分析及来源检查。
fn slow_query_artifact<B: BV>(checkpoint: Checkpoint<B>, exp: Option<&Exp<Sym>>) -> (String, serde_json::Value) {
    let ctx = Context::new_smtlib2_dump(Config::new());
    let mut solver = Solver::from_checkpoint_for_smtlib2_dump(&ctx, checkpoint, SmtDumpNames::default());
    let mut preceding = super::SourceLoc::unknown();
    let locations: Vec<_> = solver
        .trace
        .to_vec()
        .into_iter()
        .rev()
        .filter_map(|event| {
            if let super::Event::Smt(def, _, location) = event {
                let prior = preceding;
                if !location.is_unknown() {
                    preceding = *location;
                }
                if let super::Def::Assert(_) = def {
                    return Some((*location, prior));
                }
            }
            None
        })
        .collect();
    let mut definitions = Vec::new();
    let mut declarations = Vec::new();
    let mut reads = Vec::new();
    let mut assertion_dependencies = Vec::new();
    for event in solver.trace.to_vec().into_iter().rev() {
        match event {
            super::Event::Smt(super::Def::DefineConst(sym, value), _, source) => definitions.push(
                serde_json::json!({"symbol":sym.id,"source":source,"dependencies":value.variables().iter().map(|v|v.id).collect::<Vec<_>>()})),
            super::Event::Smt(super::Def::DeclareConst(sym, ty), _, source) => declarations.push(
                serde_json::json!({"symbol":sym.id,"source":source,"type":format!("{ty:?}")})),
            super::Event::Smt(super::Def::Assert(value), _, _) => assertion_dependencies.push(
                serde_json::json!(value.variables().iter().map(|v|v.id).collect::<Vec<_>>())),
            super::Event::ReadReg(..) | super::Event::ReadMem { .. } => reads.push(format!("{event:?}")),
            _ => (),
        }
    }
    let target = exp.map(|exp| solver.translate_exp(exp));
    unsafe {
        let vector = Z3_solver_get_assertions(ctx.z3_ctx, solver.z3_solver);
        Z3_ast_vector_inc_ref(ctx.z3_ctx, vector);
        let count = Z3_ast_vector_size(ctx.z3_ctx, vector);
        assert_eq!(locations.len(), count as usize, "快照断言来源数不一致");
        let assertions: Vec<_> = (0..count).map(|i| Z3_ast_vector_get(ctx.z3_ctx, vector, i)).collect();
        let mut roots = assertions.clone();
        roots.extend(target.iter().map(|ast| ast.z3_ast));
        let mut metadata = ast_size(ctx.z3_ctx, &roots);
        metadata["definitions"] = serde_json::json!(definitions);
        metadata["declarations"] = serde_json::json!(declarations);
        metadata["read_events"] = serde_json::json!(reads);
        metadata["assertion_dependencies"] = serde_json::json!(assertion_dependencies);
        metadata["query_dependencies"] =
            serde_json::json!(exp.map(|value| value.variables().iter().map(|v| v.id).collect::<Vec<_>>()));

        let mut sources: Vec<_> = locations
            .iter()
            .enumerate()
            .map(|(index, (location, preceding))| serde_json::json!({"index":index,"role":"prefix","source":location,"preceding_source":preceding}))
            .collect();
        if target.is_some() {
            sources.push(serde_json::json!({"index":sources.len(),"role":"query"}));
        }
        metadata["assertions"] = serde_json::json!(sources);
        let name = CString::new("isla-slow-query").unwrap();
        let empty = CString::new("").unwrap();
        let status = CString::new("unknown").unwrap();
        metadata["query_kind"] = serde_json::json!(if target.is_some() { "check_sat_with" } else { "check_sat" });
        let formula = Z3_mk_true(ctx.z3_ctx);
        let text = CStr::from_ptr(Z3_benchmark_to_smtlib_string(
            ctx.z3_ctx,
            name.as_ptr(),
            empty.as_ptr(),
            status.as_ptr(),
            empty.as_ptr(),
            roots.len().try_into().expect("导出断言数超限"),
            roots.as_ptr(),
            formula,
        ))
        .to_string_lossy()
        .into_owned();
        Z3_ast_vector_dec_ref(ctx.z3_ctx, vector);
        (text, metadata)
    }
}

pub(super) struct SlowQueryToken {
    started: std::time::Instant,
    before: serde_json::Value,
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    pub(super) fn slow_query_begin(&self, solver: Z3_solver) -> Option<SlowQueryToken> {
        let config = SLOW_QUERY_DUMP.get()?;
        if config.next.load(std::sync::atomic::Ordering::Relaxed) >= config.limit {
            return None;
        }
        let before = self.diagnostic_solver_stats(solver);
        Some(SlowQueryToken { started: std::time::Instant::now(), before })
    }

    pub(super) fn slow_query_finish(
        &self,
        token: Option<SlowQueryToken>,
        solver: Z3_solver,
        exp: Option<&Exp<Sym>>,
        info: super::SourceLoc,
        result: Z3_lbool,
    ) {
        let Some(token) = token else {
            return;
        };
        let elapsed = token.started.elapsed();
        let config = SLOW_QUERY_DUMP.get().unwrap();
        let Some(index) = config.reserve(elapsed) else {
            return;
        };
        let after = self.diagnostic_solver_stats(solver);
        let dump_started = std::time::Instant::now();
        let (text, mut metadata) = slow_query_artifact(self.checkpoint_snapshot(), exp);
        metadata["kind"] = serde_json::json!("slow_query_dump");
        metadata["source"] = serde_json::json!(info);
        metadata["check_seconds"] = serde_json::json!(elapsed.as_secs_f64());
        metadata["result"] = serde_json::json!(if result == Z3_L_TRUE {
            "sat"
        } else if result == Z3_L_FALSE {
            "unsat"
        } else {
            "unknown"
        });
        metadata["solver"] = serde_json::json!(format!("{:p}", solver));
        metadata["context"] = serde_json::json!(format!("{:p}", self.ctx.z3_ctx));
        metadata["thread"] = serde_json::json!(format!("{:?}", std::thread::current().id()));
        metadata["uses_main_solver"] = serde_json::json!(solver == self.z3_solver);
        metadata["statistics_before"] = token.before;
        metadata["statistics_after"] = after;
        metadata["export_seconds"] = serde_json::json!(dump_started.elapsed().as_secs_f64());
        let stem = config.directory.join(format!("query-{index:03}"));
        std::fs::write(stem.with_extension("smt2"), text).expect("写出慢查询SMT失败");
        std::fs::write(stem.with_extension("json"), serde_json::to_vec_pretty(&metadata).unwrap())
            .expect("写出慢查询统计失败");
        eprintln!("[SLOW_QUERY_DUMP] index={index} check_seconds={} path={}", elapsed.as_secs_f64(), stem.display());
    }
}
