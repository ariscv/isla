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
        let mut solver = Self::new_with_symbol_namer(ctx, Z3SymbolNamer::Smtlib2(names), None);
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
        let directory = std::env::var_os("ISLA_QUERY_DUMP_DIR").expect("指定导出位置时必须指定数据目录");
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
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        OnceLock,
    };
    static SITES: OnceLock<Option<Vec<String>>> = OnceLock::new();
    let sites = SITES.get_or_init(|| {
        std::env::var("ISLA_SAME_CONTEXT_SITES").ok().map(|s| s.split(',').map(str::to_owned).collect())
    });
    let Some(sites) = sites.as_ref() else {
        return false;
    };
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
