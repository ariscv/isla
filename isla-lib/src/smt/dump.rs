//! SMT timeout 诊断 dump 的构造与 SMT-LIB2 物化。

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
        let mut solver = Self::new_with_symbol_namer(ctx, Z3SymbolNamer::Smtlib2(names));
        solver.replay(num, trace);
        solver.next_var = next_var;
        solver
    }

    pub(super) fn checkpoint_snapshot(&self) -> Checkpoint<B> {
        let trace = Arc::new(Some(Trace {
            checkpoints: self.trace.checkpoints,
            head: self.trace.head.clone(),
            tail: self.trace.tail.clone(),
        }));
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
    fn checkpoint_dump_without_worker_uses_replayable_datatype_symbols() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let enum_id = solver.get_enum(Name::from_u32(2097), 5);
        let symbol = solver.declare_const(Ty::Enum(enum_id), SourceLoc::unknown());
        solver.add(Assert(Neq(Box::new(Var(symbol)), Box::new(Enum(EnumMember { enum_id, member: 4 })))));
        let dump = timeout_dump_from_checkpoint(checkpoint(&mut solver), SmtDumpRequest::CheckSat);

        let text = dump.materialize().unwrap();

        assert!(text.contains("(declare-datatypes ((isla_s2097 0))"), "unexpected datatype declaration:\n{}", text);
        assert!(text.contains("() isla_s2097)"), "datatype reference does not match declaration:\n{}", text);
    }

    #[test]
    fn checkpoint_dump_uses_shared_state_names_without_changing_local_symbols() {
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
