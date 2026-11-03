//! 全部静态条件分支清单和各路径实际经过的条件分支。
use super::{TraceHandler, TracePerPath};
use crate::bitvector::BV;
use crate::executor::Backtrace;
use crate::ir::{Instr, Name, SharedState, Symtab};
use crate::smt::{smtlib, Sym};
use crate::source_loc::SourceLoc;

#[derive(Clone)]
pub(super) struct BranchEdge {
    pub(super) function_name: Name,
    pub(super) backtrace: Backtrace,
    pub(super) pc: u64,
    pub(super) successor_pc: u64,
    pub(super) taken: bool,
    pub(super) source_loc: SourceLoc,
    pub(super) condition: String,
}

impl TracePerPath {
    pub fn push_branch_condition(&mut self, condition: smtlib::Exp<Sym>) {
        self.branch_conditions.push(condition);
    }
    pub fn record_jump<B: BV>(
        &mut self,
        function_name: Name,
        backtrace: Backtrace,
        pc: u64,
        successor_pc: u64,
        taken: bool,
        instruction: &Instr<Name, B>,
    ) {
        let Instr::Jump(condition, target, source_loc) = instruction else {
            panic!("btrace: 当前指令不是条件跳转");
        };
        assert_eq!(successor_pc, if taken { *target as u64 } else { pc + 1 }, "btrace: 实际后继与跳转方向不符");
        self.branch_edges.push(BranchEdge {
            function_name,
            backtrace,
            pc,
            successor_pc,
            taken,
            source_loc: *source_loc,
            condition: format!("{:?}", condition),
        });
    }
    #[cfg(test)]
    pub fn record_branch_edge(
        &mut self,
        function_name: Name,
        backtrace: Backtrace,
        pc: u64,
        successor_pc: u64,
        taken: bool,
    ) {
        self.branch_edges.push(BranchEdge {
            function_name,
            backtrace,
            pc,
            successor_pc,
            taken,
            source_loc: SourceLoc::unknown(),
            condition: "true".into(),
        });
    }
    #[cfg(test)]
    pub(crate) fn branch_edges_for_test(&self) -> Vec<(Name, u64, u64, bool)> {
        self.branch_edges.iter().map(|edge| (edge.function_name, edge.pc, edge.successor_pc, edge.taken)).collect()
    }
    pub(super) fn render_title(&self, title: &str, symtab: &Symtab) -> String {
        if self.branch_conditions.is_empty() {
            format!("<{}> path({}):", title, title)
        } else {
            let branches = self
                .branch_conditions
                .iter()
                .map(|condition| condition.to_trace_string(symtab))
                .collect::<Vec<_>>()
                .join("_");
            format!("<{}> path({}_branch_{}):", title, title, branches)
        }
    }
    pub(super) fn render_branches(&self, handler: &TraceHandler, symtab: &Symtab, lines: &mut Vec<String>) {
        if handler.btrace_enabled() && !self.branch_edges.is_empty() {
            lines.push(String::new());
            lines.push("---- branch edges ----".to_string());
            for edge in self.branch_edges.iter() {
                let source = edge.source_loc.location_string(symtab.files());
                let context = edge
                    .backtrace
                    .iter()
                    .map(|(function, pc)| format!("{}:{}", symtab.to_str(*function), pc))
                    .collect::<Vec<_>>()
                    .join(" > ");
                lines.push(format!(
                    "branch_edge function={} pc={} successor={} taken={} source={} context=[{}] condition={}",
                    symtab.to_str(edge.function_name),
                    edge.pc,
                    edge.successor_pc,
                    edge.taken,
                    source,
                    context,
                    edge.condition
                ));
            }
        }
    }
}

impl TraceHandler {
    /// btrace 的静态分支清单包含未执行的分支；只输出，不保留查询表。
    pub fn write_branch_sites<B: BV>(&self, shared_state: &SharedState<'_, B>) {
        if !self.btrace_enabled() || self.writer.output_path().is_none() {
            return;
        }
        let mut sites = Vec::new();
        for (function, (_, _, body)) in &shared_state.functions {
            for (pc, instruction) in body.iter().enumerate() {
                if let Instr::Jump(_, target, source) = instruction {
                    sites.push(
                        serde_json::json!({
                            "function": shared_state.symtab.to_str(*function),
                            "pc": pc,
                            "instruction": format!("{:?}", instruction),
                            "source_loc": source.location_string(shared_state.symtab.files()),
                            "target": target,
                            "fallthrough": pc + 1,
                        })
                        .to_string(),
                    );
                }
            }
        }
        sites.sort();
        let mut lines = vec!["---- branch sites ----".to_string()];
        lines.extend(sites);
        lines.push("---- end branch sites ----".to_string());
        self.writer.submit_text(lines.join("\n"));
    }
}

impl smtlib::Exp<Sym> {
    fn to_trace_string(&self, symtab: &Symtab) -> String {
        use smtlib::Exp::*;

        let sym_to_string = |sym: Sym| {
            let sym_id = sym.to_string();
            let Some(id) = sym_id.parse::<u32>().ok() else {
                return format!("v{}", sym);
            };
            let name = Name::from_u32(id);
            let name_str = symtab.to_str(name);
            if name_str == "zUNKNOWN" {
                format!("v{}", sym)
            } else {
                name_str.to_string()
            }
        };

        match self {
            Var(sym) => sym_to_string(*sym),
            Bits(bits) => {
                let bits = bits.iter().rev().map(|bit| if *bit { '1' } else { '0' }).collect::<String>();
                format!("#b{}", bits)
            }
            Bits64(bits) => bits.to_string(),
            Enum(member) => format!("{:?}", member),
            Bool(value) => value.to_string(),
            Eq(lhs, rhs) => format!("({} == {})", lhs.to_trace_string(symtab), rhs.to_trace_string(symtab)),
            Neq(lhs, rhs) => format!("({} != {})", lhs.to_trace_string(symtab), rhs.to_trace_string(symtab)),
            And(lhs, rhs) => format!("({} && {})", lhs.to_trace_string(symtab), rhs.to_trace_string(symtab)),
            Or(lhs, rhs) => format!("({} || {})", lhs.to_trace_string(symtab), rhs.to_trace_string(symtab)),
            Not(value) => format!("!{}", value.to_trace_string(symtab)),
            Bvnot(value) => format!("bvnot({})", value.to_trace_string(symtab)),
            Bvneg(value) => format!("bvneg({})", value.to_trace_string(symtab)),
            Extract(hi, lo, value) => format!("extract({}, {}, {})", hi, lo, value.to_trace_string(symtab)),
            ZeroExtend(width, value) => format!("zero_extend({}, {})", width, value.to_trace_string(symtab)),
            SignExtend(width, value) => format!("sign_extend({}, {})", width, value.to_trace_string(symtab)),
            Ite(cond, then_value, else_value) => format!(
                "ite({}, {}, {})",
                cond.to_trace_string(symtab),
                then_value.to_trace_string(symtab),
                else_value.to_trace_string(symtab)
            ),
            App(sym, args) => format!(
                "{}({})",
                sym_to_string(*sym),
                args.iter().map(|arg| arg.to_trace_string(symtab)).collect::<Vec<_>>().join(", ")
            ),
            Distinct(values) => format!(
                "distinct({})",
                values.iter().map(|value| value.to_trace_string(symtab)).collect::<Vec<_>>().join(", ")
            ),
            FPConstant(value, ebits, sbits) => format!("fp_constant({:?}, {}, {})", value, ebits, sbits),
            FPRoundingMode(value) => format!("{:?}", value),
            FPUnary(op, value) => format!("{:?}({})", op, value.to_trace_string(symtab)),
            FPRoundingUnary(op, rm, value) => {
                format!("{:?}({}, {})", op, rm.to_trace_string(symtab), value.to_trace_string(symtab))
            }
            FPBinary(op, lhs, rhs) => {
                format!("{:?}({}, {})", op, lhs.to_trace_string(symtab), rhs.to_trace_string(symtab))
            }
            FPRoundingBinary(op, rm, lhs, rhs) => format!(
                "{:?}({}, {}, {})",
                op,
                rm.to_trace_string(symtab),
                lhs.to_trace_string(symtab),
                rhs.to_trace_string(symtab)
            ),
            FPfma(rm, x, y, z) => format!(
                "fpfma({}, {}, {}, {})",
                rm.to_trace_string(symtab),
                x.to_trace_string(symtab),
                y.to_trace_string(symtab),
                z.to_trace_string(symtab)
            ),
            Bvand(lhs, rhs)
            | Bvor(lhs, rhs)
            | Bvxor(lhs, rhs)
            | Bvnand(lhs, rhs)
            | Bvnor(lhs, rhs)
            | Bvxnor(lhs, rhs)
            | Bvadd(lhs, rhs)
            | Bvsub(lhs, rhs)
            | Bvmul(lhs, rhs)
            | Bvudiv(lhs, rhs)
            | Bvsdiv(lhs, rhs)
            | Bvurem(lhs, rhs)
            | Bvsrem(lhs, rhs)
            | Bvsmod(lhs, rhs)
            | Bvult(lhs, rhs)
            | Bvslt(lhs, rhs)
            | Bvule(lhs, rhs)
            | Bvsle(lhs, rhs)
            | Bvuge(lhs, rhs)
            | Bvsge(lhs, rhs)
            | Bvugt(lhs, rhs)
            | Bvsgt(lhs, rhs)
            | Bvshl(lhs, rhs)
            | Bvlshr(lhs, rhs)
            | Bvashr(lhs, rhs)
            | Concat(lhs, rhs)
            | Select(lhs, rhs) => format!(
                "{}({}, {})",
                match self {
                    Bvand(_, _) => "bvand",
                    Bvor(_, _) => "bvor",
                    Bvxor(_, _) => "bvxor",
                    Bvnand(_, _) => "bvnand",
                    Bvnor(_, _) => "bvnor",
                    Bvxnor(_, _) => "bvxnor",
                    Bvadd(_, _) => "bvadd",
                    Bvsub(_, _) => "bvsub",
                    Bvmul(_, _) => "bvmul",
                    Bvudiv(_, _) => "bvudiv",
                    Bvsdiv(_, _) => "bvsdiv",
                    Bvurem(_, _) => "bvurem",
                    Bvsrem(_, _) => "bvsrem",
                    Bvsmod(_, _) => "bvsmod",
                    Bvult(_, _) => "bvult",
                    Bvslt(_, _) => "bvslt",
                    Bvule(_, _) => "bvule",
                    Bvsle(_, _) => "bvsle",
                    Bvuge(_, _) => "bvuge",
                    Bvsge(_, _) => "bvsge",
                    Bvugt(_, _) => "bvugt",
                    Bvsgt(_, _) => "bvsgt",
                    Bvshl(_, _) => "bvshl",
                    Bvlshr(_, _) => "bvlshr",
                    Bvashr(_, _) => "bvashr",
                    Concat(_, _) => "concat",
                    Select(_, _) => "select",
                    _ => unreachable!(),
                },
                lhs.to_trace_string(symtab),
                rhs.to_trace_string(symtab)
            ),
            Store(array, index, value) => format!(
                "store({}, {}, {})",
                array.to_trace_string(symtab),
                index.to_trace_string(symtab),
                value.to_trace_string(symtab)
            ),
        }
    }
}
