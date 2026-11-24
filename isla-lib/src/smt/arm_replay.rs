//! B 臂的私有求解器复用不可变入口，正文仍由既有事务处理。
use super::*;

#[derive(Clone, Copy, Default)]
struct Mark {
    declarations: usize,
    assertions: usize,
    enum_next: u32,
    floating_point: bool,
}

pub(crate) struct ArmReplay<'ctx, B> {
    solver: Solver<'ctx, B>,
    marks: Vec<Mark>,
    undo: Vec<DeclarationUndo<'ctx>>,
    assertions: Vec<Ast<'ctx>>,
    /// 每个原生作用域的起始断言偏移。回滚最多重装一个保留片段的 AST。
    scopes: Vec<usize>,
}

impl<B> Trace<B> {
    fn arm_event_count(&self) -> usize {
        self.head_prefix.as_ref().map_or(0, |prefix| prefix.events.len()) + self.local_len()
    }

    fn common_arm_events(&self, other: &Self) -> usize {
        if std::ptr::eq(self, other) {
            return self.arm_event_count();
        }
        let shared_head = match (&self.head_prefix, &other.head_prefix) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        };
        if !shared_head {
            return self.head_events().zip(other.head_events()).take_while(|(a, b)| std::ptr::eq(*a, *b)).count();
        }
        let prefix = self.head_prefix.as_ref().map_or(0, |prefix| prefix.events.len());
        let shared_projection = match (&self.projected, &other.projected) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        };
        if shared_projection {
            return prefix
                + self.projected.as_ref().map_or(0, |s| s.len)
                + self.head.iter().zip(&other.head).take_while(|(a, b)| std::ptr::eq(*a, *b)).count();
        }
        prefix + self.local_events().zip(other.local_events()).take_while(|(a, b)| std::ptr::eq(*a, *b)).count()
    }
}

impl<B> Checkpoint<B> {
    /// 调度时只看共享的已冻结迹链。实际恢复还会比较最后一段的事件身份。
    pub(crate) fn shared_arm_depth(&self, other: &Self) -> usize {
        let (mut a, mut b) = (&self.trace, &other.trace);
        let (mut an, mut bn) = (self.num, other.num);
        while an > bn {
            a = &a.as_ref().as_ref().unwrap().tail;
            an -= 1;
        }
        while bn > an {
            b = &b.as_ref().as_ref().unwrap().tail;
            bn -= 1;
        }
        while an > 0 && !Arc::ptr_eq(a, b) {
            a = &a.as_ref().as_ref().unwrap().tail;
            b = &b.as_ref().as_ref().unwrap().tail;
            an -= 1;
        }
        an
    }
}

impl<'ctx, B: BV> ArmReplay<'ctx, B> {
    pub(crate) fn new(ctx: &'ctx Context) -> Self {
        Self {
            solver: Solver::new(ctx),
            marks: Vec::new(),
            undo: Vec::new(),
            assertions: Vec::new(),
            scopes: Vec::new(),
        }
    }

    pub(crate) fn options(&self) -> (SolverOptions, bool) {
        self.solver.arm_context_options()
    }

    pub(crate) fn restore(&mut self, point: Checkpoint<B>) -> (&mut Solver<'ctx, B>, usize) {
        // SMT 性能图带跨事件边。保留该编译选项的完整图和原计数行为。
        if cfg!(feature = "smtperf") {
            let events = std::iter::successors(point.trace.as_ref().as_ref(), |t| t.tail.as_ref().as_ref())
                .map(Trace::arm_event_count)
                .sum();
            self.solver = Solver::from_arm_checkpoint(self.solver.ctx, point);
            self.solver.arm_body_enums = Some(Vec::new());
            return (&mut self.solver, events);
        }

        let old_tail = Arc::clone(&self.solver.trace.tail);
        let mut old: Vec<_> = std::iter::successors(old_tail.as_ref().as_ref(), |t| t.tail.as_ref().as_ref()).collect();
        let mut new: Vec<_> =
            std::iter::successors(point.trace.as_ref().as_ref(), |t| t.tail.as_ref().as_ref()).collect();
        old.reverse();
        new.reverse();
        assert_eq!(old.len(), self.solver.trace.checkpoints);
        assert_eq!(new.len(), point.num);
        let (mut segment, mut offset, mut common) = (0, 0, 0);
        for (a, b) in old.iter().zip(&new) {
            offset = a.common_arm_events(b);
            common += offset;
            if offset != a.arm_event_count() || offset != b.arm_event_count() {
                break;
            }
            segment += 1;
            offset = 0;
        }
        let mark = common.checked_sub(1).map_or_else(Mark::default, |index| self.marks[index]);
        let previous_assertions = self.assertions.len();
        let solver = &mut self.solver;
        assert!(solver.trace.head.is_empty());
        assert!(solver.declaration_undo.is_empty() && solver.savepoints.is_empty());
        solver.declaration_undo = std::mem::take(&mut self.undo);
        solver.rewind_declarations(mark.declarations);
        if common < self.marks.len() {
            if let Some(prefix) = &mut solver.finite_prefix {
                prefix.rewind(
                    segment,
                    offset,
                    false,
                    old.iter().enumerate().skip(segment).rev().flat_map(|(index, trace)| {
                        let start = if segment == index { offset } else { 0 };
                        let end = trace.arm_event_count();
                        trace
                            .head_events()
                            .rev()
                            .take(end - start)
                            .enumerate()
                            .map(move |(i, e)| (index, end - 1 - i, e))
                    }),
                );
            }
        }
        self.marks.truncate(common);
        self.assertions.truncate(mark.assertions);
        solver.asserts_since_check = mark.assertions;
        solver.floating_point_seen.set(mark.floating_point);
        solver.next_var = mark.enum_next;
        solver.knowledge = dedup::Knowledge::default();
        solver.replaying_arm_entry = true;
        solver.replay_assertions = Some(std::mem::take(&mut self.assertions));
        for (index, trace) in new.iter().enumerate().skip(segment) {
            let start = if index == segment { offset } else { 0 };
            for (i, event) in trace.head_events().enumerate().skip(start) {
                solver.add_event_internal(event);
                if let Some(prefix) = &mut solver.finite_prefix {
                    prefix.push(index, i, event);
                }
                self.marks.push(Mark {
                    declarations: solver.declaration_undo.len(),
                    assertions: solver.replay_assertions.as_ref().unwrap().len(),
                    enum_next: solver.next_var,
                    floating_point: solver.floating_point_seen.get(),
                });
            }
        }
        solver.replaying_arm_entry = false;
        self.undo = std::mem::take(&mut solver.declaration_undo);
        self.assertions = solver.replay_assertions.take().unwrap();

        // 活动 B 的原生作用域由事务配对回滚。入口断言按 32 条一组登记，
        // 两个相邻入口只有末段不同时可直接 pop，保留前段已登记的约束。
        let ctx = solver.ctx.z3_ctx;
        let native = solver.z3_solver;
        let mut installed = previous_assertions;
        unsafe {
            let old_scopes = self.scopes.len();
            while installed > mark.assertions {
                installed = self.scopes.pop().expect("回滚入口断言必须有原生作用域");
            }
            let pop = old_scopes - self.scopes.len();
            if pop > 0 {
                Z3_solver_pop(ctx, native, pop.try_into().unwrap());
            }
            while installed < self.assertions.len() {
                self.scopes.push(installed);
                Z3_solver_push(ctx, native);
                let end = (installed + 32).min(self.assertions.len());
                for ast in &self.assertions[installed..end] {
                    Z3_solver_assert(ctx, native, ast.z3_ast);
                }
                installed = end;
            }
        }

        solver.trace.checkpoints = point.num;
        solver.trace.tail = point.trace;
        solver.next_var = point.next_var;
        solver.cycles = point.cycles;
        solver.arm_body_enums = Some(Vec::new());
        (solver, self.marks.len() - common)
    }

    pub(crate) fn finish(&mut self) {
        let solver = &mut self.solver;
        assert!(solver.savepoints.is_empty() && solver.declaration_undo.is_empty());
        for name in solver.arm_body_enums.take().expect("必须先恢复入口") {
            solver.enums.enums.remove(&name).unwrap().dec_refs(solver.ctx.z3_ctx);
        }
        // 正文创建的枚举可在事务内共享，退出 B 后只保留入口可见的枚举。
        solver.trace.head.clear();
        solver.trace.event_guards.clear();
        solver.clear_stashed_model();
        solver.last_check_sat = false;
        solver.shadow_witnesses = witness_shadow::Bank::new(solver.ctx);
        if let Some(prefix) = &mut solver.finite_prefix {
            prefix.invalidate_candidates();
        }
    }
}
