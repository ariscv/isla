//! 到达片段先准备状态与定义。只有批准的合并步骤可以发布定义、历史和事件。
use super::join_terms::{self, Operation, Terms};
use super::*;
use crate::executor::region_merge::fold_prepared_exit_frontiers;

pub(in crate::executor) struct Arrival<'ir, B> {
    pub(in crate::executor) source: (usize, usize),
    pub(in crate::executor) frame: LocalFrame<'ir, B>,
}

pub(in crate::executor) struct PreparedFold<'ir, B> {
    condition: Sym,
    union: Sym,
    guards: Vec<Operation<B>>,
    pair: PreparedPair<'ir, B>,
}

impl<'ir, B: BV> PreparedFold<'ir, B> {
    pub(in crate::executor) fn publish_guards(
        self,
        solver: &mut Solver<B>,
    ) -> (Sym, smtlib::Exp<Sym>, Option<PreparedPair<'ir, B>>) {
        join_terms::emit(self.guards, solver);
        (self.condition, smtlib::Exp::Var(self.union), Some(self.pair))
    }
}

struct Fold<'ir, B> {
    left: usize,
    right: usize,
    earliest: usize,
    prepared: PreparedFold<'ir, B>,
}

enum Output<'ir, B> {
    Complete { sides: [Option<usize>; 2], pair: Option<PreparedPair<'ir, B>> },
    Groups { nodes: Vec<usize>, reason: SpeculativeRejectReason },
}

pub(in crate::executor) enum Joined<'ir, B> {
    Complete { arms: Vec<Option<LocalFrame<'ir, B>>>, pair: Option<PreparedPair<'ir, B>> },
    Groups { frames: Vec<(LocalFrame<'ir, B>, bool)>, reason: SpeculativeRejectReason },
}

pub(in crate::executor) struct JoinPlan<'ir, B> {
    arrivals: Vec<Arrival<'ir, B>>,
    folds: Vec<Fold<'ir, B>>,
    output: Output<'ir, B>,
    symbols: (u32, u32),
}

struct Planner<'a, 'ctx, 'ir, B> {
    arrivals: &'a [Arrival<'ir, B>],
    folds: Vec<Fold<'ir, B>>,
    terms: Terms<'a, 'ctx, B>,
    base: &'a LocalFrame<'ir, B>,
    region: &'a Region,
    state: &'a TaskState<B>,
    shared: &'a SharedState<'ir, B>,
    info: SourceLoc,
}

impl<'ir, B: BV> Planner<'_, '_, 'ir, B> {
    fn earliest(&self, node: usize) -> usize {
        if let Some(fold) = node.checked_sub(self.arrivals.len()) {
            self.folds[fold].earliest
        } else {
            node
        }
    }

    fn frame(&self, node: usize) -> &LocalFrame<'ir, B> {
        if let Some(fold) = node.checked_sub(self.arrivals.len()) {
            &self.folds[fold].prepared.pair.state.frame
        } else {
            &self.arrivals[node].frame
        }
    }

    fn pair(&mut self, condition: Sym, left: usize, right: usize) -> Result<PreparedPair<'ir, B>, ExecError> {
        let mark = self.terms.mark();
        let frame = |node: usize| match node.checked_sub(self.arrivals.len()) {
            Some(fold) => &self.folds[fold].prepared.pair.state.frame,
            None => &self.arrivals[node].frame,
        };
        let result = prepare_state(
            condition,
            self.base,
            frame(left),
            frame(right),
            self.region,
            self.state,
            self.shared,
            &mut self.terms,
            self.info,
        );
        match result {
            Ok(state) => Ok(PreparedPair { state, operations: self.terms.take_operations() }),
            Err(error) => {
                self.terms.discard(mark);
                Err(error)
            }
        }
    }

    fn fold(&mut self, left: usize, right: usize) -> Result<usize, ExecError> {
        use smtlib::Exp::{Or, Var};
        let guard = |node| self.frame(node).local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let (a, b) = (guard(left), guard(right));
        let mark = self.terms.mark();
        let condition = self.terms.define_const(a.clone(), self.info);
        let union = self.terms.define_const(Or(Box::new(a), Box::new(b)), self.info);
        let guards = self.terms.take_operations();
        let mut pair = match self.pair(condition, left, right) {
            Ok(pair) => pair,
            Err(error) => {
                self.terms.discard(mark);
                return Err(error);
            }
        };
        // 给上一级计划看的只有到达状态。记录、逻辑臂和事件在发布阶段拼接。
        let access = cost::make_mut(&mut pair.state.frame.local_state).speculative_access.as_mut().unwrap();
        access.guard = Some(Var(union));
        let node = self.arrivals.len() + self.folds.len();
        let earliest = self.earliest(left).min(self.earliest(right));
        self.folds.push(Fold { left, right, earliest, prepared: PreparedFold { condition, union, guards, pair } });
        Ok(node)
    }

    fn complete(&mut self, condition: Sym) -> Result<Output<'ir, B>, ExecError> {
        let mut sides = [None, None];
        for (node, arrival) in self.arrivals.iter().enumerate() {
            let side = &mut sides[arrival.source.0];
            *side = Some(match *side {
                None => node,
                Some(previous) => self.fold(previous, node)?,
            });
        }
        let pair = match sides {
            [Some(left), Some(right)] => Some(self.pair(condition, left, right)?),
            _ => None,
        };
        Ok(Output::Complete { sides, pair })
    }

    fn partition(&mut self) -> Result<(Vec<usize>, Option<ExecError>), ExecError> {
        let mut members: Vec<_> = (0..self.arrivals.len()).collect();
        if !self.state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values) {
            // 严格模式中，一个已有的 SMT 整数可承载多个具体值。优先用此表示，再按来源坐标排列。
            members.sort_by_cached_key(|&node| {
                let frame = self.frame(node);
                let integers = [frame.vars(), frame.lets()]
                    .into_iter()
                    .flat_map(|bindings| bindings.values())
                    .filter(|value| {
                        matches!(value, UVal::Init(Val::Symbolic(sym))
                        if !self.terms.is_sail_bitvector(*sym)
                            && matches!(self.terms.length(*sym), Some(64 | 128)))
                    })
                    .count();
                (std::cmp::Reverse(integers), node)
            });
        }
        let mut groups = Vec::new();
        let mut first_rejection = None;
        for member in members {
            let mut selected = None;
            for group in &mut groups {
                match self.fold(*group, member) {
                    Ok(node) => {
                        *group = node;
                        selected = Some(node);
                        break;
                    }
                    Err(error @ ExecError::SpeculativeReject { reason, .. }) if is_join_rejection(reason) => {
                        first_rejection.get_or_insert(error);
                    }
                    Err(error) => return Err(error),
                }
            }
            if selected.is_none() {
                groups.push(member);
            }
        }
        groups.sort_unstable_by_key(|&node| self.earliest(node));
        Ok((groups, first_rejection))
    }
}

impl<'ir, B: BV> JoinPlan<'ir, B> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn prepare(
        mut arrivals: Vec<Arrival<'ir, B>>,
        condition: Sym,
        keep_separate: bool,
        base: &LocalFrame<'ir, B>,
        region: &Region,
        state: &TaskState<B>,
        shared: &SharedState<'ir, B>,
        solver: &Solver<B>,
        info: SourceLoc,
    ) -> Result<Self, ExecError> {
        arrivals.sort_unstable_by_key(|arrival| arrival.source);
        assert!(arrivals.windows(2).all(|pair| pair[0].source != pair[1].source), "汇合成员坐标必须唯一");
        assert!(arrivals.iter().all(|arrival| arrival.frame.arm_error.is_none()), "错误终态由区域事务独立发布");
        let mut planner = Planner {
            arrivals: &arrivals,
            folds: Vec::new(),
            terms: Terms::new(solver),
            base,
            region,
            state,
            shared,
            info,
        };
        let output = if arrivals.len() <= 2 {
            match planner.complete(condition) {
                Ok(output) => output,
                Err(ExecError::SpeculativeReject { reason, .. }) if keep_separate && is_join_rejection(reason) => {
                    Output::Groups { nodes: vec![0, 1], reason }
                }
                Err(error) => return Err(error),
            }
        } else {
            let (nodes, rejection) = planner.partition()?;
            if nodes.len() == 1 {
                Output::Complete { sides: [Some(nodes[0]), None], pair: None }
            } else {
                let error = rejection.expect("分开的汇合组必须有明确原因");
                let ExecError::SpeculativeReject { reason, .. } = error else { unreachable!() };
                if !keep_separate {
                    return Err(error);
                }
                Output::Groups { nodes, reason }
            }
        };
        let symbols = planner.terms.symbol_range();
        let folds = planner.folds;
        Ok(Self { arrivals, folds, output, symbols })
    }

    pub(super) fn separate_groups(&self) -> Option<usize> {
        match &self.output {
            Output::Groups { nodes, .. } => Some(nodes.len()),
            Output::Complete { .. } => None,
        }
    }

    #[cfg(test)]
    pub(in crate::executor) fn groups(&self) -> Vec<Vec<(usize, usize)>> {
        let mut members: Vec<Vec<_>> = self.arrivals.iter().map(|arrival| vec![arrival.source]).collect();
        for fold in &self.folds {
            let mut joined = members[fold.left].clone();
            joined.extend_from_slice(&members[fold.right]);
            joined.sort_unstable();
            members.push(joined);
        }
        match &self.output {
            Output::Complete { sides, .. } => {
                let mut joined: Vec<_> =
                    sides.iter().flatten().flat_map(|&node| members[node].iter().copied()).collect();
                joined.sort_unstable();
                vec![joined]
            }
            Output::Groups { nodes, .. } => nodes.iter().map(|&node| members[node].clone()).collect(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn construct(
        self,
        base: &LocalFrame<'ir, B>,
        region: &Region,
        state: &TaskState<B>,
        shared: &SharedState<'ir, B>,
        solver: &mut Solver<B>,
        info: SourceLoc,
    ) -> Result<Joined<'ir, B>, ExecError> {
        solver.reserve_join_symbols(self.symbols.0, self.symbols.1);
        let count = self.arrivals.len();
        let mut frames: Vec<_> =
            self.arrivals.into_iter().map(|arrival| Some((arrival.frame, None, arrival.source))).collect();
        let mut builds = 0;
        for fold in self.folds {
            let (left, mut history, left_source) = frames[fold.left].take().expect("计划左成员只能消费一次");
            let (right, _, right_source) = frames[fold.right].take().expect("计划右成员只能消费一次");
            let result = fold_prepared_exit_frontiers(
                left,
                right,
                &mut history,
                base,
                region,
                state,
                shared,
                solver,
                info,
                Some(fold.prepared),
            );
            if let Err(ExecError::SpeculativeReject { reason, function, pc, location }) = &result {
                panic!("已批准的汇合拒绝：成员 {left_source:?}、{right_source:?}，站点 {function:?} @{pc} {location:?}，{reason:?}");
            }
            builds += 1;
            frames.push(Some((result?, history, left_source.min(right_source))));
        }
        let output = match self.output {
            Output::Complete { sides, pair } => {
                let arms = sides.into_iter().map(|node| node.map(|node| frames[node].take().unwrap().0)).collect();
                builds += usize::from(pair.is_some());
                Joined::Complete { arms, pair }
            }
            Output::Groups { nodes, reason } => {
                let frames = nodes.into_iter().map(|node| (frames[node].take().unwrap().0, node >= count)).collect();
                Joined::Groups { frames, reason }
            }
        };
        let groups = match &output {
            Joined::Complete { .. } => usize::from(count > 0),
            Joined::Groups { frames, .. } => frames.len(),
        };
        assert_eq!(builds + groups, count, "每个合并节点和最终成员都必须恰好消费一次");
        assert!(frames.into_iter().all(|frame| frame.is_none()), "所有成员必须在最终汇合中消费");
        Ok(output)
    }
}
