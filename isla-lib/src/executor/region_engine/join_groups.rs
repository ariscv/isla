//! 到达片段先准备状态与定义。只有批准的合并步骤可以发布定义、历史和事件。
use super::join_terms::{self, Operation, Terms};
use super::*;
use std::collections::BTreeMap;

#[cfg(test)]
thread_local! {
    pub(in crate::executor) static FOLD_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
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
    #[allow(clippy::too_many_arguments)]
    fn prepare(
        left: &LocalFrame<'ir, B>,
        right: &LocalFrame<'ir, B>,
        base: &LocalFrame<'ir, B>,
        region: &Region,
        state: &TaskState<B>,
        shared: &SharedState<'ir, B>,
        terms: &mut Terms<'_, '_, B>,
        info: SourceLoc,
    ) -> Result<Self, ExecError> {
        use smtlib::Exp::{Or, Var};
        let guard =
            |frame: &LocalFrame<'ir, B>| frame.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
        let (a, b) = (guard(left), guard(right));
        let mark = terms.mark();
        let condition = terms.define_const(a.clone(), info);
        let union = terms.define_const(Or(Box::new(a), Box::new(b)), info);
        let guards = terms.take_operations();
        let mut frame = match prepare_state(condition, base, left, right, region, state, shared, terms, info) {
            Ok(state) => state,
            Err(error) => {
                terms.discard(mark);
                return Err(error);
            }
        };
        // 后续计划只读取到达状态，历史及可见事件延后构造。
        cost::make_mut(&mut frame.frame.local_state).speculative_access.as_mut().unwrap().guard = Some(Var(union));
        let pair = PreparedPair { state: frame, operations: terms.take_operations() };
        Ok(Self { condition, union, guards, pair })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn prepare_loop(
        previous: &LocalFrame<'ir, B>,
        next: &LocalFrame<'ir, B>,
        base: &LocalFrame<'ir, B>,
        region: &Region,
        state: &TaskState<B>,
        shared: &SharedState<'ir, B>,
        solver: &Solver<B>,
        info: SourceLoc,
    ) -> Result<(Self, (u32, u32)), ExecError> {
        let mut terms = Terms::new(solver);
        let fold = Self::prepare(previous, next, base, region, state, shared, &mut terms, info)?;
        Ok((fold, terms.symbol_range()))
    }

    pub(in crate::executor) fn publish_guards(
        self,
        solver: &mut Solver<B>,
    ) -> (Sym, smtlib::Exp<Sym>, PreparedPair<'ir, B>) {
        join_terms::emit(self.guards, solver);
        (self.condition, smtlib::Exp::Var(self.union), self.pair)
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

// 每个可折叠集合只需保留一个可重建的顺序。划分时固定最小未用成员，避免枚举组的排列。
fn minimum_cover(
    remaining: Vec<usize>,
    blocks: &[(Vec<usize>, Vec<usize>)],
    by_first: &[Vec<usize>],
    memo: &mut BTreeMap<Vec<usize>, Vec<usize>>,
) -> Vec<usize> {
    let Some(&first) = remaining.first() else { return Vec::new() };
    if let Some(solution) = memo.get(&remaining) {
        return solution.clone();
    }
    let mut best = None;
    for &index in &by_first[first] {
        let (members, _) = &blocks[index];
        if !members.iter().all(|member| remaining.binary_search(member).is_ok()) {
            continue;
        }
        let rest = remaining.iter().copied().filter(|node| members.binary_search(node).is_err()).collect();
        let mut solution = minimum_cover(rest, blocks, by_first, memo);
        solution.push(index);
        if best.as_ref().is_none_or(|current: &Vec<usize>| solution.len() < current.len()) {
            let complete = solution.len() == 1;
            best = Some(solution);
            if complete {
                break;
            }
        }
    }
    let best = best.expect("每个单成员块均可行");
    memo.insert(remaining, best.clone());
    best
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
        let frame = |node: usize| match node.checked_sub(self.arrivals.len()) {
            Some(fold) => &self.folds[fold].prepared.pair.state.frame,
            None => &self.arrivals[node].frame,
        };
        #[cfg(test)]
        FOLD_ATTEMPTS.set(FOLD_ATTEMPTS.get() + 1);
        let prepared = PreparedFold::prepare(
            frame(left),
            frame(right),
            self.base,
            self.region,
            self.state,
            self.shared,
            &mut self.terms,
            self.info,
        )?;
        let node = self.arrivals.len() + self.folds.len();
        let earliest = self.earliest(left).min(self.earliest(right));
        self.folds.push(Fold { left, right, earliest, prepared });
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

    // 只剪掉当前已失败的有序前缀。同一集合的不同成功折叠可能有不同的后继，必须分别扩展。
    fn feasible_blocks(
        &mut self,
        node: usize,
        order: &mut Vec<usize>,
        remaining: &mut [usize],
        blocks: &mut BTreeMap<Vec<usize>, Vec<usize>>,
    ) -> Result<bool, ExecError> {
        let mut members = order.clone();
        members.sort_unstable();
        blocks.entry(members).or_insert_with(|| order.clone());
        if remaining.is_empty() {
            return Ok(true);
        }
        let mark = self.terms.mark();
        let folds = self.folds.len();
        for i in 0..remaining.len() {
            let member = remaining[i];
            match self.fold(node, member) {
                Ok(next) => {
                    remaining.swap(0, i);
                    order.push(member);
                    let complete = self.feasible_blocks(next, order, &mut remaining[1..], blocks)?;
                    order.pop();
                    remaining.swap(0, i);
                    self.folds.truncate(folds);
                    self.terms.discard(mark);
                    if complete {
                        return Ok(true);
                    }
                }
                // 额外试探碰到不可用的折叠时，已有可发布的划分仍有效。
                Err(ExecError::SpeculativeReject { .. }) => (),
                Err(error) => return Err(error),
            }
        }
        Ok(false)
    }

    // 同一活跃变量在所有成员中都只有严格具体值时，组内必须相等。
    // End 可以丢弃局部 I64；区域私有槽也可能被删除。这些槽不能证明下界。
    fn strict_lower_bound(&self) -> usize {
        let at_end = self.arrivals.iter().any(|a| matches!(a.frame.instrs.get(a.frame.pc), Some(Instr::End)));
        self.frame(0)
            .vars()
            .keys()
            .filter_map(|name| {
                if self.region.local_variables.contains(name) && !self.base.vars().contains_key(name) {
                    return None;
                }
                let mut distinct = Vec::new();
                for arrival in self.arrivals {
                    let frame = &arrival.frame;
                    let UVal::Init(value) = frame.vars().get(name)? else { return None };
                    match value {
                        Val::String(_) => (),
                        Val::I64(_) if *name == RETURN || !at_end => (),
                        _ => return None,
                    }
                    if !distinct.contains(&value) {
                        distinct.push(value);
                    }
                }
                Some(distinct.len())
            })
            .max()
            .unwrap_or(1)
    }

    fn better_partition(
        &mut self,
        members: &mut [usize],
        upper_bound: usize,
    ) -> Result<Option<Vec<Vec<usize>>>, ExecError> {
        let mut blocks = BTreeMap::new();
        for i in 0..members.len() {
            members.swap(0, i);
            let first = members[0];
            let complete = self.feasible_blocks(first, &mut vec![first], &mut members[1..], &mut blocks)?;
            members.swap(0, i);
            if complete {
                let all = (0..members.len()).collect::<Vec<_>>();
                return Ok(Some(vec![blocks.remove(&all).unwrap()]));
            }
        }
        let blocks: Vec<_> = blocks.into_iter().collect();
        let mut by_first = vec![Vec::new(); members.len()];
        for (i, (block, _)) in blocks.iter().enumerate() {
            by_first[block[0]].push(i);
        }
        let solution = minimum_cover((0..members.len()).collect(), &blocks, &by_first, &mut BTreeMap::new());
        Ok((solution.len() < upper_bound).then(|| solution.iter().map(|&i| blocks[i].1.clone()).collect()))
    }

    fn partition(&mut self) -> Result<(Vec<usize>, Option<ExecError>), ExecError> {
        let mut members: Vec<_> = (0..self.arrivals.len()).collect();
        let strict = !self.state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values);
        let start = self.terms.mark();
        if strict {
            // 严格模式中，一个已有的 SMT 整数可承载多个具体值。优先用此表示，再按来源坐标排列。
            members.sort_by_cached_key(|&node| {
                let frame = self.frame(node);
                let integers = [frame.vars(), frame.lets()]
                    .into_iter()
                    .flat_map(|bindings| bindings.values())
                    .filter_map(|value| match value {
                        UVal::Init(val) => Some(val.symbolic_variables()),
                        _ => None,
                    })
                    .flatten()
                    .filter(|sym| {
                        !self.terms.is_sail_bitvector(*sym) && matches!(self.terms.length(*sym), Some(64 | 128))
                    })
                    .count();
                (std::cmp::Reverse(integers), node)
            });
        }
        let mut groups = Vec::new();
        let mut first_rejection = None;
        for &member in &members {
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
        if groups.len() > 1 && !(strict && groups.len() == self.strict_lower_bound()) {
            if let Some(orders) = self.better_partition(&mut members, groups.len())? {
                self.folds.clear();
                self.terms.discard(start);
                groups.clear();
                for order in orders {
                    let (&first, rest) = order.split_first().unwrap();
                    let node = rest
                        .iter()
                        .try_fold(first, |node, &next| self.fold(node, next))
                        .expect("可行块的折叠顺序必须可重建");
                    groups.push(node);
                }
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

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(in crate::executor) fn feasible_order(
        arrivals: &[Arrival<'ir, B>],
        order: &[usize],
        base: &LocalFrame<'ir, B>,
        region: &Region,
        state: &TaskState<B>,
        shared: &SharedState<'ir, B>,
        solver: &Solver<B>,
        info: SourceLoc,
    ) -> bool {
        let mut planner =
            Planner { arrivals, folds: Vec::new(), terms: Terms::new(solver), base, region, state, shared, info };
        let (&first, rest) = order.split_first().unwrap();
        match rest.iter().try_fold(first, |node, &member| planner.fold(node, member)) {
            Ok(_) => true,
            Err(ExecError::SpeculativeReject { .. }) => false,
            Err(error) => panic!("对照折叠失败：{error:?}"),
        }
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
                fold.prepared,
            );
            if let Err(ExecError::SpeculativeReject { reason, function, pc, location, .. }) = &result {
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
