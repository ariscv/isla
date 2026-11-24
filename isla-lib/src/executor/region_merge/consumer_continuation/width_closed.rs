//! 变长值在通过纯包装时保留各臂的具体位宽，直到该调用链恢复定长。
use super::*;
use crate::ir::regions::instruction_operands;
use crate::primop::Effect;
use std::collections::{BTreeMap, BTreeSet};

struct Join<'ir, B> {
    function: Name,
    instrs: &'ir [Instr<Name, B>],
    depth: usize,
    region: Arc<Region>,
    dead: HashSet<Name>,
}

/// 已初始化的局部值可以参与构造或解包；地址和未定义值不能用来证明纯包装。
fn is_local_value(exp: &Exp<Name>, initialized: &HashSet<Name>) -> bool {
    match exp {
        Exp::Id(name) => initialized.contains(name),
        Exp::Ref(_) | Exp::Undefined(_) => false,
        Exp::Field(exp, _) | Exp::Kind(_, exp) | Exp::Unwrap(_, exp) => is_local_value(exp, initialized),
        Exp::Call(_, args) => args.iter().all(|arg| is_local_value(arg, initialized)),
        Exp::Struct(_, fields) => fields.iter().all(|(_, exp)| is_local_value(exp, initialized)),
        _ => true,
    }
}

fn fixed_width(ty: &Ty<Name>, types: &crate::ir::IRTypeInfo, visiting: &mut HashSet<Name>) -> bool {
    match ty {
        Ty::Bits(_) | Ty::Bool | Ty::Bit | Ty::I64 | Ty::I128 | Ty::Enum(_) | Ty::Unit => true,
        Ty::FixedVector(_, elem) => fixed_width(elem, types, visiting),
        Ty::Struct(name) if visiting.insert(*name) => {
            let fixed = types
                .structs
                .get(name)
                .is_some_and(|fields| fields.values().all(|field| fixed_width(field, types, visiting)));
            visiting.remove(name);
            fixed
        }
        _ => false,
    }
}

struct Scan<'a, 'ir, B> {
    shared: &'a SharedState<'ir, B>,
    summaries: &'a HashMap<Name, FunctionEffect>,
    assumptions: &'a HashMap<Name, Vec<(Vec<Val<B>>, Val<B>)>>,
    wrappers: HashMap<Name, bool>,
}

impl<'ir, B: BV> Scan<'_, 'ir, B> {
    fn pure_wrapper(&mut self, name: Name) -> bool {
        if let Some(pure) = self.wrappers.get(&name) {
            return *pure;
        }
        if self.shared.trace_functions.contains(&name)
            || self.shared.probes.contains(&name)
            || self.assumptions.contains_key(&name)
            || !self.summaries.get(&name).is_some_and(|s| s.effect == Effect::Pure && !s.non_returning)
        {
            return false;
        }
        let Some((params, _, body)) = self.shared.functions.get(&name) else { return false };
        // 在遍历子调用前标记；遇到递归边时不能证明包装有限。
        self.wrappers.insert(name, false);
        let mut locals = HashSet::from([RETURN]);
        let initialized: HashSet<_> = params.iter().map(|(name, _)| *name).collect();
        locals.extend(initialized.iter().copied());
        // 前向边按指令位置处理。多条边汇合时只保留每条边都定义的槽。
        let mut pending = BTreeMap::from([(0, (locals, initialized))]);
        let mut pure = true;
        while let Some((pc, (mut locals, mut initialized))) = pending.pop_first() {
            let targets = match body.get(pc) {
                Some(Instr::End) if initialized.contains(&RETURN) => continue,
                Some(Instr::Goto(target)) if *target > pc => [Some(*target), None],
                Some(Instr::Jump(exp, target, _)) if *target > pc && is_local_value(exp, &initialized) => {
                    [Some(pc + 1), Some(*target)]
                }
                Some(instr) if self.step(instr, &mut locals, &mut initialized).is_some() => [Some(pc + 1), None],
                _ => {
                    pure = false;
                    break;
                }
            };
            for target in targets.into_iter().flatten() {
                pending
                    .entry(target)
                    .and_modify(|(old_locals, old_initialized)| {
                        old_locals.retain(|name| locals.contains(name));
                        old_initialized.retain(|name| initialized.contains(name));
                    })
                    .or_insert_with(|| (locals.clone(), initialized.clone()));
            }
        }
        self.wrappers.insert(name, pure);
        pure
    }

    /// 仅接受确定执行的局部计算。普通推演允许的内存读、断言与寄存器访问
    /// 禁止进入这个延续，因为原定出口后只应重复执行纯计算。
    fn step(
        &mut self,
        instr: &Instr<Name, B>,
        locals: &mut HashSet<Name>,
        initialized: &mut HashSet<Name>,
    ) -> Option<(Name, HashSet<Name>)> {
        let (expressions, dest, _) = instruction_operands(instr);
        if !expressions.iter().all(|exp| is_local_value(exp, initialized)) {
            return None;
        }
        let name = match instr {
            Instr::Decl(name, ..) => {
                locals.insert(*name);
                initialized.remove(name);
                return Some((*name, HashSet::new()));
            }
            Instr::Init(name, ..) => {
                locals.insert(*name);
                *name
            }
            _ => {
                let Loc::Id(name) = dest? else { return None };
                if !locals.contains(name) {
                    return None;
                }
                match instr {
                    Instr::Copy(..) => (),
                    Instr::PrimopUnary(_, f, ..) if primop::unary_effect(*f) == Some(Effect::Pure) => (),
                    Instr::PrimopBinary(_, f, ..) if primop::binary_effect(*f) == Some(Effect::Pure) => (),
                    Instr::PrimopVariadic(_, f, ..) if primop::variadic_effect(*f) == Some(Effect::Pure) => (),
                    Instr::Call(_, _, callee, args, ..)
                        if !self.shared.functions.contains_key(callee)
                            && self.shared.type_info.union_ctors.contains(callee)
                            && args.len() == 1 =>
                    {
                        ()
                    }
                    Instr::Call(_, _, callee, ..) if self.pure_wrapper(*callee) => (),
                    _ => return None,
                }
                *name
            }
        };
        let mut inputs = HashSet::new();
        for exp in expressions {
            exp.collect_ids(&mut inputs);
        }
        initialized.insert(name);
        Some((name, inputs))
    }

    fn find_join(
        &mut self,
        frame: &LocalFrame<'ir, B>,
        first: &LocalFrame<'ir, B>,
        dest: Name,
    ) -> Option<Join<'ir, B>> {
        let mut site = first.clone();
        let mut start = frame.pc;
        let mut tainted = HashSet::from([dest]);
        loop {
            let depth = site.backtrace.len();
            let parent = frame.region_execution.as_ref().filter(|parent| parent.entry_depth == depth);
            let mut locals: HashSet<_> = site.vars().keys().copied().collect();
            let mut initialized: HashSet<_> =
                site.vars().iter().filter_map(|(name, val)| matches!(val, UVal::Init(_)).then_some(*name)).collect();
            // 返回目的槽在快照里仍是调用前的内容；实际返回会初始化它。
            initialized.extend(tainted.iter().copied());
            let mut types: HashMap<_, _> =
                self.shared.functions.get(&site.function_name).map_or_else(HashMap::new, |(params, ret_ty, _)| {
                    params.iter().copied().chain([(RETURN, *ret_ty)]).collect()
                });
            let mut nodes = BTreeSet::new();
            let mut dirty = tainted.clone();
            let mut pc = start + 1;
            for instr in &site.instrs[..pc] {
                if let Instr::Decl(name, ty, _) | Instr::Init(name, ty, ..) = instr {
                    types.insert(*name, ty);
                }
            }
            let next = with_function_regions(&site, self.shared, self.summaries, true, |analysis| loop {
                let instr = site.instrs.get(pc)?;
                tainted.retain(|name| !analysis.slot_unused_at(pc, *name));
                if tainted.is_empty() {
                    let dead = dirty.into_iter().filter(|name| analysis.slot_unused_at(pc, *name)).collect();
                    return Some(Ok((pc, nodes, dead)));
                }
                // 只能在父区域自己的范围内执行。可以停在父出口，不能执行出口指令。
                if parent.is_some_and(|parent| {
                    !parent.region.nodes.contains(&pc)
                        || parent.region.join == RegionPoint::Instruction(pc)
                        || (parent.region.join == RegionPoint::FunctionExit && matches!(instr, Instr::End))
                }) {
                    return None;
                }
                nodes.insert(pc);
                match instr {
                    Instr::End if tainted.contains(&RETURN) => return Some(Err(())),
                    Instr::Goto(target) if *target > pc => {
                        pc = *target;
                        continue;
                    }
                    _ => (),
                }
                let (name, inputs) = self.step(instr, &mut locals, &mut initialized)?;
                if let Instr::Decl(_, ty, _) | Instr::Init(_, ty, ..) = instr {
                    types.insert(name, ty);
                }
                if !tainted.is_disjoint(&inputs)
                    && !types.get(&name).is_some_and(|ty| fixed_width(ty, &self.shared.type_info, &mut HashSet::new()))
                {
                    dirty.insert(name);
                    tainted.insert(name);
                } else {
                    tainted.remove(&name);
                }
                pc += 1;
            })?;
            if let Ok((join, nodes, dead)) = next {
                return Some(Join {
                    function: site.function_name,
                    instrs: site.instrs,
                    depth,
                    region: Arc::new(Region {
                        branch_pc: start,
                        join: RegionPoint::Instruction(join),
                        has_back_edge: false,
                        nodes,
                        kind: crate::ir::regions::RegionKind::Reconvergent,
                        local_variables: Default::default(),
                    }),
                    dead,
                });
            }
            if self.shared.trace_functions.contains(&site.function_name) {
                return None;
            }
            let &(caller, call_pc) = site.backtrace.last()?;
            let &(_, _, instrs) = self.shared.functions.get(&caller)?;
            let Instr::Call(Loc::Id(slot), _, callee, _, _) = instrs.get(call_pc)? else { return None };
            if *callee != site.function_name {
                return None;
            }
            pop_call_stack(&mut site);
            if !site.vars().contains_key(slot) {
                return None;
            }
            cost::make_mut(&mut site.backtrace).pop();
            site.function_name = caller;
            site.instrs = instrs;
            site.pc = call_pc + 1;
            start = call_pc;
            tainted = HashSet::from([*slot]);
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::executor::region_merge) fn try_join<'ir, 'task, B: BV, S: ForkSink<'ir, 'task, B> + ?Sized>(
    record_id: usize,
    condition: Sym,
    base: &LocalFrame<'ir, B>,
    arms: &[Vec<LocalFrame<'ir, B>>; 2],
    tid: usize,
    task_id: TaskId,
    fraction: &mut Fraction,
    timeout: PathTimeout,
    stop: Option<&'task StopConditions>,
    sink: &S,
    frame: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<RegionResult>, ExecError> {
    if stop.is_some() || !shared.probes.is_empty() || !shared.probe_functions.is_empty() {
        return Ok(None);
    }
    let pc = frame.pc;
    let same_producer = frame
        .region_execution
        .as_ref()
        .is_some_and(|parent| parent.entry_depth == frame.backtrace.len() && parent.region.branch_pc == pc);
    let dest = match &frame.instrs[pc] {
        Instr::PrimopUnary(Loc::Id(dest), ..)
        | Instr::PrimopBinary(Loc::Id(dest), ..)
        | Instr::PrimopVariadic(Loc::Id(dest), ..)
        | Instr::Copy(Loc::Id(dest), ..)
            if frame.vars().contains_key(dest) =>
        {
            *dest
        }
        _ => return Ok(None),
    };
    let Some(first) = arms.iter().flatten().next() else { return Ok(None) };
    let width = |part: &LocalFrame<'ir, B>| match part.vars().get(&dest) {
        Some(UVal::Init(value)) => crate::primop_util::merge_bit_width(value, solver, info).ok().flatten(),
        _ => None,
    };
    let Some(first_width) = width(first) else { return Ok(None) };
    let mut differs = false;
    for arm in arms.iter().flatten() {
        if arm.pc != pc + 1 || arm.function_name != frame.function_name || arm.backtrace != frame.backtrace {
            return Ok(None);
        }
        let Some(width) = width(arm) else { return Ok(None) };
        differs |= width != first_width;
    }
    if !differs {
        return Ok(None);
    }

    let global = state.execution_limits.as_ref().is_some_and(|limits| limits.region_global_state);
    let summaries = state.region_effect_summaries.get_or_init(|| function_effect_summaries(shared, global));
    let mut scan = Scan { shared, summaries, assumptions: &frame.function_assumptions, wrappers: HashMap::new() };
    let mut scan_origin = frame.clone();
    if same_producer {
        // 同一指令继续枚举剩余长度，由最外层一次性推进全部具体宽度。
        // 不再创建中间 Guarded 位向量，也不在这里跨越父层出口。
        scan_origin.region_execution = None;
    }
    let Some(join) = scan.find_join(&scan_origin, first, dest) else { return Ok(None) };
    if same_producer {
        if charge_fragment_growth(base, arms.iter().map(Vec::len).sum::<usize>() - 1).is_err() {
            return Ok(None);
        }
        frame.region_arrivals = arms
            .iter()
            .flatten()
            .map(|part| {
                let mut part = part.clone();
                part.region_execution = frame.region_execution.clone();
                part.speculation_mode = frame.speculation_mode;
                part
            })
            .collect();
        return Ok(Some(RegionResult::Separate {
            reason: SpeculativeRejectReason::IncompatibleState,
            merged_groups: false,
        }));
    }
    let source_depth = frame.backtrace.len();
    let mut execution = base.region_execution.as_ref().unwrap().clone();
    execution.region = Arc::clone(&join.region);
    execution.entry_depth = join.depth;
    execution.verified_prefix = None;
    if join.depth < source_depth && frame.region_execution.is_none() {
        execution.catch_return = Some(fresh_call_scope());
        execution.write_depth = join.depth;
    }

    let tx = solver.start_transaction();
    let pending = ArmErrorSink::new();
    let result = (|| {
        let mut reached = [Vec::new(), Vec::new()];
        for (side, arms) in arms.iter().enumerate() {
            for arrival in arms {
                let mut part = arrival.clone();
                part.region_execution = Some(execution.clone());
                let owner = part.region_arm.expect("到达项必须拥有逻辑臂");
                let guard = part.local_state.speculative_access.as_ref().unwrap().guard.clone().unwrap();
                let part_tx = solver.start_transaction_with_guard(Some(guard));
                let alive = solver.with_logical_arm(owner, |solver| {
                    advance_region_arm(
                        tid, task_id, fraction, timeout, stop, &pending, &mut part, state, shared, solver, true,
                        part_tx, info,
                    )
                })?;
                if alive {
                    if part.region_arrivals.is_empty() {
                        reached[side].push(part);
                    } else {
                        reached[side].append(&mut part.region_arrivals);
                    }
                }
            }
        }
        let Some(first) = reached.iter().flatten().next() else { return Ok(None) };
        if reached.iter().flatten().any(prefix_commit::is_cut) {
            return Ok(None);
        }
        let mut base = base.clone();
        let mut candidate = frame.clone();
        for position in [&mut base, &mut candidate] {
            for _ in join.depth..source_depth {
                pop_call_stack(position);
                cost::make_mut(&mut position.backtrace).pop().expect("目标在当前调用栈内");
            }
            position.function_name = join.function;
            position.instrs = join.instrs;
            position.pc = join.region.branch_pc;
            position.stack_call = first.stack_call.clone();
            position.vars_mut().retain(|name, _| !join.dead.contains(name));
            let local = cost::make_mut(&mut position.local_state);
            local.call_instance = first.local_state.call_instance;
            local.loop_attempt_seen = first.local_state.loop_attempt_seen;
            if let Some(access) = local.speculative_access.as_mut() {
                access.call_scope = first.local_state.speculative_access.as_ref().unwrap().call_scope;
            }
        }
        execution.catch_return = None;
        base.region_execution = Some(execution);
        for part in reached.iter_mut().flatten() {
            assert_eq!(part.function_name, join.function);
            assert_eq!(part.backtrace.len(), join.depth);
            assert_eq!(RegionPoint::Instruction(part.pc), join.region.join);
            part.vars_mut().retain(|name, _| !join.dead.contains(name));
            promote_initials(&mut base, part, solver);
        }
        let result = finish_arrivals(
            record_id,
            condition,
            &join.region,
            true,
            candidate.region_execution.is_none(),
            &base,
            reached,
            &mut candidate,
            state,
            shared,
            solver,
            info,
        )?;
        Ok(matches!(result, RegionResult::Merged).then_some((result, candidate)))
    })();
    match result {
        Ok(Some((result, candidate))) => {
            solver.commit_transaction();
            *frame = candidate;
            pending.forward(sink);
            if diagnostics::enabled() {
                eprintln!(
                    "{}",
                    serde_json::json!({
                        "kind": "width_closed_continuation",
                        "function": diagnostics::name_string(first.function_name, &shared.symtab),
                        "pc": pc,
                        "join_function": diagnostics::name_string(join.function, &shared.symtab),
                        "join": frame.pc,
                        "arms": arms.iter().map(Vec::len).sum::<usize>(),
                    })
                );
            }
            Ok(Some(result))
        }
        Ok(None) | Err(ExecError::SpeculativeReject { .. }) => {
            solver.rollback_transaction(tx);
            Ok(None)
        }
        Err(error) => {
            solver.rollback_transaction(tx);
            Err(error)
        }
    }
}
