//! A 独占主求解器。领取者只提交从入口重放所得的 B 臂数据。
use super::*;
use crate::executor::region_arm::{
    self, ArmJob, ArmPath, Delivery, ErrorLeaf, JoinCell, QueuedArm, RegionId, RemoteArrival, Scheduler, ThreadSlot,
};
use crate::executor::region_summary::{constraint_binary, constraint_unary};
use crate::smt::{ArmSuffixEvent, SymRemap};

pub(super) use region_arm::ArmCell;
pub(super) type Entry<'a, B> = (Option<ThreadSlot<'a>>, Checkpoint<B>);

pub(super) struct ScheduledErrors<'a, 'ir, 'task, B: BV> {
    pub errors: &'a ArmErrorSink<'ir, 'task, B>,
    pub scheduler: Option<Scheduler<'a, 'ir, B>>,
}

impl<'ir, 'task, B: BV> ForkSink<'ir, 'task, B> for ScheduledErrors<'_, 'ir, 'task, B> {
    fn submit(&self, task: Task<'ir, 'task, B>) {
        self.errors.submit(task);
    }

    fn arm_scheduler(&self) -> Option<Scheduler<'_, 'ir, B>> {
        self.scheduler
    }
}

/// B 只执行能在私有帧和事务中隔离的指令。按实际路径检查，允许被调函数内的循环和递归。
pub(super) fn transferable_instruction<B: BV>(frame: &LocalFrame<B>, shared: &SharedState<B>) -> bool {
    let effect_ok = |effect| {
        effect == Some(primop::Effect::Pure)
            || (effect == Some(primop::Effect::ReadsMemory) && frame.memory.is_pure_reader())
    };
    match &frame.instrs[frame.pc] {
        Instr::Decl(..)
        | Instr::Init(..)
        | Instr::Copy(..)
        | Instr::End
        | Instr::Goto(_)
        | Instr::Jump(..)
        | Instr::Exit(..)
        | Instr::Arbitrary => true,
        Instr::PrimopUnary(_, f, ..) => effect_ok(primop::unary_effect(*f)) || constraint_unary(*f),
        Instr::PrimopBinary(_, f, ..) => effect_ok(primop::binary_effect(*f)) || constraint_binary(*f),
        Instr::PrimopVariadic(_, f, ..) => effect_ok(primop::variadic_effect(*f)),
        Instr::Call(_, _, name, ..) => {
            shared.functions.contains_key(name)
                || shared.type_info.union_ctors.contains(name)
                || matches!(
                    *name,
                    REG_DEREF
                        | READ_REGISTER_FROM_VECTOR
                        | WRITE_REGISTER_FROM_VECTOR
                        | INTERNAL_VECTOR_INIT
                        | INTERNAL_VECTOR_UPDATE
                        | ITE_PHI
                )
        }
        _ => false,
    }
}

pub(super) fn entry<'a, 'ir: 'a, 'task, B: BV>(
    sink: &'a (impl ForkSink<'ir, 'task, B> + ?Sized),
    frame: &LocalFrame<'ir, B>,
    state: &TaskState<B>,
    region: &Region,
    solver: &mut Solver<B>,
) -> Option<Entry<'a, B>> {
    if !state.execution_limits.as_ref().is_some_and(ExecutionLimits::can_schedule_region_arm)
        || !region_arm::transferable_entry(frame)
        || solver.transaction_invalid()
        || (solver.transaction_depth() != 0
            && (solver.current_logical_arm().is_none() || solver.current_logical_arm() != frame.region_arm))
        || region.has_back_edge
        || state.reverse_region_ready
        || state.region_step_budget().is_some()
    {
        return None;
    }
    let scheduler = sink.arm_scheduler()?;
    let slot = scheduler.threads.reserve();
    if slot.is_none() && !scheduler.queue.has_helper() {
        region_arm::observe(state, "no_slot").expect("名额观察点不可失败");
        return None;
    };
    Some((slot, region_arm::capture_arm_entry_checkpoint(solver)))
}

#[allow(clippy::too_many_arguments)]
fn run_b<'ir, B: BV>(
    job: ArmJob<'ir, B>,
    tid: usize,
    cancelled: Arc<AtomicBool>,
    scheduler: Option<Scheduler<'_, 'ir, B>>,
    stop: Option<&StopConditions>,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
) -> Result<Delivery<'ir, B>, ExecError> {
    let ArmJob { checkpoint, options, mut base, pc, guard, task, mut fraction, timeout, info } = job;
    let memory_task = stats::memory_stats::enabled().then(|| stats::memory_stats::begin_task(task.as_usize()));
    let _ = &memory_task;
    base.path_timing.start_active();
    let mut config = Config::new();
    (config.solver_options, config.validation) = options;
    region_arm::observe(state, "context")?;
    let ctx = Context::new(config);
    let prefix = Arc::clone(checkpoint.path_cache_parts().2);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let start = solver.next_join_symbol();
    let root = solver.start_transaction();
    let mut errors = ArmErrorSink::new();
    let mut run = |solver: &mut Solver<B>| {
        let execution = base.region_execution.as_mut().unwrap();
        execution.remote_cancel =
            Some(region_arm::Cancellation::new(cancelled.clone(), execution.remote_cancel.take()));
        if crate::config::RegionOptions::current().progress {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"region_arm_start","root_attempt":diagnostics::root_attempt(),
                "task":task.as_usize(),"function":diagnostics::name_string(base.function_name,&shared.symtab),
                "pc":execution.region.branch_pc})
            );
        }
        let region = RegionId::new(vec![base.function_name.as_u32() as usize, execution.region.branch_pc]);
        let entry_depth = execution.entry_depth;
        let outer_region = execution.region.clone();
        let owner = solver.new_logical_arm(None);
        let tx = solver.start_transaction_with_guard(Some(guard.clone()));
        let mut frame = branch_arm(&base, pc, guard.clone(), owner);
        let result = solver.with_logical_arm(owner, |solver| {
            advance_region_arm(
                tid,
                task,
                &mut fraction,
                timeout,
                stop,
                &ScheduledErrors { errors: &errors, scheduler },
                &mut frame,
                state,
                shared,
                solver,
                false,
                tx,
                info,
            )
        });
        let dead = match result {
            Ok(live) => !live,
            Err(ExecError::SpeculativeReject { .. }) => return Ok(None),
            Err(e) => return Err(e),
        };
        if dead {
            // 死臂没有继续帧，入口帧只携带公共计时和历史。失败点另有自己的冻结帧。
            frame = base.clone();
            frame.region_arm = Some(owner);
        }
        if cancelled.load(Ordering::Acquire) {
            return Ok(None);
        }
        let Some(outer) = &frame.region_execution else { return Ok(None) };
        let at_join = frame.backtrace.len() == entry_depth
            && match outer_region.join {
                RegionPoint::Instruction(join) => frame.pc == join,
                RegionPoint::FunctionExit => matches!(frame.instrs.get(frame.pc), Some(Instr::End)),
            };
        let returned_to_caller = match (&base.stack_call, &frame.stack_call) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        };
        if (!dead && !at_join)
            || !returned_to_caller
            || !Arc::ptr_eq(&outer.region, &outer_region)
            || outer.pending_branch.is_some()
            || !frame.region_arrivals.is_empty()
            || frame.arm_error.is_some()
            || frame.pending_retry_operand.is_some()
            || frame.local_state.expression_retry_operands.is_some()
            || solver.transaction_has_memory_writes()
        {
            return Ok(None);
        }
        // 所有存活片段必须收束到这一条；其逻辑臂可以与最初分配的 owner 不同。
        let Some(suffix) = solver.export_arm_suffix(frame.region_arm.expect("到达帧必须有逻辑臂")) else {
            return Ok(None);
        };
        // 枚举 sort 在本 Context 首次声明时还会占用成员编号，应在 A 的命名空间中执行。
        if suffix.iter().any(|item| matches!(item.event, Event::Smt(smtlib::Def::DefineEnum(..), ..))) {
            return Ok(None);
        }
        if dead {
            // commit_dead_transaction 只留下 ¬g。新枚举或其它不可移交的后缀由 A 重跑。
            if !matches!(suffix.as_slice(), [item] if item.guard.as_ref() == Some(&guard)
                && matches!(&item.event, Event::Smt(smtlib::Def::Assert(smtlib::Exp::Not(inner)), ..) if **inner == guard))
            {
                return Ok(None);
            }
        }
        let ordered_reads = base.local_state.speculative_access.as_ref().unwrap().ordered_events;
        if !errors.tasks.get_mut().unwrap().iter().all(|task| transferable_error(task, &prefix, ordered_reads, start)) {
            return Ok(None);
        }
        frame.path_timing.pause_active();
        frame.region_execution.as_mut().unwrap().remote_cancel = None;
        let errors = std::mem::take(errors.tasks.get_mut().unwrap())
            .into_iter()
            .map(|task| ErrorLeaf {
                task: task.id,
                fraction: task.fraction,
                frame: task.frame,
                checkpoint: task.checkpoint,
                fork: task.fork_cond.expect("错误叶须有选择条件"),
            })
            .collect();
        Ok(Some(RemoteArrival {
            errors,
            dead,
            region,
            arm: ArmPath::new(vec![1]),
            symbols: start..solver.next_join_symbol(),
            suffix,
            deferred: solver.take_arm_assertions(),
            frame,
        }))
    };
    let result = if solver.defer_region_checks() { solver.with_deferred_region_queries(run) } else { run(&mut solver) };
    solver.rollback_transaction(root);
    result
}

fn guard_available(guard: &smtlib::Exp<Sym>, start: u32, defined: &HashSet<Sym>) -> bool {
    let mut available = true;
    guard.clone().modify(&mut |part| {
        if let smtlib::Exp::Var(sym) | smtlib::Exp::App(sym, _) = part {
            available &= sym.as_u32() < start || defined.contains(sym);
        }
    });
    available
}

/// 叶快照只交付入口检查点后的本段。没有读取序号的冻结叶仅接纳每个字段的一次读取。
fn transferable_error<B: BV>(
    task: &Task<B>,
    prefix: &Arc<Option<crate::smt::Trace<B>>>,
    ordered_reads: bool,
    start: u32,
) -> bool {
    let mut reads = HashSet::new();
    let trace = task.checkpoint.trace().as_ref().expect("错误叶必须有冻结前缀");
    if !Arc::ptr_eq(trace.path_cache_parts().2, prefix) {
        return false;
    }
    let count = trace.path_cache_parts().1.count();
    let mut defined = HashSet::new();
    let events: Vec<_> = trace.events_with_guards_rev().take(count).collect();
    let Some((_, Event::Fork(_, selector, _, _))) = task.fork_cond.as_ref() else { return false };
    // 失败点先定义 selector，再补寄存器写入，最后由快照附上从外到内的活动条件。
    let marker = events
        .iter()
        .skip_while(|(e, _)| matches!(e, Event::Smt(smtlib::Def::Assert(_), ..)))
        .skip_while(|(e, _)| matches!(e, Event::WriteReg(..)))
        .next();
    if !matches!(marker, Some((Event::Smt(smtlib::Def::DefineConst(sym, _), ..), _)) if sym == selector) {
        return false;
    }
    for (event, guard) in events.into_iter().rev() {
        if guard.is_some_and(|g| !guard_available(g, start, &defined)) {
            return false;
        }
        match event {
            Event::ReadReg(reg, field, _) if ordered_reads || !reads.insert((*reg, field)) => return false,
            Event::Smt(smtlib::Def::DefineEnum(..), ..) | Event::WriteMem { .. } => return false,
            _ => (),
        }
        defined.extend(event.defines());
    }
    true
}

/// 在 A 的 B 入口重新投影错误叶。A 更早产生的定义和可复用读取位置必须进入冻结前缀。
fn import_error<'ir, 'task, B: BV>(
    leaf: ErrorLeaf<'ir, B>,
    owner: crate::smt::LogicalArm,
    remap: &SymRemap,
    history_prefix: usize,
    state: &'task TaskState<B>,
    stop: Option<&'task StopConditions>,
    solver: &mut Solver<B>,
) -> Task<'ir, 'task, B> {
    let trace = leaf.checkpoint.trace().as_ref().unwrap();
    let local_events = trace.path_cache_parts().1.count();
    let events: Vec<_> = trace.events_with_guards_rev().take(local_events).collect();
    let condition_count =
        events.iter().take_while(|(e, _)| matches!(e, Event::Smt(smtlib::Def::Assert(_), ..))).count();
    let (conditions, body) = events.split_at(condition_count);
    let tx = solver.start_transaction();
    let (checkpoint, memory_guards) = solver.with_logical_arm(owner, |solver| {
        solver.import_arm_suffix(
            owner,
            body.iter().rev().map(|&(event, guard)| ArmSuffixEvent {
                guard: guard.map(|g| remap.exp(g)),
                event: remap.event(event),
                register_read_occurrence: matches!(event, Event::ReadReg(..)).then_some(0),
                cycle: matches!(event, Event::Cycle),
            }),
        );
        // 本层活动条件位于远端条件之前，均由同一快照入口按实际嵌套次序写出。
        let scopes: Vec<_> = conditions
            .iter()
            .rev()
            .map(|(event, _)| {
                let Event::Smt(smtlib::Def::Assert(guard), ..) = event else { unreachable!() };
                solver.start_transaction_with_guard(Some(remap.exp(guard)))
            })
            .collect();
        let result = solver.arm_error_snapshot(owner);
        for scope in scopes.into_iter().rev() {
            solver.rollback_transaction(scope);
        }
        result
    });
    solver.rollback_transaction(tx);
    let mut frame = unfreeze_frame(&leaf.frame);
    let (error, certified) = frame.arm_error.take().unwrap();
    frame.remap_symbols(remap, history_prefix);
    frame.arm_error = Some((error.remap_symbols(remap), certified));
    frame.arm_error_memory_guards = memory_guards.into();
    let mut frame = freeze_frame(&frame);
    frame.path_account = leaf.frame.path_account;
    Task {
        id: leaf.task,
        fraction: leaf.fraction,
        state,
        stop_conditions: stop,
        checkpoint,
        frame,
        fork_cond: Some((remap.def(&leaf.fork.0), remap.event(&leaf.fork.1))),
    }
}

/// A 提前结束或调试构建意外展开时唤醒等待者。真正的 panic 仍由线程作用域传播。
struct CancelOnDrop<'a, 'ir, B: BV> {
    cell: &'a ArmCell<'ir, B>,
    scheduler: Option<Scheduler<'a, 'ir, B>>,
    error: Option<ExecError>,
}

impl<B: BV> Drop for CancelOnDrop<'_, '_, B> {
    fn drop(&mut self) {
        if let Some(error) = self.error.take() {
            self.cell.cancel(error);
        }
        if let Some(scheduler) = self.scheduler {
            scheduler.queue.wake();
        }
    }
}

fn execute_job<'ir, B: BV>(
    work: QueuedArm<'ir, B>,
    tid: usize,
    scheduler: Option<Scheduler<'_, 'ir, B>>,
    state: &TaskState<B>,
    stop: Option<&StopConditions>,
    shared: &SharedState<'ir, B>,
) {
    let QueuedArm { job, cell, failure, .. } = work;
    let before_claim = region_arm::observe(state, "before_claim");
    if !cell.try_claim() {
        return;
    }
    let mut cleanup = CancelOnDrop { cell: &cell, scheduler, error: Some(failure) };

    let prior_smt = crate::smt::path_smt_stats();

    let result = before_claim.and_then(|()| {
        #[cfg(test)]
        cell.observe_id(state, "claim")?;
        region_arm::observe(state, "worker_claimed")?;
        let packet = run_b(job, tid, cell.cancelled.clone(), scheduler, stop, state, shared)?;
        region_arm::observe(state, "before_delivery")?;
        Ok(packet)
    });

    crate::smt::restore_path_smt_stats(prior_smt);
    let failed = result.is_err();
    cell.deliver(result);
    cleanup.error = None;
    drop(cleanup);
    region_arm::observe(state, if failed { "failed" } else { "delivered" }).expect("交付后观察点不可失败");
}

pub(super) fn with_worker<'ir, B: BV, T>(
    slot: Option<ThreadSlot<'_>>,
    scheduler: Option<Scheduler<'_, 'ir, B>>,
    state: &TaskState<B>,
    stop: Option<&StopConditions>,
    shared: &SharedState<'ir, B>,
    failure: ExecError,
    job: ArmJob<'ir, B>,
    local: impl FnOnce(Option<&ArmCell<'ir, B>>) -> Result<T, ExecError>,
) -> Result<T, ExecError> {
    let cell = Arc::new(JoinCell::new());
    let work =
        QueuedArm { job, cell: cell.clone(), failure: failure.clone(), parent_attempt: diagnostics::root_attempt() };
    std::thread::scope(|scope| {
        let cleanup = CancelOnDrop { cell: &cell, scheduler, error: Some(failure) };
        let available = if let Some(slot) = slot {
            std::thread::Builder::new()
                .spawn_scoped(scope, move || {
                    diagnostics::set_arm_parent(work.parent_attempt);
                    execute_job(work, slot.tid, scheduler, state, stop, shared);
                    drop(slot);
                })
                .is_ok()
        } else {
            scheduler.expect("等待线程来自当前任务").queue.enqueue(work);
            true
        };
        let result = local(available.then_some(cell.as_ref()));
        drop(cleanup);
        if let Some(scheduler) = scheduler {
            scheduler.queue.retire(&cell);
        }
        result
    })
}

pub(super) enum Received<'ir, B> {
    Retry,
    Dead,
    Arrived(LocalFrame<'ir, B>),
}

pub(super) fn receive<'ir, 'task, B: BV>(
    cell: &JoinCell<Delivery<'ir, B>>,
    initial_state: &Arc<LocalState<'ir, B>>,
    a: &[LocalFrame<'ir, B>],
    base: &mut LocalFrame<'ir, B>,
    state: &'task TaskState<B>,
    solver: &mut Solver<B>,
    sink: &(impl ForkSink<'ir, 'task, B> + ?Sized),
    tid: usize,
    stop: Option<&'task StopConditions>,
    shared: &SharedState<'ir, B>,
) -> Result<Received<'ir, B>, ExecError> {
    #[cfg(test)]
    cell.observe_id(state, "join")?;
    region_arm::observe(state, "a_join")?;
    if cell.try_reclaim() {
        region_arm::observe(state, "reclaimed")?;
        return Ok(Received::Retry);
    }

    // A 提升了初值或交付多个片段时，立即停止基于旧入口的 B，在本地从正确的入口重跑。
    if a.len() > 1 || !Arc::ptr_eq(initial_state, &base.local_state) {
        cell.cancel(reject(base, SpeculativeRejectReason::IncompatibleState));
        region_arm::observe(state, "serial_retry")?;
        return Ok(Received::Retry);
    }
    base.path_timing.pause_active();
    region_arm::observe(state, "waiting").expect("等待观察点不可失败");
    if let Some(scheduler) = sink.arm_scheduler() {
        scheduler.queue.help_until(
            cell,
            |work| {
                region_arm::observe(state, "helping").expect("帮助执行观察点不可失败");
                execute_job(work, tid, Some(scheduler), state, stop, shared);
            },
            state,
        );
    }
    let result = cell.take();
    if let Ok(Some(packet)) = &result {
        base.path_timing.include_parallel(packet.frame.path_timing.snapshot());
    }
    base.path_timing.start_active();
    let Some(mut packet) = result? else {
        region_arm::observe(state, "serial_retry")?;
        return Ok(Received::Retry);
    };
    let start = solver.next_join_symbol();
    let count = packet.symbols.end - packet.symbols.start;
    let end = start.checked_add(count).expect("区域臂编号溢出");
    let remap = if count != 0 && start != packet.symbols.start {
        let remap = region_arm::remap_region_arm_symbols(
            Sym::from_u32(start),
            vec![(packet.region.clone(), packet.arm.clone(), packet.symbols.clone().map(Sym::from_u32).collect())],
        );
        packet.remap_symbols(&remap, base.region_merge_records.len());
        remap
    } else {
        SymRemap::from_pairs([])
    };
    let parent = solver.current_logical_arm();
    let owner = solver.new_logical_arm(parent);
    solver.reserve_join_symbols(start, end);
    for leaf in packet.errors {
        region_arm::observe(state, "imported_error").expect("错误叶观察点不可失败");
        sink.submit_consumer_error(import_error(
            leaf,
            owner,
            &remap,
            base.region_merge_records.len(),
            state,
            stop,
            solver,
        ));
    }
    solver.import_arm_assertions(packet.deferred, &mut packet.suffix);
    solver.import_arm_suffix(owner, packet.suffix);
    if packet.dead {
        solver.discard_logical_arm_effects(owner);
        region_arm::observe(state, "imported")?;
        return Ok(Received::Dead);
    }
    packet.frame.region_execution.as_mut().unwrap().remote_cancel =
        base.region_execution.as_ref().unwrap().remote_cancel.clone();
    packet.frame.region_arm = Some(owner);
    packet.frame.path_timing = base.path_timing.clone();
    promote_initials(base, &packet.frame, solver);
    region_arm::observe(state, "imported")?;
    Ok(Received::Arrived(packet.frame))
}
