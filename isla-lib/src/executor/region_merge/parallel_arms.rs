//! A 独占主求解器。领取者只提交从入口重放所得的 B 臂数据。
use super::*;
use crate::executor::region_arm::{self, ArmPath, JoinCell, RegionId, RemoteArrival, ThreadSlot};
use crate::executor::region_summary::{constraint_binary, constraint_unary};

pub(super) type Entry<'a, B> = (ThreadSlot<'a>, Checkpoint<B>);

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

pub(super) fn entry<'a, 'ir, 'task, B: BV>(
    sink: &'a (impl ForkSink<'ir, 'task, B> + ?Sized),
    frame: &LocalFrame<'ir, B>,
    state: &TaskState<B>,
    region: &Region,
    solver: &mut Solver<B>,
) -> Option<Entry<'a, B>> {
    if !state.execution_limits.as_ref().is_some_and(ExecutionLimits::can_schedule_region_arm)
        || !region_arm::transferable_entry(frame)
        || solver.transaction_depth() != 0
        || region.has_back_edge
        || state.reverse_region_ready
        || state.region_step_budget().is_some()
    {
        return None;
    }
    let Some(slot) = sink.reserve_arm_thread() else {
        region_arm::observe(state, "no_slot").expect("名额观察点不可失败");
        return None;
    };
    Some((slot, region_arm::capture_arm_entry_checkpoint(solver)))
}

type Delivery<'ir, B> = Option<RemoteArrival<'ir, B>>;
pub(super) type ArmCell<'ir, B> = JoinCell<Delivery<'ir, B>>;

#[allow(clippy::too_many_arguments)]
pub(super) fn run_b<'ir, B: BV>(
    checkpoint: Checkpoint<B>,
    options: (crate::smt::SolverOptions, bool),
    cancelled: Arc<AtomicBool>,
    mut base: LocalFrame<'ir, B>,
    pc: usize,
    guard: smtlib::Exp<Sym>,
    tid: usize,
    task: TaskId,
    mut fraction: Fraction,
    timeout: PathTimeout,
    stop: Option<&StopConditions>,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    info: SourceLoc,
) -> Result<Delivery<'ir, B>, ExecError> {
    let memory_task = stats::memory_stats::enabled().then(|| stats::memory_stats::begin_task(task.as_usize()));
    let _ = &memory_task;
    base.path_timing.start_active();
    let mut config = Config::new();
    (config.solver_options, config.validation) = options;
    region_arm::observe(state, "context")?;
    let ctx = Context::new(config);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let start = solver.next_join_symbol();
    let root = solver.start_transaction();
    let mut errors = ArmErrorSink::new();
    let run = |solver: &mut Solver<B>| {
        let execution = base.region_execution.as_mut().unwrap();
        execution.remote_cancel = Some(cancelled.clone());
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
        let mut frame = branch_arm(&base, pc, guard, owner);
        let result = solver.with_logical_arm(owner, |solver| {
            advance_region_arm(
                tid,
                task,
                &mut fraction,
                timeout,
                stop,
                &errors,
                &mut frame,
                state,
                shared,
                solver,
                false,
                tx,
                info,
            )
        });
        match result {
            Ok(true) => (),
            // 不可移交的操作和局部拒绝交由 A 在真实串行前态上重跑。
            Err(ExecError::SpeculativeReject { .. }) | Ok(false) => return Ok(None),
            Err(e) => return Err(e),
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
        if !at_join
            || !returned_to_caller
            || !Arc::ptr_eq(&outer.region, &outer_region)
            || outer.pending_branch.is_some()
            || !frame.region_arrivals.is_empty()
            || frame.arm_error.is_some()
            || frame.pending_retry_operand.is_some()
            || frame.local_state.expression_retry_operands.is_some()
            || !errors.tasks.get_mut().unwrap().is_empty()
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
        frame.path_timing.pause_active();
        frame.region_execution.as_mut().unwrap().remote_cancel = None;
        Ok(Some(RemoteArrival {
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

/// A 提前结束或调试构建意外展开时唤醒等待者。真正的 panic 仍由线程作用域传播。
struct CancelOnDrop<'a, T> {
    cell: &'a JoinCell<T>,
    error: Option<ExecError>,
}

impl<T> Drop for CancelOnDrop<'_, T> {
    fn drop(&mut self) {
        if let Some(error) = self.error.take() {
            self.cell.cancel(error);
        }
    }
}

pub(super) fn with_worker<'ir, B: BV, T>(
    slot: ThreadSlot<'_>,
    state: &TaskState<B>,
    failure: ExecError,
    work: impl FnOnce(usize, Arc<AtomicBool>) -> Result<Delivery<'ir, B>, ExecError> + Send,
    local: impl FnOnce(Option<&JoinCell<Delivery<'ir, B>>>) -> Result<T, ExecError>,
) -> Result<T, ExecError> {
    let cell = JoinCell::new();
    std::thread::scope(|scope| {
        let delivery = &cell;
        let local_cleanup = CancelOnDrop { cell: &cell, error: Some(failure.clone()) };
        let parent_attempt = diagnostics::root_attempt();
        let child = std::thread::Builder::new().spawn_scoped(scope, move || {
            // 在认领前不建立 Context；A 可以在此窗口直接使用原来的 B 执行路径。
            let before_claim = region_arm::observe(state, "before_claim");
            if !delivery.try_claim() {
                return;
            }
            let mut cleanup = CancelOnDrop { cell: delivery, error: Some(failure) };
            let result = before_claim.and_then(|()| {
                diagnostics::set_arm_parent(parent_attempt);
                region_arm::observe(state, "worker_claimed")?;
                let packet = work(slot.tid, Arc::clone(&delivery.cancelled))?;
                region_arm::observe(state, "before_delivery")?;
                Ok(packet)
            });
            let failed = result.is_err();
            delivery.deliver(result);
            cleanup.error = None;
            drop(slot);
            region_arm::observe(state, if failed { "failed" } else { "delivered" }).expect("交付后观察点不可失败");
        });
        // OS 拒绝创建线程时，闭包随错误一并释放名额，A 仍能正常顺序执行。
        let result = local(child.is_ok().then_some(&cell));
        drop(local_cleanup);
        result
    })
}

pub(super) fn receive<'ir, B: BV>(
    cell: &JoinCell<Delivery<'ir, B>>,
    initial_state: &Arc<LocalState<'ir, B>>,
    a: &[LocalFrame<'ir, B>],
    base: &mut LocalFrame<'ir, B>,
    state: &TaskState<B>,
    solver: &mut Solver<B>,
) -> Result<Option<LocalFrame<'ir, B>>, ExecError> {
    region_arm::observe(state, "a_join")?;
    if cell.try_reclaim() {
        region_arm::observe(state, "reclaimed")?;
        return Ok(None);
    }

    // A 提升了初值或交付多个片段时，立即停止基于旧入口的 B，在本地从正确的入口重跑。
    if a.len() != 1 || !Arc::ptr_eq(initial_state, &base.local_state) {
        cell.cancel(reject(base, SpeculativeRejectReason::IncompatibleState));
        region_arm::observe(state, "serial_retry")?;
        return Ok(None);
    }
    base.path_timing.pause_active();
    region_arm::observe(state, "waiting").expect("等待观察点不可失败");
    let result = cell.take();
    if let Ok(Some(packet)) = &result {
        base.path_timing.include_parallel(packet.frame.path_timing.snapshot());
    }
    base.path_timing.start_active();
    let Some(mut packet) = result? else {
        region_arm::observe(state, "serial_retry")?;
        return Ok(None);
    };
    let start = solver.next_join_symbol();
    let count = packet.symbols.end - packet.symbols.start;
    let end = start.checked_add(count).expect("区域臂编号溢出");
    if count != 0 && start != packet.symbols.start {
        let remap = region_arm::remap_region_arm_symbols(
            Sym::from_u32(start),
            vec![(packet.region.clone(), packet.arm.clone(), packet.symbols.clone().map(Sym::from_u32).collect())],
        );
        packet.remap_symbols(&remap, base.region_merge_records.len());
    }
    let owner = solver.new_logical_arm(None);
    solver.reserve_join_symbols(start, end);
    solver.import_arm_assertions(packet.deferred, &mut packet.suffix);
    solver.import_arm_suffix(owner, &packet.suffix);
    packet.frame.region_arm = Some(owner);
    packet.frame.path_timing = base.path_timing.clone();
    promote_initials(base, &packet.frame, solver);
    region_arm::observe(state, "imported")?;
    Ok(Some(packet.frame))
}
