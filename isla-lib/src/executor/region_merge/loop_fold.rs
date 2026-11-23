//! 折叠时优先运行可退出的臂。CFG 只决定访问顺序，是否折叠由实际到达帧决定。
use super::*;

pub(super) fn back_edge_predecessors(cfg: &crate::ir::regions::RegionCfg, region: &Region) -> HashSet<usize> {
    let mut predecessors = HashMap::<usize, Vec<usize>>::new();
    for pc in region.nodes.iter().copied().chain([region.branch_pc]) {
        for (target, _) in cfg.successors(pc) {
            if let RegionPoint::Instruction(target) = target {
                predecessors.entry(target).or_default().push(pc);
            }
        }
    }
    let mut reaches = HashSet::new();
    let mut pending = vec![region.branch_pc];
    while let Some(pc) = pending.pop() {
        if reaches.insert(pc) {
            if let Some(previous) = predecessors.remove(&pc) {
                pending.extend(previous);
            }
        }
    }
    reaches
}

pub(super) fn compact_frontiers<'ir, B: BV>(
    exit_prefix: &mut [LocalFrame<'ir, B>],
    next: &mut LocalFrame<'ir, B>,
    exit_ids: &mut Option<HashSet<usize>>,
    base: &LocalFrame<'ir, B>,
    arm_start: usize,
    solver: &mut Solver<B>,
    info: SourceLoc,
) {
    for frame in exit_prefix.iter_mut().chain(std::iter::once(&mut *next)) {
        let access = frame.local_state.speculative_access.as_ref().unwrap();
        frame.region_merge_records.compact_loop_suffix(
            &base.region_merge_records,
            access.global_state || !access.ordered_events,
            solver,
            info,
        );
    }
    // append_loop_exit 只会继续折叠最后一组。
    *exit_ids = exit_prefix.last().map(|exit| {
        exit.region_merge_records.suffix(base.region_merge_records.len()).map(|record| record.record_id).collect()
    });
    let mut live: Vec<_> =
        exit_prefix.iter().chain([&*next]).map(|frame| frame.region_arm.expect("循环前沿必须属于逻辑臂")).collect();
    solver.compact_loop_arms(arm_start, &mut live);
    for (frame, id) in exit_prefix.iter_mut().chain(std::iter::once(&mut *next)).zip(live) {
        frame.region_arm = Some(id);
    }
}

#[cfg(test)]
pub(super) fn sample_frontiers<'ir, B: BV>(
    exit_prefix: &[LocalFrame<'ir, B>],
    next: &LocalFrame<'ir, B>,
    exit_ids: &Option<HashSet<usize>>,
    solver: &Solver<B>,
) {
    FOLD_SAMPLES.with_borrow_mut(|samples| {
        if let Some(samples) = samples {
            let frames = exit_prefix.iter().chain([next]);
            let (_, slots, reads) = MergeHistory::frontier_storage(frames.map(|f| &f.region_merge_records));
            samples.push([
                exit_prefix.len() + 1,
                slots,
                reads,
                exit_ids.as_ref().map_or(0, HashSet::len),
                solver.loop_arm_count(),
                solver.transaction_depth(),
                solver.loop_event_count(),
            ]);
        }
    });
}
