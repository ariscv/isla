//! 失败汇合点按稳定的逻辑臂顺序尝试兼容组。
use super::*;

type Frame<'ir, B> = LocalFrame<'ir, B>;

/// 显式关闭具体值合并时，按所有片段都含有的活跃字符串槽分桶。
/// 严格合并要求字符串相等，合并后签名不变。
fn string_slots<B: BV>(arrivals: &[Frame<B>], base: &Frame<B>, region: &Region) -> Vec<(bool, Name)> {
    let mut keys = Vec::new();
    for (lets, slots) in [(false, arrivals[0].vars()), (true, arrivals[0].lets())] {
        for (&name, value) in slots {
            if !matches!(value, UVal::Init(Val::String(_)))
                || (!lets && region.local_variables.contains(&name) && !base.vars().contains_key(&name))
            {
                continue;
            }
            if arrivals.iter().all(|frame| {
                let slots = if lets { frame.lets() } else { frame.vars() };
                matches!(slots.get(&name), Some(UVal::Init(Val::String(_))))
            }) {
                keys.push((lets, name));
            }
        }
    }
    keys.sort_unstable();
    keys
}

#[allow(clippy::too_many_arguments)]
pub(super) fn merge_compatible<'ir, B: BV>(
    arrivals: Vec<Frame<'ir, B>>,
    base: &Frame<'ir, B>,
    region: &Region,
    state: &TaskState<B>,
    shared: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Vec<(Frame<'ir, B>, bool)>, ExecError> {
    let slots = (!state.execution_limits.as_ref().is_some_and(|limits| limits.merge_concrete_values))
        .then(|| string_slots(&arrivals, base, region))
        .filter(|slots| !slots.is_empty());
    let mut buckets = HashMap::<Vec<String>, Vec<usize>>::new();
    let mut groups: Vec<(Frame<'ir, B>, bool)> = Vec::new();
    for arrival in arrivals {
        let candidates = slots.as_ref().map(|slots| {
            let signature = slots
                .iter()
                .map(|&(lets, name)| {
                    let values = if lets { arrival.lets() } else { arrival.vars() };
                    let UVal::Init(Val::String(value)) = &values[&name] else {
                        unreachable!("字符串分桶槽必须存在")
                    };
                    value.clone()
                })
                .collect();
            buckets.entry(signature).or_default()
        });
        let mut combined = false;
        let candidate_count = candidates.as_ref().map_or(groups.len(), |indices| indices.len());
        for candidate in 0..candidate_count {
            let index = candidates.as_ref().map_or(candidate, |indices| indices[candidate]);
            let tx = solver.start_transaction();
            let trial = fold_exit_frontiers(
                groups[index].0.clone(),
                arrival.clone(),
                base,
                region,
                state,
                shared,
                solver,
                info,
            );
            match trial {
                Ok(frame) => {
                    solver.commit_transaction();
                    groups[index] = (frame, true);
                    combined = true;
                    break;
                }
                Err(error) => {
                    solver.rollback_transaction(tx);
                    if !matches!(&error, ExecError::SpeculativeReject { reason, .. } if is_join_rejection(*reason)) {
                        return Err(error);
                    }
                }
            }
        }
        if !combined {
            if let Some(indices) = candidates {
                indices.push(groups.len());
            }
            groups.push((arrival, false));
        }
    }
    Ok(groups)
}
