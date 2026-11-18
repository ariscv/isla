//! 失败汇合点按稳定的逻辑臂顺序尝试兼容组。
use super::*;

type Frame<'ir, B> = LocalFrame<'ir, B>;

/// 只以所有片段都含有的活跃具体字符串槽分桶。
/// 两个不同的具体字符串在现有值合并中一定失败，等值合并也不会改变其签名。
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
    let slots = string_slots(&arrivals, base, region);
    let mut buckets = HashMap::<Vec<String>, Vec<usize>>::new();
    let mut groups: Vec<(Frame<'ir, B>, bool)> = Vec::new();
    for arrival in arrivals {
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
        let candidates = buckets.entry(signature).or_default();
        let mut combined = false;
        for &index in candidates.iter() {
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
            candidates.push(groups.len());
            groups.push((arrival, false));
        }
    }
    Ok(groups)
}
