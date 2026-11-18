use super::*;
use crate::ir::regions::SlotProjection;
use smtlib::Exp::{And, Eq, Not, Var};

fn contains_poison<B: BV>(value: &Val<B>) -> bool {
    match value {
        Val::Poison => true,
        Val::Ctor(_, payload) => contains_poison(payload),
        Val::Struct(fields) | Val::SymbolicCtor(_, fields) => fields.values().any(contains_poison),
        Val::List(values) | Val::Vector(values) => values.iter().any(contains_poison),
        _ => false,
    }
}

/// 移除经结构判定为非活动、且下游保持标签检查的 Poison 候选。
/// 既有联合合并会从另一臂保留载荷，原标签仍参与 ITE。活动或无法证明的 Poison 继续由严格合并处理。
fn prune_inactive<B: BV>(
    value: &mut Val<B>,
    guard: &smtlib::Exp<Sym>,
    path: &mut Vec<SlotProjection>,
    solver: &Solver<B>,
    reads_guarded: &impl Fn(&[SlotProjection], Name) -> bool,
) {
    match value {
        Val::Ctor(ctor, payload) => {
            path.push(SlotProjection::Ctor(*ctor));
            prune_inactive(payload, guard, path, solver, reads_guarded);
            path.pop();
        }
        Val::SymbolicCtor(tag, payloads) => {
            payloads.retain(|ctor, payload| {
                if contains_poison(payload) {
                    let active = Eq(Box::new(Var(*tag)), Box::new(ctor.to_smt()));
                    if solver.structural_bool(&And(Box::new(guard.clone()), Box::new(active))) == Some(false)
                        && reads_guarded(path, *ctor)
                    {
                        return false;
                    }
                    path.push(SlotProjection::Ctor(*ctor));
                    prune_inactive(payload, guard, path, solver, reads_guarded);
                    path.pop();
                }
                true
            });
        }
        Val::Struct(fields) => {
            for (name, value) in fields {
                path.push(SlotProjection::Field(*name));
                prune_inactive(value, guard, path, solver, reads_guarded);
                path.pop();
            }
        }
        Val::Vector(values) | Val::List(values) => {
            for (index, value) in values.iter_mut().enumerate() {
                path.push(SlotProjection::Element(index));
                prune_inactive(value, guard, path, solver, reads_guarded);
                path.pop();
            }
        }
        _ => (),
    }
}

/// 仅使用当前帧的局部槽。让寄存器、全局槽及会逃逸的局部值沿用严格规则。
pub(super) fn prepare_local<'ir, B: BV>(
    a: &mut Option<UVal<'ir, B>>,
    b: &mut Option<UVal<'ir, B>>,
    condition: Sym,
    solver: &Solver<B>,
    reads_guarded: impl Fn(Option<(&[SlotProjection], Name)>) -> bool,
) -> Option<&'ir Ty<Name>> {
    match (a, b) {
        (Some(UVal::Init(_)), Some(UVal::Uninit(ty))) | (Some(UVal::Uninit(ty)), Some(UVal::Init(_))) => {
            reads_guarded(None).then_some(*ty)
        }
        (Some(UVal::Init(a)), Some(UVal::Init(b))) => {
            let guard = Var(condition);
            for (value, guard) in [(a, guard.clone()), (b, Not(Box::new(guard)))] {
                if contains_poison(value) {
                    prune_inactive(value, &guard, &mut Vec::new(), solver, &|path, ctor| {
                        reads_guarded(Some((path, ctor)))
                    });
                }
            }
            None
        }
        _ => None,
    }
}
