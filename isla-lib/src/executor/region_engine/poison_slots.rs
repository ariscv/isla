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
    solver: &dyn crate::primop_util::merge_terms::MergeTerms<B>,
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
                    let tag_matches = Eq(Box::new(Var(*tag)), Box::new(ctor.to_smt()));
                    let active = And(Box::new(guard.clone()), Box::new(tag_matches));
                    if solver.structural_bool(&active) == Some(false) && reads_guarded(path, *ctor) {
                        return false;
                    }
                    path.push(SlotProjection::Ctor(*ctor));
                    prune_inactive(payload, &active, path, solver, reads_guarded);
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

/// 未初始化联合的新鲜标签可以取任一构造子。仅在旧内容不可读时保留原未初始化槽。
pub(super) fn dead_uninit_union<'ir, B: BV>(
    a: Option<&UVal<'ir, B>>,
    b: Option<&UVal<'ir, B>>,
    unread: impl FnOnce() -> bool,
) -> Option<&'ir Ty<Name>> {
    match (a, b) {
        (Some(UVal::Uninit(ty @ Ty::Union(_))), Some(UVal::Init(_)))
        | (Some(UVal::Init(_)), Some(UVal::Uninit(ty @ Ty::Union(_)))) => unread().then_some(*ty),
        _ => None,
    }
}

/// 仅使用当前帧的局部槽。可正常初始化的槽位继续保留带守卫的值。
pub(super) fn prepare_local<'slot, 'ir, B: BV>(
    a: &mut Option<Cow<'slot, UVal<'ir, B>>>,
    b: &mut Option<Cow<'slot, UVal<'ir, B>>>,
    uninit_is_poison: bool,
    condition: Sym,
    solver: &dyn crate::primop_util::merge_terms::MergeTerms<B>,
    reads_guarded: impl Fn(Option<(&[SlotProjection], Name)>) -> bool,
) -> Option<&'ir Ty<Name>> {
    match (a.as_deref(), b.as_deref()) {
        (Some(UVal::Init(value)), Some(UVal::Uninit(ty))) | (Some(UVal::Uninit(ty)), Some(UVal::Init(value)))
            if uninit_is_poison && !matches!(value, Val::Poison) =>
        {
            reads_guarded(None).then_some(*ty)
        }
        (Some(UVal::Init(_)), Some(UVal::Init(_))) => {
            let guard = Var(condition);
            for (slot, guard) in [(a, guard.clone()), (b, Not(Box::new(guard)))] {
                let slot = slot.as_mut().unwrap();
                if matches!(slot.as_ref(), UVal::Init(value) if contains_poison(value)) {
                    let UVal::Init(value) = slot.to_mut() else { unreachable!() };
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::{Config, Context};
    use smtlib::Exp::Ite;

    #[test]
    fn region_merge_poison_slots_nested_constructor_activation() {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let loc = SourceLoc::unknown();
        let branch = Var(solver.declare_const(smtlib::Ty::Bool, loc));
        let wrapper_active = Var(solver.declare_const(smtlib::Ty::Bool, loc));
        let [wrapper, other, field, ok, err] = [90, 91, 92, 93, 94].map(Name::from_u32);
        let tag = |guard, yes: Name, no: Name| Ite(Box::new(guard), Box::new(yes.to_smt()), Box::new(no.to_smt()));
        let outer_tag = solver.define_const(tag(wrapper_active.clone(), wrapper, other), loc);
        for (when_active, when_inactive) in [(err, ok), (ok, err)] {
            let inner_tag = solver.define_const(tag(wrapper_active.clone(), when_active, when_inactive), loc);
            let inner = Val::SymbolicCtor(inner_tag, [(ok, Val::Poison), (err, Val::Unit)].into_iter().collect());
            let payloads = [(wrapper, Val::Struct([(field, inner)].into_iter().collect())), (other, Val::Unit)];
            let mut value = Val::SymbolicCtor(outer_tag, payloads.into_iter().collect());
            prune_inactive(&mut value, &branch, &mut Vec::new(), &solver, &|path, ctor| {
                path == [SlotProjection::Ctor(wrapper), SlotProjection::Field(field)] && ctor == ok
            });
            let Val::SymbolicCtor(_, outer) = value else { unreachable!() };
            let Val::Struct(fields) = &outer[&wrapper] else { unreachable!() };
            let Val::SymbolicCtor(_, inner) = &fields[&field] else { unreachable!() };
            assert_eq!(inner.contains_key(&ok), when_active == ok);
            assert_eq!(inner[&err], Val::Unit);
        }
    }
}
