//! 通用 Sail 异常终态策略：只匹配配置给出的构造子，不推断模型或消息含义。
use crate::{
    bitvector::BV,
    ir::{Name, SharedState, Symtab, Val},
    zencode,
};

pub(super) fn filtered_constructor(names: &[String], ctor: Name, symtab: &Symtab) -> Option<String> {
    if names.is_empty() {
        return None;
    }
    let constructor = zencode::decode(symtab.to_str_demangled(ctor));
    names.iter().any(|name| name == &constructor).then_some(constructor)
}

pub(super) fn filtered_exception<'a, B: BV>(
    names: &[String],
    exception: &'a Val<B>,
    symtab: &Symtab,
) -> Option<(String, &'a Val<B>)> {
    let Val::Ctor(ctor, payload) = exception else { return None };
    filtered_constructor(names, *ctor, symtab).map(|constructor| (constructor, payload.as_ref()))
}

/// 返回用于审计的“构造子＋载荷”键；原始消息中的源码位置完整保留。
pub fn filtered_site<B: BV>(names: &[String], exception: &Val<B>, shared: &SharedState<B>) -> Option<String> {
    let (constructor, payload) = filtered_exception(names, exception, &shared.symtab)?;
    Some(format!("{constructor}: {}", payload.to_str(shared)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    #[test]
    fn matches_exact_constructor_and_preserves_message_without_model_special_cases() {
        let mut symtab = Symtab::new();
        let encoded = zencode::encode("Generic_error");
        let ctor = symtab.intern(&encoded);
        let shared = SharedState::<B64>::empty(symtab);
        let value = Val::Ctor(ctor, Box::new(Val::String("generic.sail:19: failure".into())));
        assert!(filtered_site(&[], &value, &shared).is_none());
        assert!(filtered_site(&["Generic".into()], &value, &shared).is_none());
        assert!(filtered_site(&["Generic_error".into()], &Val::Poison, &shared).is_none());
        assert_eq!(
            filtered_site(&["Generic_error".into()], &value, &shared),
            Some("Generic_error: \"generic.sail:19: failure\"".into())
        );
    }
}

pub(super) fn discard<B: BV>(
    frame: &super::LocalFrame<B>,
    names: &[String],
    shared: &SharedState<B>,
    location: crate::source_loc::SourceLoc,
) -> bool {
    let Some((exception, _)) = frame.get_exception() else { return false };
    let Some((constructor, payload)) = filtered_exception(names, exception, &shared.symtab) else { return false };
    let in_region = frame.region_execution.is_some();
    shared.execution_stats.filtered_model_exception(in_region);
    super::stats::merge_diagnostics::filtered_model_exception(frame, shared, location, &constructor, payload);
    true
}
