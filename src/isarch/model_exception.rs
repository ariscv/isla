//! 通用 Sail 异常终态策略：只匹配配置给出的构造子，不推断模型或消息含义。
use isla_lib::{
    bitvector::BV,
    ir::{SharedState, Val},
    zencode,
};

/// 返回用于审计的“构造子＋载荷”键；原始消息中的源码位置完整保留。
pub(super) fn filtered_site<B: BV>(names: &[String], exception: &Val<B>, shared: &SharedState<B>) -> Option<String> {
    if names.is_empty() {
        return None;
    }
    let Val::Ctor(ctor, payload) = exception else {
        return None;
    };
    let constructor = zencode::decode(shared.symtab.to_str_demangled(*ctor));
    names.iter().any(|name| name == &constructor).then(|| format!("{constructor}: {}", payload.to_str(shared)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::{bitvector::b64::B64, ir::Symtab};

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
