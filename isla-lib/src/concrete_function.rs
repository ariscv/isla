use std::collections::HashMap;
use std::str::FromStr;

use crate::ir::{Name, SharedState};
use crate::zencode;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathSegment {
    Exact(String),
    Wildcard,
    Globstar,
    Ctor { ctor_name: String, fun_name: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteFunctionSpec {
    pub path: Vec<PathSegment>,
    pub param_values: HashMap<String, Option<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteFunctionConfig {
    pub specs: Vec<ConcreteFunctionSpec>,
}

impl ConcreteFunctionSpec {
    /// Check if this spec matches the given call stack.
    ///
    /// `call_stack` is ordered from bottom (oldest/outermost) to top (current function).
    /// The rightmost path segment is anchored to the stack top, then earlier path segments
    /// are matched against progressively older callers. Any remaining ancestor frames after
    /// the path is fully consumed are allowed.
    pub fn matches<B>(&self, call_stack: &[Name], shared_state: &SharedState<'_, B>) -> bool {
        if self.path.is_empty() {
            return call_stack.is_empty();
        }
        match_segments(&self.path, call_stack, self.path.len(), call_stack.len(), shared_state)
    }
}

impl ConcreteFunctionConfig {
    /// Find the first spec that matches the given call stack.
    pub fn find_matching<B>(
        &self,
        call_stack: &[Name],
        shared_state: &SharedState<'_, B>,
    ) -> Option<&ConcreteFunctionSpec> {
        self.specs.iter().find(|spec| spec.matches(call_stack, shared_state))
    }
}

/// Recursive segment matcher with globstar backtracking.
///
/// `seg_idx` is an exclusive upper bound for the unmatched path prefix.
/// `stack_idx` is an exclusive upper bound for the unmatched stack prefix.
/// Matching proceeds right-to-left so the path suffix is anchored at the stack top.
fn match_segments<B>(
    path: &[PathSegment],
    call_stack: &[Name],
    seg_idx: usize,
    stack_idx: usize,
    shared_state: &SharedState<'_, B>,
) -> bool {
    if seg_idx == 0 {
        // All path segments consumed — remaining older ancestor frames are allowed.
        return true;
    }

    let seg = &path[seg_idx - 1];

    match seg {
        PathSegment::Exact(name) => {
            if stack_idx == 0 {
                return false;
            }
            let frame_name = call_stack[stack_idx - 1];
            let decoded = zencode::decode(shared_state.symtab.to_str(frame_name));
            if decoded != *name {
                return false;
            }
            match_segments(path, call_stack, seg_idx - 1, stack_idx - 1, shared_state)
        }
        PathSegment::Wildcard => {
            if stack_idx == 0 {
                return false;
            }
            match_segments(path, call_stack, seg_idx - 1, stack_idx - 1, shared_state)
        }
        PathSegment::Globstar => {
            // Globstar matches zero or more frames immediately below the already-matched suffix.
            for next_stack_idx in (0..=stack_idx).rev() {
                if match_segments(path, call_stack, seg_idx - 1, next_stack_idx, shared_state) {
                    return true;
                }
            }
            false
        }
        PathSegment::Ctor { ctor_name, fun_name } => {
            if stack_idx == 0 {
                return false;
            }
            let frame_name = call_stack[stack_idx - 1];
            let decoded = zencode::decode(shared_state.symtab.to_str(frame_name));
            if decoded != *fun_name {
                return false;
            }
            // Check that this function is a ctor of the named union
            if !is_ctor_of(shared_state, frame_name, ctor_name) {
                return false;
            }
            match_segments(path, call_stack, seg_idx - 1, stack_idx - 1, shared_state)
        }
    }
}

/// Check whether `fun_name` is a constructor of the union whose decoded name is `ctor_name`.
fn is_ctor_of<B>(shared_state: &SharedState<'_, B>, fun_name: Name, ctor_name: &str) -> bool {
    for (union_name, ctors) in &shared_state.type_info.unions {
        let decoded_union = zencode::decode(shared_state.symtab.to_str(*union_name));
        if decoded_union != ctor_name {
            continue;
        }
        if ctors.iter().any(|(ctor_name, _)| *ctor_name == fun_name) {
            return true;
        }
    }
    false
}

impl FromStr for ConcreteFunctionSpec {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        if s.is_empty() {
            return Err("concrete function spec cannot be empty".to_string());
        }

        let (path_part, params_part) = if let Some(open_idx) = s.rfind('(') {
            if !s.ends_with(')') {
                return Err("parameter list must end with ')'".to_string());
            }
            if s[..open_idx].contains('(') || s[..open_idx].contains(')') {
                return Err("path must not contain parentheses".to_string());
            }
            (&s[..open_idx], &s[open_idx + 1..s.len() - 1])
        } else {
            (s, "")
        };

        let path = parse_path(path_part)?;
        let param_values = parse_params(params_part)?;

        Ok(ConcreteFunctionSpec { path, param_values })
    }
}

fn parse_path(path: &str) -> Result<Vec<PathSegment>, String> {
    let path = path.trim();
    if path.is_empty() {
        return Err("concrete function path cannot be empty".to_string());
    }

    path.split("->")
        .map(|segment| {
            let segment = segment.trim();
            if segment.is_empty() {
                return Err("concrete function path contains an empty segment".to_string());
            }

            if segment == "*" {
                Ok(PathSegment::Wildcard)
            } else if segment == "**" {
                Ok(PathSegment::Globstar)
            } else if segment.contains("::") {
                let mut parts = segment.split("::");
                let ctor_name = parts.next().unwrap_or("").trim();
                let fun_name = parts.next().unwrap_or("").trim();
                if ctor_name.is_empty() || fun_name.is_empty() || parts.next().is_some() {
                    return Err(format!("invalid constructor path segment: {}", segment));
                }
                Ok(PathSegment::Ctor { ctor_name: ctor_name.to_string(), fun_name: fun_name.to_string() })
            } else {
                Ok(PathSegment::Exact(segment.to_string()))
            }
        })
        .collect()
}

fn parse_params(params: &str) -> Result<HashMap<String, Option<String>>, String> {
    let params = params.trim();
    if params.is_empty() {
        return Ok(HashMap::new());
    }

    let mut values = HashMap::new();
    for param in params.split(',') {
        let param = param.trim();
        if param.is_empty() {
            return Err("parameter list contains an empty entry".to_string());
        }

        let mut parts = param.splitn(2, '=');
        let name = parts.next().unwrap_or("").trim();
        if name.is_empty() {
            return Err("parameter name cannot be empty".to_string());
        }

        let value = parts
            .next()
            .map(|value| {
                let value = value.trim();
                if value.is_empty() {
                    Err("parameter value cannot be empty".to_string())
                } else {
                    Ok(value.to_string())
                }
            })
            .transpose()?;

        if values.insert(name.to_string(), value).is_some() {
            return Err(format!("duplicate parameter name: {}", name));
        }
    }

    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};
    use std::str::FromStr;

    use crate::ir::{IRTypeInfo, Name, SharedState, Symtab, Ty};
    use crate::zencode;

    fn exact(name: &str) -> PathSegment {
        PathSegment::Exact(name.to_string())
    }

    // --- Parsing tests ---

    #[test]
    fn parses_simple_exact_with_value() {
        let spec = ConcreteFunctionSpec::from_str("zADD(imm=5)").unwrap();
        assert_eq!(spec.path, vec![exact("zADD")]);
        assert_eq!(spec.param_values.get("imm"), Some(&Some("5".to_string())));
    }

    #[test]
    fn parses_simple_exact_without_value() {
        let spec = ConcreteFunctionSpec::from_str("zADD(imm)").unwrap();
        assert_eq!(spec.path, vec![exact("zADD")]);
        assert_eq!(spec.param_values.get("imm"), Some(&None));
    }

    #[test]
    fn parses_call_chain() {
        let spec = ConcreteFunctionSpec::from_str("zEXECUTE->zADD->zplus(imm=5,rs=1)").unwrap();
        assert_eq!(spec.path, vec![exact("zEXECUTE"), exact("zADD"), exact("zplus")]);
        assert_eq!(spec.param_values.get("imm"), Some(&Some("5".to_string())));
        assert_eq!(spec.param_values.get("rs"), Some(&Some("1".to_string())));
    }

    #[test]
    fn parses_ctor_path_segment() {
        let spec = ConcreteFunctionSpec::from_str("CtorA::funA->B->C(a,b=2,c)").unwrap();
        assert_eq!(
            spec.path,
            vec![
                PathSegment::Ctor { ctor_name: "CtorA".to_string(), fun_name: "funA".to_string() },
                exact("B"),
                exact("C"),
            ]
        );
        assert_eq!(spec.param_values.get("a"), Some(&None));
        assert_eq!(spec.param_values.get("b"), Some(&Some("2".to_string())));
        assert_eq!(spec.param_values.get("c"), Some(&None));
    }

    #[test]
    fn parses_wildcard_and_globstar() {
        let wildcard = ConcreteFunctionSpec::from_str("A->*->C(a=1)").unwrap();
        assert_eq!(wildcard.path, vec![exact("A"), PathSegment::Wildcard, exact("C")]);
        assert_eq!(wildcard.param_values.get("a"), Some(&Some("1".to_string())));

        let globstar = ConcreteFunctionSpec::from_str("A->**->C(a=1)").unwrap();
        assert_eq!(globstar.path, vec![exact("A"), PathSegment::Globstar, exact("C")]);
        assert_eq!(globstar.param_values.get("a"), Some(&Some("1".to_string())));
    }

    #[test]
    fn parses_ctor_in_middle_of_path() {
        let spec = ConcreteFunctionSpec::from_str("A->B::b->C()").unwrap();
        assert_eq!(
            spec.path,
            vec![exact("A"), PathSegment::Ctor { ctor_name: "B".to_string(), fun_name: "b".to_string() }, exact("C"),]
        );
        assert!(spec.param_values.is_empty());
    }

    #[test]
    fn rejects_invalid_formats() {
        for input in ["", "()", "A->", "->A", "A->B::->C()", "A->B::b::c->C()", "A->B(a=)", "A(a=1"] {
            assert!(ConcreteFunctionSpec::from_str(input).is_err(), "{input}");
        }
    }

    // --- Matching tests ---
    //
    // We build a minimal SharedState with a symtab containing known names
    // and a type_info with known unions for Ctor matching.

    struct TestFixture {
        names: Vec<Name>,
        shared_state: SharedState<'static, ()>,
    }

    static EMPTY_FILES: &[String] = &[];

    impl TestFixture {
        fn new(symbol_strs: &[&str]) -> Self {
            let encoded: Vec<String> = symbol_strs.iter().map(|s| zencode::encode(s)).collect();
            let encoded: &'static [String] = encoded.leak();
            let symtab = Symtab::from_raw_table(encoded, EMPTY_FILES);
            let names: Vec<Name> = (0..symbol_strs.len()).map(|i| Name::from_u32(i as u32)).collect();

            let type_info = IRTypeInfo {
                structs: HashMap::new(),
                enums: HashMap::new(),
                enum_members: HashMap::new(),
                unions: HashMap::new(),
                union_ctors: HashSet::new(),
            };

            let shared_state = SharedState {
                functions: HashMap::new(),
                externs: HashMap::new(),
                symtab,
                type_info,
                registers: HashMap::new(),
                probes: HashSet::new(),
                probe_functions: HashSet::new(),
                trace_functions: HashSet::new(),
                reset_registers: Vec::new(),
                reset_constraints: Vec::new(),
                function_assumptions: Vec::new(),
            };

            TestFixture { names, shared_state }
        }

        fn name(&self, symbol: &str) -> Name {
            let encoded = zencode::encode(symbol);
            for &name in &self.names {
                if self.shared_state.symtab.to_str(name) == encoded {
                    return name;
                }
            }
            panic!("symbol {symbol} not found in test fixture");
        }

        fn add_union(&mut self, union_name: &str, ctors: &[&str]) {
            let union_n = self.name(union_name);
            let ctor_names: Vec<(Name, Ty<Name>)> = ctors.iter().map(|&c| (self.name(c), Ty::Unit)).collect();
            for &(cn, _) in &ctor_names {
                self.shared_state.type_info.union_ctors.insert(cn);
            }
            self.shared_state.type_info.unions.insert(union_n, ctor_names);
        }
    }

    #[test]
    fn exact_match_single() {
        let fx = TestFixture::new(&["zADD", "zSUB", "zMUL"]);
        let spec = ConcreteFunctionSpec::from_str("zADD").unwrap();
        let stack = vec![fx.name("zADD")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_no_match_single() {
        let fx = TestFixture::new(&["zADD", "zSUB"]);
        let spec = ConcreteFunctionSpec::from_str("zADD").unwrap();
        let stack = vec![fx.name("zSUB")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_chain_match() {
        let fx = TestFixture::new(&["zEXECUTE", "zADD", "zSUB"]);
        let spec = ConcreteFunctionSpec::from_str("zEXECUTE->zADD").unwrap();
        let stack = vec![fx.name("zEXECUTE"), fx.name("zADD")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_chain_no_match_too_short() {
        let fx = TestFixture::new(&["zADD"]);
        let spec = ConcreteFunctionSpec::from_str("zEXECUTE->zADD").unwrap();
        let stack = vec![fx.name("zADD")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_chain_match_with_ancestors() {
        let fx = TestFixture::new(&["zA", "zB", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->zB").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zB"), fx.name("zC")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_single_match_with_ancestors() {
        let fx = TestFixture::new(&["zEXECUTE", "zADD"]);
        let spec = ConcreteFunctionSpec::from_str("zADD").unwrap();
        let stack = vec![fx.name("zEXECUTE"), fx.name("zADD")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn exact_single_no_match_below_stack_top() {
        let fx = TestFixture::new(&["zADD", "zOTHER"]);
        let spec = ConcreteFunctionSpec::from_str("zADD").unwrap();
        let stack = vec![fx.name("zADD"), fx.name("zOTHER")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn wildcard_match() {
        let fx = TestFixture::new(&["zA", "zB", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->*->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zB"), fx.name("zC")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn wildcard_no_match_wrong_endpoints() {
        let fx = TestFixture::new(&["zA", "zB", "zD"]);
        let spec = ConcreteFunctionSpec::from_str("zA->*->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zB"), fx.name("zD")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn wildcard_no_match_too_short() {
        let fx = TestFixture::new(&["zA", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->*->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zC")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_zero() {
        let fx = TestFixture::new(&["zA", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->**->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zC")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_one() {
        let fx = TestFixture::new(&["zA", "zB", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->**->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zB"), fx.name("zC")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_many() {
        let fx = TestFixture::new(&["zA", "zX", "zY", "zZ", "zC"]);
        let spec = ConcreteFunctionSpec::from_str("zA->**->zC").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zX"), fx.name("zY"), fx.name("zZ"), fx.name("zC")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_many_with_ancestors() {
        let fx = TestFixture::new(&["X", "A", "Y", "Z", "C"]);
        let spec = ConcreteFunctionSpec::from_str("A->**->C").unwrap();
        let stack = vec![fx.name("X"), fx.name("A"), fx.name("Y"), fx.name("Z"), fx.name("C")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_zero_new_anchor_case() {
        let fx = TestFixture::new(&["A", "C"]);
        let spec = ConcreteFunctionSpec::from_str("A->**->C").unwrap();
        let stack = vec![fx.name("A"), fx.name("C")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn wildcard_no_match_multiple_frames_between_endpoints() {
        let fx = TestFixture::new(&["X", "A", "Y", "Z", "C"]);
        let spec = ConcreteFunctionSpec::from_str("A->*->C").unwrap();
        let stack = vec![fx.name("X"), fx.name("A"), fx.name("Y"), fx.name("Z"), fx.name("C")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn globstar_match_only_globstar() {
        let fx = TestFixture::new(&["zA", "zB"]);
        let spec = ConcreteFunctionSpec { path: vec![PathSegment::Globstar], param_values: HashMap::new() };
        assert!(spec.matches(&[], &fx.shared_state));
        assert!(spec.matches(&[fx.name("zA")], &fx.shared_state));
        assert!(spec.matches(&[fx.name("zA"), fx.name("zB")], &fx.shared_state));
    }

    #[test]
    fn globstar_between_exact() {
        let fx = TestFixture::new(&["zA", "zX", "zY", "zB"]);
        let spec = ConcreteFunctionSpec::from_str("zA->**->zB").unwrap();
        let stack = vec![fx.name("zA"), fx.name("zX"), fx.name("zY"), fx.name("zB")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn ctor_match_success() {
        let mut fx = TestFixture::new(&["MyUnion", "myctor", "zTOP"]);
        fx.add_union("MyUnion", &["myctor"]);
        let spec = ConcreteFunctionSpec::from_str("MyUnion::myctor->zTOP").unwrap();
        let stack = vec![fx.name("myctor"), fx.name("zTOP")];
        assert!(spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn ctor_no_match_wrong_fun() {
        let mut fx = TestFixture::new(&["MyUnion", "myctor", "otherfun", "zTOP"]);
        fx.add_union("MyUnion", &["myctor"]);
        let spec = ConcreteFunctionSpec::from_str("MyUnion::myctor->zTOP").unwrap();
        let stack = vec![fx.name("otherfun"), fx.name("zTOP")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn ctor_no_match_wrong_union() {
        let mut fx = TestFixture::new(&["OtherUnion", "MyUnion", "myctor", "zTOP"]);
        fx.add_union("OtherUnion", &["myctor"]);
        let spec = ConcreteFunctionSpec::from_str("MyUnion::myctor->zTOP").unwrap();
        let stack = vec![fx.name("myctor"), fx.name("zTOP")];
        assert!(!spec.matches(&stack, &fx.shared_state));
    }

    #[test]
    fn find_matching_returns_first() {
        let fx = TestFixture::new(&["zA", "zB", "zC"]);
        let config = ConcreteFunctionConfig {
            specs: vec![
                ConcreteFunctionSpec::from_str("zA->zX").unwrap(),
                ConcreteFunctionSpec::from_str("zA->zB").unwrap(),
                ConcreteFunctionSpec::from_str("zA->zB").unwrap(),
            ],
        };
        let stack = vec![fx.name("zA"), fx.name("zB")];
        let found = config.find_matching(&stack, &fx.shared_state).unwrap();
        assert_eq!(found.path, vec![exact("zA"), exact("zB")]);
    }

    #[test]
    fn find_matching_none() {
        let fx = TestFixture::new(&["zA", "zB"]);
        let config = ConcreteFunctionConfig { specs: vec![ConcreteFunctionSpec::from_str("zX->zY").unwrap()] };
        let stack = vec![fx.name("zA"), fx.name("zB")];
        assert!(config.find_matching(&stack, &fx.shared_state).is_none());
    }

    #[test]
    fn empty_path_matches_empty_stack() {
        let fx = TestFixture::new(&["zA"]);
        let spec = ConcreteFunctionSpec { path: vec![], param_values: HashMap::new() };
        assert!(spec.matches(&[], &fx.shared_state));
        assert!(!spec.matches(&[fx.name("zA")], &fx.shared_state));
    }
}
