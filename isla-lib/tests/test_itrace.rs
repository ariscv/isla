/*
这个文件是 itrace IR 文本缓存的回归测试。

itrace 会从 .ir 文件中按函数缓存函数体里的非空 IR 行，之后执行器记录到的 pc
会被当作这个缓存向量的下标，用来把每条执行过的指令还原成对应的 IR 文本行。
因此这里用 fixtures/ir_cache_assumption.ir 构造 SharedState，并同时用一个独立的
文本扫描器取出 fixture 中的函数体行，验证两件事：

1. SharedState 解析出的指令数量必须和缓存到的函数体行数一致；
2. 每个 pc 对应的 Instr 类型和左值，必须落在 fixture 中预期的那一行上。

如果 IR 解析器、fixture 格式或 itrace 缓存规则发生变化，导致“pc == 函数体 IR 行
下标”这个假设失效，这些测试会先失败，避免 itrace 输出错误的 IR 行。
*/

use std::collections::HashMap;

use isla_lib::bitvector::b64::B64;
use isla_lib::ir::{self, IRTypeInfo, Instr, Loc, Name, SharedState, Symtab};
use isla_lib::ir_lexer;
use isla_lib::ir_parser;
use std::collections::HashSet;

const IR_FIXTURE: &str = include_str!("fixtures/ir_cache_assumption.ir");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InstrTag {
    Decl,
    Init,
    Copy,
    Call,
    End,
}

fn parse_shared_state_from_fixture() -> SharedState<'static, B64> {
    let mut symtab = Symtab::new();
    let defs: Vec<ir::Def<Name, B64>> =
        ir_parser::IrParser::new().parse(&mut symtab, ir_lexer::new_ir_lexer(IR_FIXTURE)).expect("IR parse failed");
    let defs: &'static [ir::Def<Name, B64>] = Box::leak(defs.into_boxed_slice());
    let type_info = IRTypeInfo::new(defs);

    SharedState::new(
        symtab,
        defs,
        type_info,
        HashSet::new(),
        HashSet::new(),
        HashSet::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )
}

fn strip_source_loc(line: &str) -> String {
    let trimmed = line.trim_end_matches(|c: char| c == ';' || c.is_whitespace()).trim_end();
    if let Some(pos) = trimmed.rfind('`') {
        let suffix = trimmed[pos + 1..].trim();
        if looks_like_source_loc_suffix(suffix) {
            return trimmed[..pos].trim_end().to_string();
        }
    }

    trimmed.to_string()
}

fn looks_like_source_loc_suffix(value: &str) -> bool {
    if value.chars().all(|c| c.is_ascii_digit()) {
        return !value.is_empty();
    }

    let mut segments = value.split_whitespace();
    let file = segments.next();
    let range = segments.next();
    if segments.next().is_some() {
        return false;
    }

    let (Some(file), Some(range)) = (file, range) else {
        return false;
    };

    if !file.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }

    let mut line_chars = range.splitn(2, ':');
    let line1 = line_chars.next();
    let positions = line_chars.next();
    if line_chars.next().is_some() {
        return false;
    }

    if !line1.is_some_and(|v| v.chars().all(|c| c.is_ascii_digit())) {
        return false;
    }

    let mut pos_parts = positions.unwrap_or_default().splitn(2, '-');
    let char1 = pos_parts.next();
    let tail = pos_parts.next();
    if pos_parts.next().is_some() {
        return false;
    }

    if !char1.is_some_and(|v| v.chars().all(|c| c.is_ascii_digit())) {
        return false;
    }

    let mut end_parts = tail.unwrap_or_default().split(':');
    let end_line = end_parts.next();
    let end_char = end_parts.next();
    if end_parts.next().is_some() {
        return false;
    }

    end_line.is_some_and(|line| line.chars().all(|c| c.is_ascii_digit()))
        && end_char.is_some_and(|col| col.chars().all(|c| c.is_ascii_digit()))
}

fn function_bodies(ir_text: &str) -> HashMap<String, Vec<String>> {
    let mut function_bodies = HashMap::new();
    let mut current_function: Option<String> = None;
    let mut current_lines = Vec::new();

    for line in ir_text.lines() {
        let trimmed = line.trim();

        if let Some(name) = &current_function {
            if trimmed == "}" {
                function_bodies.insert(name.clone(), current_lines.clone());
                current_function = None;
                current_lines.clear();
                continue;
            }

            let cleaned = strip_source_loc(line);
            if !cleaned.trim().is_empty() {
                current_lines.push(cleaned);
            }

            if trimmed == "end;" {
                function_bodies.insert(name.clone(), current_lines.clone());
                current_function = None;
                current_lines.clear();
            }
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("fn ") {
            let mut head = rest.split_whitespace().next().expect("function declaration should include name");
            if let Some((name, _)) = head.split_once('(') {
                head = name;
            }
            let func_name = head;
            if func_name != "" {
                current_function = Some(func_name.to_string());
            }
        }
    }

    function_bodies
}

fn expected_instructions() -> HashMap<&'static str, Vec<(InstrTag, &'static str)>> {
    HashMap::from([
        (
            "zcache_ok",
            vec![
                (InstrTag::Decl, "z0"),
                (InstrTag::Decl, "z1"),
                (InstrTag::Call, "z1"),
                (InstrTag::Copy, "return"),
                (InstrTag::End, "end"),
            ],
        ),
        (
            "zpc_lookup",
            vec![
                (InstrTag::Decl, "p0"),
                (InstrTag::Decl, "p1"),
                (InstrTag::Decl, "p2"),
                (InstrTag::Call, "p1"),
                (InstrTag::Copy, "return"),
                (InstrTag::End, "end"),
            ],
        ),
    ])
}

fn instruction_tag(instr: &Instr<Name, B64>) -> InstrTag {
    match instr {
        Instr::Decl(_, _, _) => InstrTag::Decl,
        Instr::Init(_, _, _, _) => InstrTag::Init,
        Instr::Copy(_, _, _) => InstrTag::Copy,
        Instr::Call(_, _, _, _, _) => InstrTag::Call,
        Instr::End => InstrTag::End,
        _ => panic!("fixture contains unsupported instruction kind"),
    }
}

fn instr_lhs(shared_state: &SharedState<'_, B64>, instr: &Instr<Name, B64>) -> String {
    match instr {
        Instr::Decl(name, _, _) | Instr::Init(name, _, _, _) => shared_state.symtab.to_str(*name).to_string(),
        Instr::Copy(Loc::Id(name), _, _) | Instr::Call(Loc::Id(name), _, _, _, _) => {
            shared_state.symtab.to_str(*name).to_string()
        }
        Instr::End => "end".to_string(),
        _ => panic!("fixture contains unsupported instruction kind"),
    }
}

#[test]
fn ir_cache_assumption() {
    let shared_state = parse_shared_state_from_fixture();
    let body_map = function_bodies(IR_FIXTURE);

    for (name, expected_lines) in expected_instructions() {
        let fn_id = shared_state.symtab.lookup(name);
        let (_, _, instrs) = shared_state
            .functions
            .get(&fn_id)
            .unwrap_or_else(|| panic!("shared_state missing function in fixture: {name}"));

        let body_lines =
            body_map.get(name).unwrap_or_else(|| panic!("fixture parser missing function body lines: {name}"));

        assert_eq!(instrs.len(), body_lines.len(), "IR 行数与函数 {name} 指令数不一致");
        assert_eq!(instrs.len(), expected_lines.len(), "fixture assumptions 与函数 {name} 指令数不一致");
    }
}

#[test]
fn ir_line_lookup() {
    let shared_state = parse_shared_state_from_fixture();
    let body_map = function_bodies(IR_FIXTURE);
    let expected = expected_instructions();

    for (name, expected_lines) in expected {
        let fn_id = shared_state.symtab.lookup(name);
        let (_, _, instrs) = shared_state
            .functions
            .get(&fn_id)
            .unwrap_or_else(|| panic!("shared_state missing function in fixture: {name}"));
        let body_lines =
            body_map.get(name).unwrap_or_else(|| panic!("fixture parser missing function body lines: {name}"));

        assert_eq!(instrs.len(), expected_lines.len(), "fixture expectations 与函数 {name} 指令数不一致");
        assert_eq!(body_lines.len(), expected_lines.len(), "fixture body 行数与函数 {name} 期望不一致");

        for pc in 0..instrs.len() {
            let instr = &instrs[pc];
            let &(expected_tag, expected_prefix) = &expected_lines[pc];
            let source_line = body_lines[pc].trim();

            assert_eq!(instruction_tag(instr), expected_tag, "{name} 的第 {pc} 条指令类型映射异常");
            assert_eq!(instr_lhs(&shared_state, instr), expected_prefix, "{name} 的第 {pc} 条指令 lhs 与预期不匹配");
            assert!(
                source_line.starts_with(expected_prefix),
                "{name} 的第 {pc} 条指令未能定位到预期 IR 行：{source_line}"
            );
        }
    }
}
