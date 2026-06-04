use crate::bitvector::BV;
use crate::ir::Instr::{Arbitrary, End};
use crate::ir::{BitsSegment, Instr, Name, SharedState, Symtab, Val};
use crate::smt::{EnumId, EnumMember, Sym};
use crate::zencode;
use ahash;

#[macro_export]
macro_rules! d {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {}", file!(), line!(), stringify!($val), $val);
        )*
    };
}
#[macro_export]
macro_rules! d1 {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {:?}", file!(), line!(), stringify!($val), $val);
        )*
    };
}

#[macro_export]
macro_rules! d2 {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {:#?}", file!(), line!(), stringify!($val), $val);
        )*
    };
}

#[macro_export]
macro_rules! d3 {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {:#?}", file!(), line!(), stringify!($val), $val);
        )*
		use std::process::exit;
		exit(0);
    };
}

// 用法：warning!("format string", arg1, arg2, ...);
#[macro_export]
macro_rules! dWarning {
    ($($arg:tt)*) => {
        println!("\x1b[33mWarning:\x1b[0m {}", format_args!($($arg)*))
    };
}

#[allow(dead_code)]
pub mod colors {
    pub const RESET: &str = "\x1b[0m";
    pub const RED: &str = "\x1b[31m";
    pub const GREEN: &str = "\x1b[32m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const BLUE: &str = "\x1b[34m";
    pub const MAGENTA: &str = "\x1b[35m";
    pub const CYAN: &str = "\x1b[36m";
    pub const WHITE: &str = "\x1b[37m";
    pub const BRIGHT_RED: &str = "\x1b[91m";
    pub const BRIGHT_GREEN: &str = "\x1b[92m";
    pub const BRIGHT_YELLOW: &str = "\x1b[93m";
    pub const BRIGHT_BLUE: &str = "\x1b[94m";
    pub const BRIGHT_MAGENTA: &str = "\x1b[95m";
    pub const BRIGHT_CYAN: &str = "\x1b[96m";

    // 背景色
    pub const BG_BLACK: &str = "\x1b[40m";
    pub const BG_RED: &str = "\x1b[41m";
    pub const BG_GREEN: &str = "\x1b[42m";
    pub const BG_YELLOW: &str = "\x1b[43m";
    pub const BG_BLUE: &str = "\x1b[44m";
    pub const BG_MAGENTA: &str = "\x1b[45m";
    pub const BG_CYAN: &str = "\x1b[46m";
    pub const BG_WHITE: &str = "\x1b[47m";
}
/// 日志宏：带颜色和位置信息的调试输出
///
/// # 用法
/// - `dlog!("format", args...)` - 使用默认蓝色
/// - `dlog!(colors::RED, "format", args...)` - 使用自定义颜色
#[macro_export]
macro_rules! dlog {
    // 内部实现分支：颜色 + 格式化字符串 + 参数
    (@impl $color:expr, $fmt:literal $($arg:tt)*) => {{
        let file = file!();
        let line = line!();
        let column = column!();

        let function_name = {
            fn __f() {}
            std::any::type_name_of_val(&__f)
                .trim_end_matches("::__f")
                .trim_end_matches("::{{closure}}")
                .rsplit_once("::")
                .map(|(_, name)| name)
                .unwrap_or("unknown")
        };

        eprintln!("{}[{}:{}:{} {}]: {} {}",
            $color,
            file,
            line,
            column,
            function_name,
            format_args!($fmt $($arg)*),
            $crate::dprint::colors::RESET,
        );
    }};

    // 带自定义颜色的版本: dlog(colors::COLOR, "format", args...)
    ($color:expr, $fmt:literal $($arg:tt)*) => {
        $crate::dlog!(@impl $color, $fmt $($arg)*)
    };

    // 默认蓝色版本: dlog("format", args...)
    ($fmt:literal $($arg:tt)*) => {
        $crate::dlog!(@impl $crate::dprint::colors::BLUE, $fmt $($arg)*)
    };
}

use std::fmt::Write;
use std::str::FromStr;
use Instr::*;

/// 解码字符串中的所有 zencoded 部分
fn decode_recursive(input: &str) -> String {
    // 首先尝试对整个字符串解码
    if let Ok(decoded) = zencode::try_decode(input) {
        // 解码成功后，继续处理解码结果中可能存在的其他编码部分
        // 但要避免无限递归：只处理一次后跳到下面的逻辑
        let mut result = decoded.clone();
        let mut changed = true;

        // 最多迭代几次以处理嵌套的编码（避免无限循环）
        for _ in 0..5 {
            if !changed {
                break;
            }
            changed = false;

            // 在结果中查找可能的编码部分
            let mut temp_result = String::new();
            let mut last_end = 0;

            let mut i = 0;
            while i < result.len() {
                let c = result.chars().nth(i).unwrap();
                if c == 'z' {
                    // 检查这是否是编码字符串的开始
                    let prev_char = if i > 0 { result[..i].chars().last() } else { None };

                    let is_boundary = prev_char.map_or(true, |c| !c.is_alphanumeric() && c != '_');

                    if is_boundary {
                        // 尝试从这个位置解码
                        let remaining = &result[i..];
                        let encode_end =
                            remaining.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(remaining.len());

                        let encoded_part = &remaining[..encode_end];
                        if let Ok(decoded_part) = zencode::try_decode(encoded_part) {
                            temp_result.push_str(&result[last_end..i]);
                            temp_result.push_str(&decoded_part);
                            last_end = i + encode_end;
                            i = last_end;
                            changed = true;
                            continue;
                        }
                    }
                }
                i += 1;
            }

            if last_end < result.len() {
                temp_result.push_str(&result[last_end..]);
            }

            if !temp_result.is_empty() && temp_result != result {
                result = temp_result;
            }
        }

        return result;
    }

    // 如果整个字符串不能解码，尝试查找其中的编码部分
    let mut result = String::new();
    let mut last_end = 0;
    let mut i = 0;

    while i < input.len() {
        let c = input.chars().nth(i).unwrap();
        if c == 'z' {
            // 检查这是否是编码字符串的开始
            let prev_char = if i > 0 { input[..i].chars().last() } else { None };

            let is_boundary = prev_char.map_or(true, |c| !c.is_alphanumeric() && c != '_');

            if is_boundary {
                // 尝试从这个位置解码
                let remaining = &input[i..];
                let encode_end = remaining.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(remaining.len());

                let encoded_part = &remaining[..encode_end];
                if let Ok(decoded) = zencode::try_decode(encoded_part) {
                    result.push_str(&input[last_end..i]);
                    result.push_str(&decoded);
                    last_end = i + encode_end;
                    i = last_end;
                    continue;
                }
            }
        }
        i += 1;
    }

    if last_end < input.len() {
        result.push_str(&input[last_end..]);
    } else if result.is_empty() {
        // 如果没有进行任何解码，返回原始字符串
        result = input.to_string();
    }

    result
}
impl Name {
    pub fn to_str<B: BV>(&self, shared_state: &SharedState<B>) -> String {
        String::from_str(shared_state.symtab.to_str(**&self)).unwrap_or_else(|e| panic!("cannot get str of Name:{}", e))
    }
}
impl<B: BV> Val<B> {
    /// 单行格式化（紧凑，无缩进换行）
    pub fn to_str(&self, shared_state: &SharedState<B>) -> String {
        self.to_str_internal(shared_state, 0, false)
    }

    /// 多行格式化（带缩进换行）
    pub fn to_str_fmt(&self, shared_state: &SharedState<B>) -> String {
        self.to_str_internal(shared_state, 0, true)
    }

    /// 核心实现函数
    /// indent: 缩进层级
    /// multi_line: 是否多行格式化（true=带换行缩进，false=单行紧凑）
    fn to_str_internal(&self, shared_state: &SharedState<B>, indent: usize, multi_line: bool) -> String {
        let indent_str = "  ".repeat(indent);
        match self {
            Val::Symbolic(sym) => format!("{}Sym({})", indent_str, sym),
            Val::I64(n) => format!("{}{}i64", indent_str, n),
            Val::I128(n) => format!("{}{}i128", indent_str, n),
            Val::Bool(b) => format!("{}{}", indent_str, b),
            Val::Bits(bv) => format!("{}{}", indent_str, bv),
            Val::MixedBits(segments) => {
                let parts: Vec<String> = segments
                    .iter()
                    .map(|seg| match seg {
                        BitsSegment::Symbolic(s) => format!("Sym({})", s),
                        BitsSegment::Concrete(b) => format!("{}", b),
                    })
                    .collect();
                format!("{}[{}]", indent_str, parts.join(", "))
            }
            Val::String(s) => format!("{}\"{}\"", indent_str, s),
            Val::Unit => format!("{}()", indent_str),
            Val::Vector(vec) => {
                if vec.is_empty() {
                    format!("{}[]", indent_str)
                } else if !multi_line {
                    let elems: Vec<String> =
                        vec.iter().map(|v| v.to_str_internal(shared_state, indent, false)).collect();
                    format!("{}[{}]", indent_str, elems.join(", "))
                } else {
                    let mut result = format!("{}[\n", indent_str);
                    for elem in vec {
                        result.push_str(&elem.to_str_internal(shared_state, indent + 1, true));
                        result.push_str(",\n");
                    }
                    result.push_str(&indent_str);
                    result.push(']');
                    result
                }
            }
            Val::List(vec) => {
                if vec.is_empty() {
                    format!("{}List[]", indent_str)
                } else if !multi_line {
                    let elems: Vec<String> =
                        vec.iter().map(|v| v.to_str_internal(shared_state, indent, false)).collect();
                    format!("{}List[{}]", indent_str, elems.join(", "))
                } else {
                    let mut result = format!("{}List[\n", indent_str);
                    for elem in vec {
                        result.push_str(&elem.to_str_internal(shared_state, indent + 1, true));
                        result.push_str(",\n");
                    }
                    result.push_str(&indent_str);
                    result.push(']');
                    result
                }
            }
            Val::Enum(member) => {
                let enum_name = decode_recursive(shared_state.symtab.to_str(member.enum_id.to_name()));
                // 获取枚举成员名称
                let member_name = member.to_name(shared_state).to_str(shared_state);
                /* let member_name = shared_state
                .type_info
                .enums
                .get(&member.enum_id.to_name())
                .and_then(|members| members.iter().nth(member.member))
                .map(|name| shared_state.symtab.to_str(*name).to_string())
                .unwrap_or_else(|| format!("<member {}>", member.member)); */
                format!("{}{}::{}(EnumMember.member:{})", indent_str, enum_name, member_name, member.member)
            }
            Val::Struct(fields) => {
                if fields.is_empty() {
                    format!("{}{{}}", indent_str)
                } else if !multi_line {
                    let field_strs: Vec<String> = fields
                        .iter()
                        .map(|(name, val)| {
                            let name_decoded = decode_recursive(shared_state.symtab.to_str(*name));
                            format!("{}: {}", name_decoded, val.to_str_internal(shared_state, indent, false))
                        })
                        .collect();
                    format!("{{{}}}", field_strs.join(", "))
                } else {
                    let mut result = format!("{}{{\n", indent_str);
                    for (name, val) in fields {
                        let name_decoded = decode_recursive(shared_state.symtab.to_str(*name));
                        result.push_str(&format!("{}  {}: ", indent_str, name_decoded));
                        // 对于单行值，不额外缩进
                        match val {
                            Val::Symbolic(_)
                            | Val::I64(_)
                            | Val::I128(_)
                            | Val::Bool(_)
                            | Val::Bits(_)
                            | Val::Unit
                            | Val::Enum(_)
                            | Val::Ref(_)
                            | Val::Poison
                            | Val::String(_)
                            | Val::MixedBits(_) => {
                                result.push_str(&val.to_str_internal(shared_state, 0, false));
                            }
                            _ => {
                                result.push_str(&val.to_str_internal(shared_state, indent + 2, true));
                            }
                        }
                        result.push_str(",\n");
                    }
                    result.push_str(&indent_str);
                    result.push('}');
                    result
                }
            }
            Val::Ctor(name, val) => {
                let name_str = decode_recursive(shared_state.symtab.to_str(*name));
                if !multi_line {
                    format!("{}{}({})", indent_str, name_str, val.to_str_internal(shared_state, indent, false))
                } else {
                    match val.as_ref() {
                        Val::Symbolic(_)
                        | Val::I64(_)
                        | Val::I128(_)
                        | Val::Bool(_)
                        | Val::Bits(_)
                        | Val::Unit
                        | Val::Enum(_)
                        | Val::Ref(_)
                        | Val::Poison
                        | Val::String(_)
                        | Val::MixedBits(_) => {
                            format!("{}{}({})", indent_str, name_str, val.to_str_internal(shared_state, 0, false))
                        }
                        _ => {
                            format!(
                                "{}{}(\n{}\n{})",
                                indent_str,
                                name_str,
                                val.to_str_internal(shared_state, indent + 1, true),
                                indent_str
                            )
                        }
                    }
                }
            }
            Val::SymbolicCtor(sym, fields) => {
                if fields.is_empty() {
                    format!("{}SymCtor({{}})", indent_str)
                } else if !multi_line {
                    let field_strs: Vec<String> = fields
                        .iter()
                        .map(|(name, val)| {
                            let name_decoded = decode_recursive(shared_state.symtab.to_str(*name));
                            format!("{}: {}", name_decoded, val.to_str_internal(shared_state, indent, false))
                        })
                        .collect();
                    format!("{}SymCtor({}, {{{}}})", indent_str, sym, field_strs.join(", "))
                } else {
                    let mut result = format!("{}SymCtor({}, {{\n", indent_str, sym);
                    for (name, val) in fields {
                        let name_decoded = decode_recursive(shared_state.symtab.to_str(*name));
                        result.push_str(&format!("{}  {}: ", indent_str, name_decoded));
                        match val {
                            Val::Symbolic(_)
                            | Val::I64(_)
                            | Val::I128(_)
                            | Val::Bool(_)
                            | Val::Bits(_)
                            | Val::Unit
                            | Val::Enum(_)
                            | Val::Ref(_)
                            | Val::Poison
                            | Val::String(_)
                            | Val::MixedBits(_) => {
                                result.push_str(&val.to_str_internal(shared_state, 0, false));
                            }
                            _ => {
                                result.push_str(&val.to_str_internal(shared_state, indent + 2, true));
                            }
                        }
                        result.push_str(",\n");
                    }
                    result.push_str(&indent_str);
                    result.push_str("})");
                    result
                }
            }
            Val::Ref(name) => {
                let name_decoded = decode_recursive(shared_state.symtab.to_str(*name));
                format!("{}&{}", indent_str, name_decoded)
            }
            Val::Poison => format!("{}<poison>", indent_str),
        }
    }

    ///输出类型信息
    pub fn type_string(&self) -> String {
        use Val::*;
        match self {
            Symbolic(_) => "Symbolic".to_string(),
            I64(_) => "I64".to_string(),
            I128(_) => "I128".to_string(),
            Bool(_) => "Bool".to_string(),
            Bits(_) => "Bits".to_string(),
            MixedBits(_) => "MixedBits".to_string(),
            String(_) => "String".to_string(),
            Enum(_) => "Enum".to_string(),
            Unit => "Unit".to_string(),
            List(_) => "List".to_string(),
            Vector(_) => "Vector".to_string(),
            Struct(_) => "Struct".to_string(),
            Ctor(_, _) => "Ctor".to_string(),
            SymbolicCtor(_, _) => "SymbolicCtor".to_string(),
            Ref(_) => "Ref".to_string(),
            Poison => "Poison".to_string(),
        }
    }

    pub fn from_str(s: &str, shared_state: &SharedState<B>) -> Result<Self, String> {
        let s = s.trim();
        let chars: Vec<char> = s.chars().collect();

        // Symbolic: Sym(name)
        if s.starts_with("Sym(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1];
            let id = inner.parse::<u32>().map_err(|_| format!("无效的Sym ID: {}", inner))?;
            return Ok(Val::Symbolic(Sym::from_u32(id)));
        }

        // I64: 构造函数格式 "I64(42)"
        if s.starts_with("I64(") && s.ends_with(')') {
            let inner = &s[4..s.len() - 1];
            let n = inner.parse::<i64>().map_err(|_| format!("无效的I64格式: {}", inner))?;
            return Ok(Val::I64(n));
        }

        // I128: 构造函数格式 "I128(123)"
        if s.starts_with("I128(") && s.ends_with(')') {
            let inner = &s[5..s.len() - 1];
            let n = inner.parse::<i128>().map_err(|_| format!("无效的I128格式: {}", inner))?;
            return Ok(Val::I128(n));
        }

        // I64: 字面量格式 "42i64" (to_str 的输出格式)
        if s.ends_with("i64") {
            let num_str = &s[..s.len() - 3];
            let n = num_str.parse::<i64>().map_err(|_| format!("无法解析的Val格式: {}", s))?;
            return Ok(Val::I64(n));
        }

        // I128: 字面量格式 "42i128" (to_str 的输出格式)
        if s.ends_with("i128") {
            let num_str = &s[..s.len() - 4];
            let n = num_str.parse::<i128>().map_err(|_| format!("无法解析的Val格式: {}", s))?;
            return Ok(Val::I128(n));
        }

        // Bool: 支持两种格式 "true"/"false" 和 "Bool(true)"/"Bool(false)"
        if s == "true" {
            return Ok(Val::Bool(true));
        }
        if s == "false" {
            return Ok(Val::Bool(false));
        }
        if s == "Bool(true)" {
            return Ok(Val::Bool(true));
        }
        if s == "Bool(false)" {
            return Ok(Val::Bool(false));
        }

        // Unit: 支持 "()" 和 "Unit"
        if s == "()" {
            return Ok(Val::Unit);
        }
        if s == "Unit" {
            return Ok(Val::Unit);
        }

        // Poison
        if s == "<poison>" || s == "Poison" {
            return Ok(Val::Poison);
        }

        // String: 简单格式 "\"...\""
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            let inner = &s[1..s.len() - 1];
            return Ok(Val::String(inner.to_string()));
        }

        // Ref: &name
        if s.starts_with('&') {
            let name_str = &s[1..];
            let name = shared_state.symtab.get(name_str).ok_or_else(|| format!("未知的引用名称: {}", name_str))?;
            return Ok(Val::Ref(name));
        }

        // Vector: 简单格式 "[...]"
        if s.starts_with('[') {
            if s == "[]" {
                return Ok(Val::Vector(vec![]));
            }
            // 解析向量内容
            let inner = &s[1..s.len() - 1];
            let mut vals = Vec::new();
            let mut current = String::new();
            let mut depth = 0;
            for c in inner.chars() {
                match c {
                    '[' | '{' => {
                        depth += 1;
                        current.push(c);
                    }
                    ']' | '}' => {
                        depth -= 1;
                        current.push(c);
                    }
                    ',' if depth == 0 => {
                        if !current.trim().is_empty() {
                            vals.push(Val::from_str(current.trim(), shared_state)?);
                        }
                        current = String::new();
                    }
                    _ => {
                        current.push(c);
                    }
                }
            }
            if !current.trim().is_empty() {
                vals.push(Val::from_str(current.trim(), shared_state)?);
            }
            return Ok(Val::Vector(vals));
        }

        // List: 简单格式 "List[...]"
        if s.starts_with("List[") {
            if s == "List[]" {
                return Ok(Val::List(vec![]));
            }
            let inner = &s[5..s.len() - 1];
            let mut vals = Vec::new();
            let mut current = String::new();
            let mut depth = 0;
            for c in inner.chars() {
                match c {
                    '[' | '{' => {
                        depth += 1;
                        current.push(c);
                    }
                    ']' | '}' => {
                        depth -= 1;
                        current.push(c);
                    }
                    ',' if depth == 0 => {
                        if !current.trim().is_empty() {
                            vals.push(Val::from_str(current.trim(), shared_state)?);
                        }
                        current = String::new();
                    }
                    _ => {
                        current.push(c);
                    }
                }
            }
            if !current.trim().is_empty() {
                vals.push(Val::from_str(current.trim(), shared_state)?);
            }
            return Ok(Val::List(vals));
        }

        // Struct: {...}
        if s.starts_with('{') && s.ends_with('}') {
            if s == "{}" {
                return Ok(Val::Struct(ahash::HashMap::default()));
            }
            let inner = &s[1..s.len() - 1];
            let mut fields: ahash::HashMap<Name, Val<B>> = ahash::HashMap::default();
            let mut current = String::new();
            let mut depth = 0;
            for c in inner.chars() {
                match c {
                    '[' | '{' => {
                        depth += 1;
                        current.push(c);
                    }
                    ']' | '}' => {
                        depth -= 1;
                        current.push(c);
                    }
                    ',' if depth == 0 => {
                        if !current.trim().is_empty() {
                            // 解析 "name: value" 格式
                            let parts: Vec<&str> = current.trim().splitn(2, ": ").collect();
                            if parts.len() == 2 {
                                let name = shared_state
                                    .symtab
                                    .get(parts[0].trim())
                                    .ok_or_else(|| format!("未知的结构体字段名: {}", parts[0]))?;
                                let val = Val::from_str(parts[1].trim(), shared_state)?;
                                fields.insert(name, val);
                            }
                        }
                        current = String::new();
                    }
                    _ => {
                        current.push(c);
                    }
                }
            }
            if !current.trim().is_empty() {
                let parts: Vec<&str> = current.trim().splitn(2, ": ").collect();
                if parts.len() == 2 {
                    let name = shared_state
                        .symtab
                        .get(parts[0].trim())
                        .ok_or_else(|| format!("未知的结构体字段名: {}", parts[0]))?;
                    let val = Val::from_str(parts[1].trim(), shared_state)?;
                    fields.insert(name, val);
                }
            }
            return Ok(Val::Struct(fields));
        }

        // Ctor: Name(value) 或 Name(value) 多行格式
        if let Some(paren_pos) = s.find('(') {
            if s.ends_with(')') {
                let name_str = &s[..paren_pos];
                let inner = &s[paren_pos + 1..s.len() - 1];
                let name =
                    shared_state.symtab.get(name_str).ok_or_else(|| format!("未知的构造函数名: {}", name_str))?;
                let val = Box::new(Val::from_str(inner.trim(), shared_state)?);
                return Ok(Val::Ctor(name, val));
            }
        }

        // Enum: EnumName::MemberName(EnumMember.member:N)
        if let Some(double_colon_pos) = s.find("::") {
            if let Some(paren_pos) = s.find('(') {
                let _enum_name = &s[..double_colon_pos];
                let member_part = &s[double_colon_pos + 2..paren_pos];
                let inner = &s[paren_pos + 1..s.len() - 1]; // EnumMember.member:N

                // 解析 EnumMember.member:N
                if let Some(dot_pos) = inner.rfind('.') {
                    let enum_id_name = &inner[..dot_pos];
                    let member_index =
                        inner[dot_pos + 1..].parse::<usize>().map_err(|_| format!("无效的枚举成员索引: {}", inner))?;

                    // 从 symtab 获取 enum_id (Name)，然后转换为 EnumId
                    let enum_name = shared_state
                        .symtab
                        .get(enum_id_name)
                        .ok_or_else(|| format!("未知的枚举ID: {}", enum_id_name))?;
                    let enum_id = EnumId::from_name(enum_name);

                    return Ok(Val::Enum(EnumMember { enum_id, member: member_index }));
                }
            }
        }

        // SymCtor: SymCtor(Sym, {...})
        if s.starts_with("SymCtor(") {
            let inner = &s[8..s.len() - 1]; // 去掉 SymCtor( 和 )
                                            // 解析 Sym, {...}
            if let Some(comma_pos) = inner.find(", {") {
                let sym_str = &inner[..comma_pos];
                let fields_str = &inner[comma_pos + 2..]; // 去掉 ", {"
                let fields_str = &fields_str[..fields_str.len() - 1]; // 去掉 }

                // 解析 Sym(id)
                let sym_inner = sym_str
                    .trim()
                    .strip_prefix("Sym(")
                    .and_then(|s| s.strip_suffix(')'))
                    .ok_or_else(|| format!("无效的Sym格式: {}", sym_str))?;
                let id = sym_inner.parse::<u32>().map_err(|_| format!("无效的Sym ID: {}", sym_inner))?;
                let sym = Sym::from_u32(id);

                let fields: ahash::HashMap<Name, Val<B>> = if fields_str.trim().is_empty() {
                    ahash::HashMap::default()
                } else {
                    // 解析字段 {key: val, ...}
                    let mut field_map: ahash::HashMap<Name, Val<B>> = ahash::HashMap::default();
                    let mut current = String::new();
                    let mut depth = 0;
                    for c in fields_str.chars() {
                        match c {
                            '[' | '{' => {
                                depth += 1;
                                current.push(c);
                            }
                            ']' | '}' => {
                                depth -= 1;
                                current.push(c);
                            }
                            ',' if depth == 0 => {
                                if !current.trim().is_empty() {
                                    let parts: Vec<&str> = current.trim().splitn(2, ": ").collect();
                                    if parts.len() == 2 {
                                        let name = shared_state
                                            .symtab
                                            .get(parts[0].trim())
                                            .ok_or_else(|| format!("未知的SymCtor字段名: {}", parts[0]))?;
                                        let val = Val::from_str(parts[1].trim(), shared_state)?;
                                        field_map.insert(name, val);
                                    }
                                }
                                current = String::new();
                            }
                            _ => {
                                current.push(c);
                            }
                        }
                    }
                    if !current.trim().is_empty() {
                        let parts: Vec<&str> = current.trim().splitn(2, ": ").collect();
                        if parts.len() == 2 {
                            let name = shared_state
                                .symtab
                                .get(parts[0].trim())
                                .ok_or_else(|| format!("未知的SymCtor字段名: {}", parts[0]))?;
                            let val = Val::from_str(parts[1].trim(), shared_state)?;
                            field_map.insert(name, val);
                        }
                    }
                    field_map
                };

                return Ok(Val::SymbolicCtor(sym, fields));
            }
        }

        // Bits - 位向量解析
        // 注意：由于 BV trait 没有 from_str_radix，这里只做基本的格式识别
        // 实际的位向量解析需要具体的 BV 类型实现
        if s.starts_with("0x") || s.starts_with("0b") {
            // 暂时跳过位向量解析，返回错误
            return Err(format!("位向量解析需要具体的BV类型支持: {}", s));
        }

        // MixedBits: [Sym(...), 123, ...]
        // 这个需要更复杂的解析，暂时跳过

        Err(format!("无法解析的Val格式: {}", s))
    }
}

pub fn print_instr_toString<'a, B>(f: &'a mut String, instr: &'a Instr<Name, B>, symtab: &Symtab) -> &'a mut String {
    macro_rules! s {
        ($id:expr) => {
            symtab.to_str_demangled($id)
        };
    }

    let res = match instr {
        Decl(id, ty, info) => write!(f, "Decl {} : {:?} ` {:?}", s!(*id), ty, info),
        Init(id, ty, exp, info) => write!(f, "Init {} : {:?} = {:?} ` {:?}", s!(*id), ty, exp, info),
        Jump(exp, target, info) => write!(f, "jump {:?} to {:?} ` {:?}", exp, target, info),
        Goto(target) => write!(f, "goto {:?}", target),
        Copy(loc, exp, info) => write!(f, "Copy {:?} = {:?} ` {:?}", loc, exp, info),
        Monomorphize(id, ty, info) => write!(f, "mono {} : {:?} ` {:?}", s!(*id), ty, info),
        Call(loc, ext, id, args, info) => write!(f, "Call {:?} = {}<{:?}>({:?}) ` {:?}", loc, s!(*id), ext, args, info),
        Exit(cause, info) => write!(f, "exit {:?} ` {:?}", cause, info),
        Arbitrary => write!(f, "arbitrary"),
        End => write!(f, "end"),
        PrimopUnary(loc, fptr, exp, info) => write!(f, "PrimopUnary {:?} = {:p}({:?}) ` {:?}", loc, fptr, exp, info),
        PrimopBinary(loc, fptr, lhs, rhs, info) => {
            write!(f, "PrimopBinary {:?} = {:p}({:?}, {:?}) ` {:?}", loc, fptr, lhs, rhs, info)
        }
        PrimopReset(loc, reset, info) => {
            write!(f, "PrimopReset {:?} = {:p} ` {:?}", loc, reset, info)
        }
        PrimopVariadic(loc, fptr, args, info) => {
            write!(f, "PrimopVariadic {:?} = {:p}({:?}) ` {:?}", loc, fptr, args, info)
        }
    };

    f
}
pub fn print_instr<B>(pc: usize, instr: &Instr<Name, B>, symtab: &Symtab, function_name: Name) {
    let mut binding = String::new();
    let s = print_instr_toString(&mut binding, instr, symtab);
    println!("[{}:{}]{:?}", symtab.to_str(function_name), pc, s);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::IRTypeInfo;
    use std::collections::{BTreeMap, HashMap, HashSet};

    /// 创建一个用于测试的最小 SharedState
    ///
    /// 注意：此项目使用 Ruby 测试框架而非 Rust 标准测试框架。
    /// 这些测试函数作为文档和示例代码提供，展示如何使用 from_str 方法。
    fn create_test_shared_state<'ir, B: BV>() -> SharedState<'ir, B> {
        let mut symtab = Symtab::new();
        // 添加一些测试用的符号
        symtab.intern("x");
        symtab.intern("y");
        symtab.intern("field1");
        symtab.intern("field2");
        symtab.intern("SomeCtor");
        symtab.intern("TestEnum");
        symtab.intern("TestStruct");
        symtab.intern("Member1");

        SharedState {
            functions: HashMap::default(),
            externs: HashMap::default(),
            symtab,
            type_info: IRTypeInfo {
                structs: HashMap::default(),
                enums: HashMap::default(),
                enum_members: HashMap::default(),
                unions: HashMap::default(),
                union_ctors: HashSet::default(),
            },
            registers: HashMap::default(),
            probes: HashSet::new(),
            probe_functions: HashSet::new(),
            trace_functions: HashSet::new(),
            itrace: crate::tracetool::itrace::ItraceHandler::default(),
            reset_registers: Vec::new(),
            reset_constraints: Vec::new(),
            function_assumptions: Vec::new(),
        }
    }

    /// 示例：解析 I64 值
    ///
    /// ```ignore
    /// let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();
    /// let val = Val::from_str("I64(42)", &shared_state).unwrap();
    /// assert!(matches!(val, Val::I64(42)));
    /// ```
    #[test]
    fn test_val_from_str_i64() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 构造函数格式 I64(42)
        let val = Val::from_str("I64(42)", &shared_state).unwrap();
        assert!(matches!(val, Val::I64(42)));

        // 测试负数
        let val = Val::from_str("I64(-123)", &shared_state).unwrap();
        assert!(matches!(val, Val::I64(-123)));
    }

    /// 示例：解析 I128 值
    #[test]
    fn test_val_from_str_i128() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        let val = Val::from_str("I128(456)", &shared_state).unwrap();
        assert!(matches!(val, Val::I128(456)));
    }

    /// 示例：解析 Bool 值
    #[test]
    fn test_val_from_str_bool() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 构造函数格式
        let val = Val::from_str("Bool(true)", &shared_state).unwrap();
        assert!(matches!(val, Val::Bool(true)));

        let val = Val::from_str("Bool(false)", &shared_state).unwrap();
        assert!(matches!(val, Val::Bool(false)));

        // 简单格式
        let val = Val::from_str("true", &shared_state).unwrap();
        assert!(matches!(val, Val::Bool(true)));

        let val = Val::from_str("false", &shared_state).unwrap();
        assert!(matches!(val, Val::Bool(false)));
    }

    /// 示例：解析 Unit 值
    #[test]
    fn test_val_from_str_unit() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        let val = Val::from_str("()", &shared_state).unwrap();
        assert!(matches!(val, Val::Unit));

        let val = Val::from_str("Unit", &shared_state).unwrap();
        assert!(matches!(val, Val::Unit));
    }

    /// 示例：解析 Poison 值
    #[test]
    fn test_val_from_str_poison() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        let val = Val::from_str("<poison>", &shared_state).unwrap();
        assert!(matches!(val, Val::Poison));

        let val = Val::from_str("Poison", &shared_state).unwrap();
        assert!(matches!(val, Val::Poison));
    }

    /// 示例：解析 String 值
    #[test]
    fn test_val_from_str_string() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 简单格式
        let val = Val::from_str("\"hello world\"", &shared_state).unwrap();
        assert!(matches!(val, Val::String(_)));
        if let Val::String(s) = val {
            assert_eq!(s, "hello world");
        }
    }

    /// 示例：解析 Vector 值
    #[test]
    fn test_val_from_str_vector() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 空向量
        let val = Val::from_str("[]", &shared_state).unwrap();
        assert!(matches!(val, Val::Vector(_)));
        if let Val::Vector(v) = val {
            assert_eq!(v.len(), 0);
        }

        // 非空向量
        let val = Val::from_str("[I64(1), I64(2), I64(3)]", &shared_state).unwrap();
        assert!(matches!(val, Val::Vector(_)));
        if let Val::Vector(v) = val {
            assert_eq!(v.len(), 3);
        }
    }

    /// 示例：解析 List 值
    #[test]
    fn test_val_from_str_list() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 空列表
        let val = Val::from_str("List[]", &shared_state).unwrap();
        assert!(matches!(val, Val::List(_)));
        if let Val::List(v) = val {
            assert_eq!(v.len(), 0);
        }

        // 非空列表
        let val = Val::from_str("List[Bool(true), Bool(false)]", &shared_state).unwrap();
        assert!(matches!(val, Val::List(_)));
        if let Val::List(v) = val {
            assert_eq!(v.len(), 2);
        }
    }

    /// 示例：解析 Struct 值
    #[test]
    fn test_val_from_str_struct() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 空结构体
        let val = Val::from_str("{}", &shared_state).unwrap();
        assert!(matches!(val, Val::Struct(_)));
        if let Val::Struct(m) = val {
            assert_eq!(m.len(), 0);
        }

        // 非空结构体
        let val = Val::from_str("{field1: 1i64, field2: 2i64}", &shared_state).unwrap();
        assert!(matches!(val, Val::Struct(_)));
        if let Val::Struct(m) = val {
            assert_eq!(m.len(), 2);
        }
    }

    /// 示例：to_str 和 from_str 往返转换测试
    ///
    /// 注意：from_str 支持构造函数格式，to_str 输出紧凑格式
    /// 往返转换测试仅检查兼容的类型
    #[test]
    fn test_val_from_str_constructor_format() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 测试构造函数格式
        assert!(matches!(Val::from_str("I64(42)", &shared_state).unwrap(), Val::I64(42)));
        assert!(matches!(Val::from_str("I128(123)", &shared_state).unwrap(), Val::I128(123)));
        assert!(matches!(Val::from_str("Bool(true)", &shared_state).unwrap(), Val::Bool(true)));
        assert!(matches!(Val::from_str("Unit", &shared_state).unwrap(), Val::Unit));
        assert!(matches!(Val::from_str("Poison", &shared_state).unwrap(), Val::Poison));
    }

    /// 示例：无效输入的错误处理
    #[test]
    fn test_val_from_str_invalid() {
        let shared_state = create_test_shared_state::<crate::bitvector::b64::B64>();

        // 测试无效输入
        assert!(Val::from_str("invalid_format", &shared_state).is_err());
        assert!(Val::from_str("I64()", &shared_state).is_err()); // 空括号
        assert!(Val::from_str("I64(abc)", &shared_state).is_err()); // 非数字
        assert!(Val::from_str("&nonexistent", &shared_state).is_err());
    }
}
