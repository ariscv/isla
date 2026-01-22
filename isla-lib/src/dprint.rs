use crate::bitvector::BV;
use crate::ir::Instr::{Arbitrary, End};
use crate::ir::{BitsSegment, Instr, Name, SharedState, Symtab, Val};
use crate::smt::{EnumMember, Sym};
use crate::zencode;
use std::fmt;

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
#[macro_export]
macro_rules! dlog {
    // 带日志级别的基础版本
    ($($arg:tt)*) => {{
        // 获取调用位置信息
        let file = file!();
        let line = line!();
        let column = column!();

        // 尝试获取函数名（nightly特性，需要启用 #![feature(backtrace)]）
        //#[cfg(feature = "backtrace")]
        let function_name = {
            fn __f() {} // 一个局部零大小函数
            std::any::type_name_of_val(&__f)
                .trim_end_matches("::__f")
                .trim_end_matches("::{{closure}}")
                .rsplit_once("::")        // 从右边切最后一次
                .map(|(_, name)| name)    // 只保留最后一段
                .unwrap_or("unknown")     // 兜底
        };

        //#[cfg(not(feature = "backtrace"))]
        //let function_name = {
        //    // 使用module_path!作为替代
        //    module_path!()
        //};

        // 输出格式：文件:行:列 在大多数IDE中是可点击的
        // 格式为：级别 [文件:行:列] 消息
        println!("{}[{}:{}:{} {}]: {} {}",
            $crate::dprint::colors::BLUE,
            file,
            line,
            column,
            function_name,
            format_args!($($arg)*),
            $crate::dprint::colors::RESET,
        );
    }};


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
                let member_name = shared_state
                    .type_info
                    .enums
                    .get(&member.enum_id.to_name())
                    .and_then(|members| members.iter().nth(member.member))
                    .map(|name| shared_state.symtab.to_str(*name).to_string())
                    .unwrap_or_else(|| format!("<member {}>", member.member));
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
