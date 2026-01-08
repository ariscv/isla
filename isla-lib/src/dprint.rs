use std::fmt;
use crate::ir::{Instr, Name, Symtab};
use crate::ir::Instr::{Arbitrary, End};

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

use Instr::*;
use std::fmt::Write;
pub fn print_instr_toString<'a, B>(f: &'a mut String,instr: &'a  Instr<Name, B>, symtab: &Symtab) -> &'a mut String{

    macro_rules! s {
    ($id:expr) => {
        symtab.to_str_demangled($id)
    };
}

            let res=match instr {
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
                PrimopVariadic(loc, fptr, args, info) => write!(f, "PrimopVariadic {:?} = {:p}({:?}) ` {:?}", loc, fptr, args, info),
            };

f
}
pub fn print_instr<B>(pc:usize,instr: &Instr<Name, B>, symtab: &Symtab,function_name: Name) {

    let mut binding = String::new();
    let s=print_instr_toString(&mut binding,instr,symtab);
    println!("[{}:{}]{:?}",symtab.to_str(function_name),pc, s);
}