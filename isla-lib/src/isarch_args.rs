use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::error::ExecError;
use crate::executor::{
    backtrace_string, execute_ir_function, start_single, Collector, LocalFrame, Run, TaskId, TaskState,
};
use crate::ir::*;
use crate::isarch::get_assembly_names_all;
use crate::log;
use crate::register::RegisterBindings;
use crate::smt::{checkpoint, Config, Context};
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::{d2, dlog, zencode};
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::{Arc, Mutex, Weak};

#[derive(Clone)]
pub struct ArgStruct<'ir, B> {
    pub arg_value: Val<B>,
    pub checkpoint: Checkpoint<B>,
    shared_state: &'ir SharedState<'ir, B>,
}

impl<'ir, B: BV> ArgStruct<'ir, B> {
    pub fn new(
        arg_value: Val<B>,
        clause: Option<String>,
        checkpoint: Checkpoint<B>,
        shared_state: &'ir SharedState<'_, B>,
    ) -> Self {
        ArgStruct { arg_value, checkpoint, shared_state }
    }
    pub fn from_tuple(tupple: (Val<B>, Checkpoint<B>), shared_state: &'ir SharedState<'_, B>) -> Self {
        let (arg_value, checkpoint) = tupple;
        Self::new(arg_value, None, checkpoint, shared_state)
    }
}
struct InstructionMap<'ir, B> {
    table: Vec<(String, ArgStruct<'ir, B>)>,
    shared_state: &'ir SharedState<'ir, B>,
}
impl<'ir, B: BV> InstructionMap<'ir, B> {
    pub fn new(table: Vec<(String, ArgStruct<'ir, B>)>, shared_state: &'ir SharedState<'_, B>) -> Self {
        InstructionMap { table, shared_state }
    }
    pub fn from_vec(vec: &Vec<(String, ArgStruct<'ir, B>)>) -> Self {
        // 验证所有元素的 shared_state 指向同一个对象
        let shared_state = match vec.first() {
            None => panic!("from_vec: empty vec"),
            Some((_, first)) => first.shared_state,
        };

        let all_same = vec.iter().all(|(_, arg)| std::ptr::eq(shared_state, arg.shared_state));

        if !all_same {
            panic!("from_vec: not all shared_state pointers are the same");
        }

        Self::new(vec.clone(), shared_state)
    }
    pub fn from_map(map: &HashMap<String, ArgStruct<'ir, B>>) -> Self {
        let vec = map.clone().into_iter().collect();
        Self::from_vec(&vec)
    }
    pub fn table(&mut self) -> &mut Vec<(String, ArgStruct<'ir, B>)> {
        &mut self.table
    }
    pub fn to_vec(&self) -> Vec<(String, ArgStruct<'ir, B>)> {
        self.table.clone().into_iter().collect()
    }
    pub fn to_map(&self) -> HashMap<String, ArgStruct<'ir, B>> {
        self.table.clone().into_iter().collect()
    }
}

#[cfg(feature = "debug_clause_args")]
pub fn test_clause_args_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_instruction_list_main");

    let assembly_names = get_assembly_names_all("zRTYPE", shared_state, regs, lets);
    // let assembly_names = get_assembly_names_all("zSTORE", shared_state, regs, lets);

    /* assembly_names.iter().for_each(|name| {
        println!("{}", name);
    }); */
    println!("{:?}", assembly_names);

    ()
}
