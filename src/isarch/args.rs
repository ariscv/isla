use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::Checkpoint;
use std::collections::HashMap;

#[derive(Clone)]
pub struct ArgStruct<'ir, B> {
    pub arg_value: Val<B>,
    pub clause_name: Option<String>,
    pub checkpoint: Checkpoint<B>,
    pub shared_state: &'ir SharedState<'ir, B>,
}

impl<'ir, B: BV> ArgStruct<'ir, B> {
    pub fn new(
        arg_value: Val<B>,
        clause_name: Option<String>,
        checkpoint: Checkpoint<B>,
        shared_state: &'ir SharedState<'_, B>,
    ) -> Self {
        ArgStruct { arg_value, clause_name, checkpoint, shared_state }
    }
    pub fn from_tuple(
        tupple: (Val<B>, Checkpoint<B>),
        clause_name: Option<&str>,
        shared_state: &'ir SharedState<'_, B>,
    ) -> Self {
        let (arg_value, checkpoint) = tupple;
        Self::new(
            arg_value,
            match clause_name {
                Some(s) => Some(s.to_string()),
                None => None,
            },
            checkpoint,
            shared_state,
        )
    }
}

impl<'ir, B: BV> std::fmt::Display for ArgStruct<'ir, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "arg_value={}, clause_name={:?}", self.arg_value.to_str_fmt(self.shared_state), self.clause_name)
    }
}

impl<'ir, B: BV> std::fmt::Debug for ArgStruct<'ir, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // arg_value 使用 Display 风格（保留换行），clause_name 使用 Debug 风格
        let arg_value_str = self.arg_value.to_str_fmt(self.shared_state);
        // 对每一行添加缩进，使其与 "arg_value: " 对齐
        let indented = arg_value_str
            .lines()
            .map(|line| format!("        {}", line)) // 8 空格缩进对齐
            .collect::<Vec<_>>()
            .join("\n");
        write!(f, "ArgStruct {{\n    arg_value: {},\n    clause_name: {:?},\n}}", indented, self.clause_name)
    }
}

#[derive(Clone)]
pub struct InstructionMap<'ir, B> {
    table: Vec<(String, Vec<ArgStruct<'ir, B>>)>,
    shared_state: &'ir SharedState<'ir, B>,
}
impl<'ir, B: BV> InstructionMap<'ir, B> {
    pub fn new(table: Vec<(String, Vec<ArgStruct<'ir, B>>)>, shared_state: &'ir SharedState<'_, B>) -> Self {
        InstructionMap { table, shared_state }
    }
    pub fn from_vec_with_shared_state(
        vec: &Vec<(String, Vec<ArgStruct<'ir, B>>)>,
        shared_state: &'ir SharedState<'ir, B>,
    ) -> Self {
        let all_same =
            vec.iter().all(|(_, arg_vec)| arg_vec.iter().all(|arg| std::ptr::eq(shared_state, arg.shared_state)));

        if !all_same {
            panic!("from_vec: not all shared_state pointers are the same");
        }

        Self::new(vec.clone(), shared_state)
    }
    pub fn from_vec(vec: &Vec<(String, Vec<ArgStruct<'ir, B>>)>) -> Self {
        // 验证所有元素的 shared_state 指向同一个对象
        let shared_state = match vec.first() {
            None => panic!("from_vec: empty vec, 传进来的是个空列表{:?}, 建议用from_vec_with_shared_state", vec),
            Some((_, first_vec)) => match first_vec.first() {
                None => panic!("from_vec: empty inner vec"),
                Some(first) => first.shared_state,
            },
        };

        let all_same =
            vec.iter().all(|(_, arg_vec)| arg_vec.iter().all(|arg| std::ptr::eq(shared_state, arg.shared_state)));

        if !all_same {
            panic!("from_vec: not all shared_state pointers are the same");
        }

        Self::from_vec_with_shared_state(vec, &shared_state)
    }
    pub fn from_map(map: &HashMap<String, Vec<ArgStruct<'ir, B>>>) -> Self {
        let vec = map.clone().into_iter().collect();
        Self::from_vec(&vec)
    }
    pub fn table(&mut self) -> &mut Vec<(String, Vec<ArgStruct<'ir, B>>)> {
        &mut self.table
    }
    pub fn to_vec(&self) -> Vec<(String, Vec<ArgStruct<'ir, B>>)> {
        self.table.clone().into_iter().collect()
    }
    pub fn to_map(&self) -> HashMap<String, Vec<ArgStruct<'ir, B>>> {
        self.table.clone().into_iter().collect()
    }
    /// 用于在生成yaml时，多个clause name的InstructionMap合并成一个大的
    pub fn merge_with(self, that: Self) -> Self {
        // 将两个 InstructionMap 的 table 合并
        let mut merged_table = self.table;
        merged_table.extend(that.table);
        InstructionMap::new(merged_table, self.shared_state)
    }
}

use crate::isarch::{get_symbolic_arg_all, ir_assembly_names_to_InstructionMap};

pub fn test_clause_args_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_clause_args_main");

    /* {
        let func_id = shared_state.symtab.lookup("zMRET");
        let (func_args, ret, instr) = shared_state.functions.get(&func_id).unwrap();

        dlog!("{:?}", (func_args, ret, instr.len()));
    } */
    let assembly_names = get_symbolic_arg_all("zRTYPE", shared_state, regs, lets);
    // let assembly_names = get_assembly_names_all("zSTORE", shared_state, regs, lets);

    /* assembly_names.iter().for_each(|name| {
        println!("{}", name);
    }); */
    //println!("{:#?}", assembly_names);

    //let yaml_str = fs::read_to_string("conf.yml").unwrap();
    //let map: HashMap<String, serde_saphyr::Value> = serde_saphyr::from_str(&yaml_str)?;

    //let yaml = serde_saphyr::to_string(
    //    &assembly_names.iter().map(|x| YAMLSerializerBuilder_PerInst::from_ArgStruct(x)).collect::<Vec<_>>(),
    //)
    //.unwrap();
    //println!("{}", yaml);

    let out = ir_assembly_names_to_InstructionMap("zSTORE", shared_state, regs, lets);

    ()
}
