use crate::bitvector::BV;
use crate::ir::*;
use crate::isarch::get_symbolic_arg_all;
use crate::register::RegisterBindings;
use crate::smt::Checkpoint;
use crate::zencode;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Clone)]
pub struct ArgStruct<'ir, B> {
    pub arg_value: Val<B>,
    pub clause_name: Option<String>,
    pub checkpoint: Checkpoint<B>,
    shared_state: &'ir SharedState<'ir, B>,
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

/**
    YAML
*/
#[derive(Deserialize, Serialize)]
pub struct YAMLSerializerBuilder {
    pub arg_value: Vec<String>,
    pub clause_name: Option<String>,
}

impl YAMLSerializerBuilder {
    pub fn new(arg_value: Vec<String>, clause_name: Option<String>) -> Self {
        YAMLSerializerBuilder { arg_value, clause_name }
    }

    /// 从 ArgStruct 转换为 YAML 序列化结构
    /// 将 Val<B> 转换为 YAML 格式的字符串向量
    /// 对于 Struct/Vector/List 类型，会展开为扁平的字符串向量
    pub fn from_ArgStruct<B: BV>(arg: &ArgStruct<B>) -> Self {
        let arg_value = Self::val_to_yaml_strings_flat(&arg.arg_value, arg.shared_state);
        Self::new(arg_value, arg.clause_name.clone())
    }

    /// 将 Val<B> 转换为扁平的字符串向量（用于 Struct 内部字段的展开）
    fn val_to_yaml_strings_flat<B: BV>(val: &Val<B>, shared_state: &SharedState<B>) -> Vec<String> {
        match val {
            Val::Struct(fields) => {
                // 对于元组/结构体，按照字段顺序展开
                // 先获取字段名并排序（保持一致的顺序）
                let mut field_names: Vec<_> = fields.keys().collect();
                field_names.sort_by_key(|k| shared_state.symtab.to_str(**k));
                // 展开所有字段的值
                field_names
                    .iter()
                    .flat_map(|name| Self::val_to_yaml_strings_flat(&fields[*name], shared_state))
                    .collect()
            }
            Val::Vector(vec) => vec.iter().flat_map(|v| Self::val_to_yaml_strings_flat(v, shared_state)).collect(),
            Val::List(vec) => vec.iter().flat_map(|v| Self::val_to_yaml_strings_flat(v, shared_state)).collect(),
            _ => Self::val_to_yaml_strings(val, shared_state),
        }
    }

    /// 将 Val<B> 递归转换为 YAML 格式的字符串向量
    fn val_to_yaml_strings<B: BV>(val: &Val<B>, shared_state: &SharedState<B>) -> Vec<String> {
        match val {
            Val::Symbolic(sym) => {
                // 对于符号变量，输出为 "Sym"（不带 ID）
                vec!["Sym".to_string()]
            }
            Val::I64(n) => vec![format!("i64({})", n)],
            Val::I128(n) => vec![format!("i128({})", n)],
            Val::Bool(b) => vec![b.to_string()],
            Val::Bits(bv) => vec![format!("{}", bv)],
            Val::Enum(member) => {
                // 保持 z-encoded 格式，不做解码
                let enum_name = shared_state.symtab.to_str(member.enum_id.to_name());
                let member_name = shared_state
                    .type_info
                    .enums
                    .get(&member.enum_id.to_name())
                    .and_then(|members| members.iter().nth(member.member))
                    .map(|name| shared_state.symtab.to_str(*name).to_string())
                    .unwrap_or_else(|| format!("<member {}>", member.member));
                vec![format!("enum({}.{})", enum_name, member_name)]
            }
            Val::String(s) => vec![format!("\"{}\"", s)],
            Val::Unit => vec!["()".to_string()],
            Val::Vector(vec) => vec.iter().flat_map(|v| Self::val_to_yaml_strings(v, shared_state)).collect(),
            Val::List(vec) => vec.iter().flat_map(|v| Self::val_to_yaml_strings(v, shared_state)).collect(),
            Val::Struct(fields) => {
                let mut result = String::from("{");
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|(name, val)| {
                        let name_decoded = zencode::decode(shared_state.symtab.to_str(*name));
                        let val_strings = Self::val_to_yaml_strings(val, shared_state);
                        format!("{}: {}", name_decoded, val_strings.join(", "))
                    })
                    .collect();
                result.push_str(&field_strs.join(", "));
                result.push('}');
                vec![result]
            }
            Val::Ctor(name, val) => {
                let name_decoded = zencode::decode(shared_state.symtab.to_str(*name));
                let inner = Self::val_to_yaml_strings(val, shared_state);
                vec![format!("{}({})", name_decoded, inner.join(", "))]
            }
            Val::SymbolicCtor(discriminant, fields) => {
                let disc_str = format!("Sym({})", discriminant);
                let field_strs: Vec<String> = fields
                    .iter()
                    .map(|(name, val)| {
                        let name_decoded = zencode::decode(shared_state.symtab.to_str(*name));
                        let val_strings = Self::val_to_yaml_strings(val, shared_state);
                        format!("{}: {}", name_decoded, val_strings.join(", "))
                    })
                    .collect();
                vec![format!("{}({{{}}})", disc_str, field_strs.join(", "))]
            }
            Val::Ref(name) => {
                let name_decoded = zencode::decode(shared_state.symtab.to_str(*name));
                vec![format!("ref({})", name_decoded)]
            }
            Val::MixedBits(segments) => {
                let parts: Vec<String> = segments
                    .iter()
                    .map(|seg| match seg {
                        BitsSegment::Symbolic(s) => format!("Sym({})", s),
                        BitsSegment::Concrete(b) => format!("{}", b),
                    })
                    .collect();
                vec![format!("[{}]", parts.join(", "))]
            }
            Val::Poison => vec!["<poison>".to_string()],
        }
    }
}

#[cfg(feature = "debug_clause_args")]
pub fn test_clause_args_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_instruction_list_main");

    let assembly_names = get_symbolic_arg_all("zRTYPE", shared_state, regs, lets);
    // let assembly_names = get_assembly_names_all("zSTORE", shared_state, regs, lets);

    /* assembly_names.iter().for_each(|name| {
        println!("{}", name);
    }); */
    //println!("{:#?}", assembly_names);

    //let yaml_str = fs::read_to_string("conf.yml").unwrap();
    //let map: HashMap<String, serde_saphyr::Value> = serde_saphyr::from_str(&yaml_str)?;

    let yaml = serde_saphyr::to_string(
        &assembly_names.iter().map(|x| YAMLSerializerBuilder::from_ArgStruct(x)).collect::<Vec<_>>(),
    )
    .unwrap();
    println!("{}", yaml);

    ()
}
