use crate::bitvector::BV;
use crate::dlog;
use crate::ir::*;
use crate::isarch::{
    generate_default_value, get_default_arg_all, get_symbolic_arg_all, ir_assembly_names_to_InstructionMap,
};
use crate::isarch_args;
use crate::isarch_args::ArgStruct;
use crate::register::RegisterBindings;
use crate::smt::smtlib::Exp;
use crate::smt::{checkpoint, Config, Context, EnumMember, Model};
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;
use core::slice;
use indicatif::{ProgressBar, ProgressStyle};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::panic::panic_any;

pub trait MergeMaps<K, V> {
    fn merge_values(self) -> HashMap<K, HashSet<V>>;
}

///
/// 将多个 HashMap 合并为一个 HashMap，其中相同的 key 对应的 value 会被合并为 HashSet。
///
/// # 示例
///
/// ```
/// use std::collections::{HashMap, HashSet};
///
/// let maps = vec![
///     [("a".to_string(), 1), ("b".to_string(), 2)].into_iter().collect(),
///     [("a".to_string(), 1), ("a".to_string(), 3), ("c".to_string(), 4)].into_iter().collect(),
/// ];
/// let merged = maps.merge_values();
///
/// // 检查 "a" 对应的值是 {1, 3}
/// assert_eq!(merged.get("a"), Some(&HashSet::from([1, 3])));
/// // 检查 "b" 对应的值是 {2}
/// assert_eq!(merged.get("b"), Some(&HashSet::from([2])));
/// // 检查 "c" 对应的值是 {4}
/// assert_eq!(merged.get("c"), Some(&HashSet::from([4])));
/// ```
///
impl<K, V> MergeMaps<K, V> for Vec<HashMap<K, V>>
where
    K: Eq + Hash + Clone,
    V: Eq + Hash + Clone,
{
    fn merge_values(self) -> HashMap<K, HashSet<V>> {
        self.into_iter().flatten().fold(HashMap::new(), |mut acc, (k, v)| {
            acc.entry(k).or_default().insert(v);
            acc
        })
    }
}

/**
    YAML
*/

impl Sym {
    pub fn sym_solve_str<B: BV>(&self, point: &Checkpoint<B>, shared_state: &SharedState<B>) -> String {
        let mut cfg = Config::new();
        cfg.set_param_value("model", "true");
        let ctx = Context::new(cfg);
        let mut solver = Solver::from_checkpoint(&ctx, point.clone());

        if solver.check_sat(SourceLoc::unknown()) != crate::smt::SmtResult::Sat {
            panic!(
                "  符号求解失败: UNSAT 或 UNKNOWN (不过不用担心，大概是z3子进程由于Ctrl+C或者其他原因被杀掉了导致的)"
            );
            // return;
        }
        let mut model = Model::new(&solver);

        let sym = &self.clone();
        match model.get_var(*sym) {
            Ok(model_val) => match model_val {
                crate::smt::ModelVal::Exp(exp) => {
                    // let val = execute::eval_exp(exp, local_state, shared_state, solver, info)?.into_owned();
                    match &exp {
                        Exp::Var(v) => format!("{}", v.sym_solve_str(&point, &shared_state)),
                        Exp::Bits(vec) => format!("{:?}", &exp),
                        Exp::Bits64(b64) => format!("{:?}", b64),
                        Exp::Enum(enum_member) => format!("{:?}", &exp),
                        Exp::Bool(b) => format!("{:?}", &exp),
                        // 对于复合表达式（如Eq, And等），返回"Sym"表示需要符号化处理
                        // 这些表达式通常包含多个变量或复杂逻辑，不适合简单的字符串表示
                        Exp::Eq(_, _) | Exp::Neq(_, _) | Exp::And(_, _) | Exp::Or(_, _) | Exp::Not(_) |
                        Exp::Bvnot(_) | Exp::Bvand(_, _) | Exp::Bvor(_, _) | Exp::Bvxor(_, _) |
                        Exp::Bvnand(_, _) | Exp::Bvnor(_, _) | Exp::Bvxnor(_, _) | Exp::Bvneg(_) |
                        Exp::Bvadd(_, _) | Exp::Bvsub(_, _) | Exp::Bvmul(_, _) | Exp::Bvudiv(_, _) |
                        Exp::Bvsdiv(_, _) | Exp::Bvurem(_, _) | Exp::Bvsrem(_, _) | Exp::Bvsmod(_, _) |
                        Exp::Bvult(_, _) | Exp::Bvslt(_, _) | Exp::Bvule(_, _) | Exp::Bvsle(_, _) |
                        Exp::Bvuge(_, _) | Exp::Bvsge(_, _) | Exp::Bvugt(_, _) | Exp::Bvsgt(_, _) |
                        Exp::Extract(_, _, _) | Exp::ZeroExtend(_, _) | Exp::SignExtend(_, _) |
                        Exp::Bvshl(_, _) | Exp::Bvlshr(_, _) | Exp::Bvashr(_, _) | Exp::Concat(_, _) |
                        Exp::Ite(_, _, _) | Exp::App(_, _) | Exp::Select(_, _) | Exp::Store(_, _, _) |
                        Exp::Distinct(_) | Exp::FPConstant(_, _, _) | Exp::FPRoundingMode(_) |
                        Exp::FPUnary(_, _) | Exp::FPRoundingUnary(_, _, _) | Exp::FPBinary(_, _, _) |
                        Exp::FPRoundingBinary(_, _, _, _) | Exp::FPfma(_, _, _, _) => {
                            "Sym".to_string()
                        }
                    }
                }
                crate::smt::ModelVal::Arbitrary(ty) => {
                    // 当模型无法给出具体值时，返回一个通用的符号表示
                    dlog!("    符号变量Sym({:?})的值为Arbitrary ({:?})，将返回'Sym'", sym, ty);
                    "Arbitrary".to_string()
                }
            },
            Err(e) => {
                panic!("    Sym({:?}) = Error: {:?}", sym, e);
            }
        }
    }
}
impl<B: BV> Val<B> {
    pub fn sym_solve_str(&self, point: &Checkpoint<B>, shared_state: &SharedState<B>) -> String {
        match self {
            Val::Symbolic(sym) => sym.sym_solve_str(&point, &shared_state),
            _ => panic!("sym_solve:在符号化变量的求值中出现了非符号化的变量"),
        }
    }
}

/// 单条指令的参数定义（用于 YAML 序列化）
#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct YAMLInstArgs {
    pub clause: String,
    pub args: HashMap<String, String>,
}

/// 所有指令的 YAML 结构
#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct YAMLAllInstructions {
    pub instrs: HashMap<String, YAMLInstArgs>,
}
impl YAMLInstArgs {
    pub fn new(clause: String, args: HashMap<String, String>) -> Self {
        YAMLInstArgs { clause, args }
    }
}
impl YAMLAllInstructions {
    pub fn new(instrs: HashMap<String, YAMLInstArgs>) -> Self {
        YAMLAllInstructions { instrs }
    }
}
// Trait 为 Vec<ArgStruct> 提供 YAML 序列化功能
trait ToYAMLSerializer<'ir, B: BV> {
    fn to_YAMLSerializerBuilder(&self) -> YAMLInstArgs;
}

impl<'ir, B: BV> ToYAMLSerializer<'ir, B> for Vec<isarch_args::ArgStruct<'ir, B>> {
    fn to_YAMLSerializerBuilder(&self) -> YAMLInstArgs {
        let arg_struct_vec = self.clone();
        let mut yaml_map_vec: Vec<HashMap<String, String>> = Vec::new();
        let mut clause_name_mut: Option<String> =
            arg_struct_vec.iter().next().and_then(|arg_struct| arg_struct.clause_name.clone());

        //把表里面的Val转成字符串
        for arg_struct in arg_struct_vec {
            // 在解构前先借用，用于调试输出
            if clause_name_mut != arg_struct.clause_name {
                panic!(
                    "clause_name({:?})和其他的ArgStruct中的名字不一样\n  当前ArgStruct：{:?}",
                    arg_struct.clause_name, &arg_struct
                );
            }
            let ArgStruct { arg_value, clause_name, checkpoint: point, shared_state } = arg_struct;
            match arg_value {
                Val::Struct(map) => {
                    let yaml_map = map
                        .clone()
                        .iter()
                        .map(|(k, v)| {
                            (
                                k.to_str(&shared_state),
                                match &v {
                                    Val::Symbolic(sym) => v.sym_solve_str(&point, &shared_state),
                                    // 处理枚举类型字段
                                    Val::Enum(enum_member) => {
                                        // 获取枚举名称
                                        let enum_name = shared_state.symtab.to_str(enum_member.enum_id.to_name());
                                        // 获取成员名称（如果有成员定义）
                                        let member_name = if let Some(members) = shared_state.type_info.enums.get(&enum_member.enum_id.to_name()) {
                                            if let Some(&name) = members.get(enum_member.member) {
                                                shared_state.symtab.to_str(name)
                                            } else {
                                                &format!("{}", enum_member.member)
                                            }
                                        } else {
                                            &format!("{}", enum_member.member)
                                        };
                                        format!("{}::{}", enum_name, member_name)
                                    }
                                    _ => panic!("TODO:还要加其他类型的实现：{:#?}", v),
                                },
                            )
                        })
                        .collect::<HashMap<_, _>>();
                    //println!("[Struct]:{:#?}", yaml_map)
                    yaml_map_vec.push(yaml_map);
                }
                // Val::Unit 表示无参数的指令，创建一个空的HashMap
                Val::Unit => {
                    // 对于Unit类型，创建一个空的HashMap
                    yaml_map_vec.push(HashMap::new());
                }
                // 处理符号化值类型（如Bits等）
                // 对于符号化值，创建一个包含键值对的单元素HashMap
                Val::Symbolic(sym) => {
                    let mut yaml_map = HashMap::new();
                    yaml_map.insert("value".to_string(), sym.sym_solve_str(&point, &shared_state));
                    yaml_map_vec.push(yaml_map);
                }
                // 处理枚举值类型
                Val::Enum(enum_member) => {
                    let mut yaml_map = HashMap::new();
                    // 获取枚举名称
                    let enum_name = shared_state.symtab.to_str(enum_member.enum_id.to_name());
                    // 获取成员名称（如果有成员定义）
                    let member_name = if let Some(members) = shared_state.type_info.enums.get(&enum_member.enum_id.to_name()) {
                        if let Some(&name) = members.get(enum_member.member) {
                            shared_state.symtab.to_str(name)
                        } else {
                            &format!("{}", enum_member.member)
                        }
                    } else {
                        &format!("{}", enum_member.member)
                    };
                    yaml_map.insert("value".to_string(), format!("{}::{}", enum_name, member_name));
                    yaml_map_vec.push(yaml_map);
                }
                _ => panic!("TODO: 未处理的参数类型，类型为{}:\n{:#?}", arg_value.type_string(), &arg_value),
            }
        }

        /*
         * yaml_map_merge = {
         *   "rs1":["xxx","xxx"]
         *   "rs2":["xxx","xxx"]
         * }
         */
        let yaml_map_merge = yaml_map_vec.merge_values();

        /*
         * 返回值的操作  {
         *   "rs1":["xxx","xxx"...] => "Sym"  如果有多个，就拿Sym代替
         *   "rs2":["xxx"] => "xxx"  如果就一个，就不改了
         * }
         */
        let yaml_map_merge_simplify = yaml_map_merge
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    match v.len() {
                        0 => panic!("表中字段{}没有元素：{:#?}", k, yaml_map_merge),
                        1 => v.iter().next().unwrap().clone(),
                        _ => "Sym".to_string(),
                    },
                )
            })
            .collect::<HashMap<_, _>>();

        YAMLInstArgs::new(
            clause_name_mut.unwrap_or_else(|| panic!("clause_name(zMRET/zSTORE)不应该有为None的字符串")),
            yaml_map_merge_simplify,
        )
    }
}

/// 将 InstructionMap 转换为 YAML 格式并写入文件
pub fn write_instruction_map_to_yaml<'ir, B: BV>(
    instruction_map: &isarch_args::InstructionMap<'ir, B>,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let all_instructions = YAMLAllInstructions::new(
        instruction_map
            .to_vec()
            .into_iter()
            .map(|(instr_name, arg_struct_vec)| (instr_name, arg_struct_vec.to_YAMLSerializerBuilder()))
            .collect(),
    );

    let yaml_string = serde_saphyr::to_string(&all_instructions)?;
    std::fs::write(output_path, yaml_string)?;

    Ok(())
}

#[cfg(feature = "debug_clause_args_yaml")]
pub fn test_clause_args_yaml_main<B: BV>(
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) {
    println!("test_clause_args_yaml_main");

    let clause_names = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")).unwrap();
    println!("一共有{}种clause_name", clause_names.len());

    // 创建进度条
    let progress = ProgressBar::new(clause_names.len() as u64);
    progress.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} {msg}")
            .unwrap()
            .progress_chars("##-"),
    );
    progress.set_message("正在处理指令...");

    // 收集所有需要处理的指令名称
    let instruction_names: Vec<String> = clause_names
        .iter()
        .map(|(n, _)| shared_state.symtab.to_str(*n).to_string())
        .collect();

    // 使用 Rayon 并行处理
    let results: Vec<(String, Result<(), String>)> = instruction_names
        .into_par_iter() // 并行迭代器
        .map(|clause_name| {
            let out = ir_assembly_names_to_InstructionMap(&clause_name, shared_state, regs, lets);

            // 将结果写入 YAML 文件
            let file_name = format!("profiles/riscv/args_{}.yaml", clause_name);
            let result = write_instruction_map_to_yaml(&out, &file_name).map_err(|e| e.to_string());
            (clause_name, result)
        })
        .collect();

    // 更新进度条并输出结果
    for (clause_name, result) in results {
        match result {
            Ok(_) => {
                progress.set_message(format!("{} 完成", clause_name));
            }
            Err(e) => {
                progress.println(format!("写入 YAML 文件(args_{}.yaml)失败: {}", clause_name, e));
            }
        }
        progress.inc(1);
    }

    progress.finish_with_message("所有指令处理完成!");
}
