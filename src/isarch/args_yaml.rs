use crate::isarch::args;
use crate::isarch::args::ArgStruct;
use crate::isarch::ir_assembly_names_to_InstructionMap;
use isla_lib::bitvector::BV;
use isla_lib::ir::*;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Checkpoint, Solver, Sym};
use isla_lib::smt::{Config, Context, Model};
use isla_lib::source_loc::SourceLoc;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

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
/// use isla::isarch::args_yaml::MergeMaps;
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

pub fn sym_solve_str<B: BV>(sym: &Sym, point: &Checkpoint<B>, shared_state: &SharedState<B>) -> String {
    let mut cfg = Config::new();
    cfg.set_param_value("model", "true");
    let ctx = Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, point.clone());

    if solver.check_sat(SourceLoc::unknown()) != isla_lib::smt::SmtResult::Sat {
        panic!("  符号求解失败: UNSAT 或 UNKNOWN (不过不用担心，大概是z3子进程由于Ctrl+C或者其他原因被杀掉了导致的)");
        // return;
    }
    let mut model = Model::new(&solver);

    let sym = &sym.clone();
    match model.get_var(*sym) {
        Ok(model_val) => match model_val {
            isla_lib::smt::ModelVal::Exp(exp) => {
                // let val = execute::eval_exp(exp, local_state, shared_state, solver, info)?.into_owned();
                match &exp {
                    Exp::Var(v) => format!("{}", sym_solve_str(v, point, shared_state)),
                    Exp::Bits(vec) => format!("{:?}", &exp),
                    Exp::Bits64(b64) => format!("{:?}", b64),
                    Exp::Enum(enum_member) => format!("{:?}", &exp),
                    Exp::Bool(b) => format!("{:?}", &exp),
                    _ => panic!("不知道怎么处理的符号表达式Exp:{:?}", &exp),
                }
            }
            isla_lib::smt::ModelVal::Arbitrary(ty) => {
                panic!("    不知道怎么处理的符号变量Sym({:?}) = Arbitrary ({:?})", sym, ty);
            }
        },
        Err(e) => {
            panic!("    Sym({:?}) = Error: {:?}", sym, e);
        }
    }
}

pub fn val_sym_solve_str<B: BV>(val: &Val<B>, point: &Checkpoint<B>, shared_state: &SharedState<B>) -> String {
    match val {
        Val::Symbolic(sym) => sym_solve_str(sym, point, shared_state),
        _ => panic!("sym_solve:在符号化变量的求值中出现了非符号化的变量"),
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
    #[allow(non_snake_case)]
    fn to_yaml_serializer_builder(&self) -> YAMLInstArgs;
}

impl<'ir, B: BV> ToYAMLSerializer<'ir, B> for Vec<args::ArgStruct<'ir, B>> {
    fn to_yaml_serializer_builder(&self) -> YAMLInstArgs {
        let arg_struct_vec = self.clone();
        let mut yaml_map_vec: Vec<HashMap<String, String>> = Vec::new();
        let clause_name_mut: Option<String> =
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
                                    Val::Symbolic(sym) => val_sym_solve_str(v, &point, &shared_state),
                                    _ => panic!("TODO:还要加其他类型的实现：{:#?}", v),
                                },
                            )
                        })
                        .collect::<HashMap<_, _>>();
                    //println!("[Struct]:{:#?}", yaml_map)
                    yaml_map_vec.push(yaml_map);
                }
                _ => panic!("这是什么类型？{:?}", arg_value),
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
    instruction_map: &args::InstructionMap<'ir, B>,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let all_instructions = YAMLAllInstructions::new(
        instruction_map
            .to_vec()
            .into_iter()
            .map(|(instr_name, arg_struct_vec)| (instr_name, arg_struct_vec.to_yaml_serializer_builder()))
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

    for (n, ty) in shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")).unwrap().iter() {
        let inst_union_name_str = shared_state.symtab.to_str(*n);
        let clause_name = &inst_union_name_str;

        let out = ir_assembly_names_to_InstructionMap(clause_name, shared_state, regs, lets);

        // 将结果写入 YAML 文件
        let file_name = &format!("profiles/riscv/args_{}.yaml", clause_name);
        match write_instruction_map_to_yaml(&out, file_name) {
            Ok(_) => println!("YAML 文件已成功写入到 {}", file_name),
            Err(e) => eprintln!("写入 YAML 文件({})失败: {}", file_name, e),
        }
    }
}
