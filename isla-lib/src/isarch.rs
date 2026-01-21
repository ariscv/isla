use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::error::ExecError;
use crate::executor::{
    backtrace_string, execute_ir_function, start_single, Collector, LocalFrame, Run, TaskId, TaskState,
};
use crate::ir::*;
use crate::log;
use crate::register::RegisterBindings;
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::{d2, dlog, zencode};
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::{Arc, Mutex, Weak};

/**
 * instruction list gen
 */

/// 根据类型生成默认值
pub fn generate_default_value<B: BV>(ty: &Ty<Name>, shared_state: &SharedState<B>) -> Val<B> {
    match ty {
        Ty::Unit => Val::Unit,
        Ty::I64 => Val::I64(0),
        Ty::I128 => Val::I128(0),
        Ty::Bool => Val::Bool(false),
        Ty::Bits(n) => Val::Bits(B::zeros(*n)),
        Ty::String => Val::String(String::new()),
        Ty::Vector(elem_ty) => Val::Vector(vec![generate_default_value(elem_ty, shared_state)]),
        Ty::List(elem_ty) => Val::List(vec![generate_default_value(elem_ty, shared_state)]),
        Ty::Enum(enum_name) => {
            // 获取枚举的第一个成员作为默认值
            if let Some(_members) = shared_state.type_info.enums.get(enum_name) {
                Val::Enum(crate::smt::EnumId::from_name(*enum_name).first_member())
            } else {
                Val::Poison
            }
        }
        Ty::Struct(struct_name) => {
            // 为结构体的每个字段生成默认值
            let mut fields: std::collections::HashMap<Name, Val<B>> = std::collections::HashMap::new();
            if let Some(struct_def) = shared_state.type_info.structs.get(struct_name) {
                for (field_name, field_ty) in struct_def {
                    fields.insert(*field_name, generate_default_value(field_ty, shared_state));
                }
            }
            // 转换为 ahash::HashMap 类型以匹配 Val::Struct 的要求
            let ahash_fields: ahash::HashMap<Name, Val<B>> = fields.into_iter().collect();
            Val::Struct(ahash_fields)
        }
        Ty::Union(_) => Val::Unit, // Union 类型使用第一个构造函数的默认值
        _ => Val::Unit,            // 对于其他类型，使用 Unit 作为默认值
    }
}

/// 枚举类型的所有可能值
/// 对于枚举类型，返回所有可能的值；对于其他类型，返回包含单个默认值的向量
pub fn enumerate_possible_values<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
) -> Result<(Vec<Val<B>>, Vec<(String, String)>), ExecError> {
    let mut constraints = Vec::new();

    match ty {
        Ty::Enum(enum_name) => {
            // 对于枚举类型，返回所有可能的枚举值
            if let Some(members) = shared_state.type_info.enums.get(enum_name) {
                let num_members = members.len();
                let mut values = Vec::new();

                for i in 0..num_members {
                    // 使用默认方式创建枚举值
                    let enum_id = crate::smt::EnumId::from_name(*enum_name);
                    let enum_member = crate::smt::EnumMember { enum_id, member: i };
                    let member_val = Val::Enum(enum_member);
                    // 获取成员名称
                    let member_name = members.iter().nth(i).copied().unwrap_or(*enum_name);
                    let member_name_str = shared_state.symtab.to_str(member_name);
                    constraints.push((member_name_str.to_string(), format!("enum({})", member_name_str)));
                    values.push(member_val);
                }

                Ok((values, constraints))
            } else {
                Ok((vec![Val::Poison], vec![]))
            }
        }
        Ty::Struct(struct_name) => {
            // 对于结构体类型，检查是否有枚举字段
            if let Some(struct_def) = shared_state.type_info.structs.get(struct_name) {
                // 收集所有枚举字段
                let enum_fields: Vec<_> =
                    struct_def.iter().filter(|(_, field_ty)| matches!(field_ty, Ty::Enum(_))).collect();

                if !enum_fields.is_empty() {
                    // 有枚举字段，需要生成所有可能的组合
                    let mut combinations = vec![ahash::HashMap::<Name, Val<B>>::default()];

                    for (field_name, field_ty) in enum_fields {
                        if let Ty::Enum(enum_name) = field_ty {
                            if let Some(members) = shared_state.type_info.enums.get(enum_name) {
                                let num_members = members.len();
                                let enum_id = crate::smt::EnumId::from_name(*enum_name);

                                let mut new_combinations = Vec::new();
                                for mut combo in combinations.drain(..) {
                                    for i in 0..num_members {
                                        let enum_member = crate::smt::EnumMember { enum_id, member: i };
                                        let member_val = Val::Enum(enum_member);
                                        combo.insert(*field_name, member_val);
                                        new_combinations.push(combo.clone());
                                    }
                                }
                                combinations = new_combinations;
                            }
                        }
                    }

                    // 为非枚举字段添加默认值
                    let mut values = Vec::new();
                    for mut combo in combinations {
                        for (field_name, field_ty) in struct_def {
                            if !combo.contains_key(field_name) {
                                combo.insert(*field_name, generate_default_value(field_ty, shared_state));
                            }
                        }
                        values.push(Val::Struct(combo));
                    }

                    Ok((values, constraints))
                } else {
                    // 没有枚举字段，使用默认值
                    let val = generate_default_value(ty, shared_state);
                    Ok((vec![val], constraints))
                }
            } else {
                let val = generate_default_value(ty, shared_state);
                Ok((vec![val], constraints))
            }
        }
        _ => {
            // 对于其他类型，使用默认值（不使用符号化值，因为会导致跨solver上下文问题）
            let val = generate_default_value(ty, shared_state);
            Ok((vec![val], constraints))
        }
    }
}

/// 根据类型生成符号化值
/// 返回 (符号化值, 约束列表: (变量名, 类型描述))
pub fn generate_symbolic_value<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    use crate::primop_util::symbolic;

    Ok(symbolic(ty, shared_state, solver, info)?)
}

/// 获取指令的所有可能汇编名称
/// 探索所有枚举值的可能性，返回所有可能的汇编名称列表
pub fn get_assembly_names_all<B: BV>(
    instruction_name: &str,
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<String> {
    use crate::smt::checkpoint;

    // 查找指令的构造函数名称
    let encoded_name = format!("{}", instruction_name);
    let ctor_name = shared_state.symtab.lookup(&encoded_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));

    let Some(union_members) = instruction_union else {
        panic!("get_assembly_names_all: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        return vec![];
    };

    let mut assembly_names = Vec::new();

    // 使用 enumerate_possible_values 来获取所有可能的值
    {
        // 对于复杂类型，先尝试获取枚举值并探索所有可能性
        if let Ok((arg_values, _constraints)) = enumerate_possible_values(ctor_ty, *shared_state) {
            // 对于每个可能的值，执行一次
            for arg_value in arg_values {
                dlog!("{}：Ctor是有参数的{:?},\n{}", instruction_name, ctor_ty, arg_value.to_str_fmt(shared_state));
                let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value.clone()));

                // 创建新的 solver 和 checkpoint
                let cfg = crate::smt::Config::new();
                let ctx = crate::smt::Context::new(cfg);
                let mut new_solver = Solver::new(&ctx);
                let cp = checkpoint(&mut new_solver);

                let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
                let collected: Vec<Val<B>> = Vec::new();
                let collected = Arc::new(collected);

                crate::executor::execute_ir_function_with_checkpoint(
                    "zassembly_forwards",
                    &[instr_value],
                    shared_state,
                    regs,
                    lets,
                    &collected,
                    &|_thread, _task_id, exec_result, shared_state, _solver, _collected| match exec_result {
                        Ok((run, _frame)) => {
                            if let Run::Finished(ret_val) = run {
                                *result.lock().unwrap() = Some(ret_val);
                            }
                        }
                        Err((error, backtrace)) => match &error {
                            ExecError::MatchFailure(_) => {}
                            _ => {
                                eprintln!("执行错误: {:?}", error);
                                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                            }
                        },
                    },
                    cp,
                );

                let res = { result.lock().unwrap().as_ref().cloned() };
                if let Some(Val::String(s)) = &res {
                    assembly_names.push(s.clone());
                }
            }
        }
    }

    assembly_names
}

/// 获取zassembly_forwards函数的执行结果
/// 传入指令名称，返回对应的汇编名称
/// 使用checkpoint机制来共享符号化变量
pub fn get_assembly_name<B: BV>(
    instruction_name: &str,
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Vec<String> {
    use crate::smt::checkpoint;

    // 查找指令的构造函数名称
    let encoded_name = format!("{}", instruction_name);
    let ctor_name = shared_state.symtab.lookup(&encoded_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));

    let Some(union_members) = instruction_union else {
        panic!("get_assembly_names_all: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        return vec![];
    };

    let mut assembly_names = Vec::new();

    // 使用 enumerate_possible_values 来获取所有可能的值
    {
        // 对于复杂类型，先尝试获取枚举值并探索所有可能性
        if let Ok((arg_values, _constraints)) = enumerate_possible_values(ctor_ty, *shared_state) {
            // 对于每个可能的值，执行一次
            for arg_value in arg_values {
                dlog!("{}：Ctor是有参数的{:?},\n{}", instruction_name, ctor_ty, arg_value.to_str_fmt(shared_state));
                let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value.clone()));

                // 创建新的 solver 和 checkpoint
                let cfg = crate::smt::Config::new();
                let ctx = crate::smt::Context::new(cfg);
                let mut new_solver = Solver::new(&ctx);
                let cp = checkpoint(&mut new_solver);

                let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
                let collected: Vec<Val<B>> = Vec::new();
                let collected = Arc::new(collected);

                crate::executor::execute_ir_function_with_checkpoint(
                    "zassembly_forwards",
                    &[instr_value],
                    shared_state,
                    regs,
                    lets,
                    &collected,
                    &|_thread, _task_id, exec_result, shared_state, _solver, _collected| match exec_result {
                        Ok((run, _frame)) => {
                            if let Run::Finished(ret_val) = run {
                                *result.lock().unwrap() = Some(ret_val);
                            }
                        }
                        Err((error, backtrace)) => match &error {
                            ExecError::MatchFailure(_) => {}
                            _ => {
                                eprintln!("执行错误: {:?}", error);
                                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                            }
                        },
                    },
                    cp,
                );

                let res = { result.lock().unwrap().as_ref().cloned() };
                if let Some(Val::String(s)) = &res {
                    assembly_names.push(s.clone());
                }
            }
        }
    }

    assembly_names
}
/* /// 提取类型的参数信息，返回 (参数名列表, 约束列表)
fn extract_type_params<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(Vec<String>, Vec<(String, String)>), ExecError> {
    match ty {
        Ty::Unit => Ok((vec![], vec![])),
        Ty::Struct(struct_name) => {
            let mut param_names = Vec::new();
            let mut all_constraints = Vec::new();

            if let Some(struct_def) = shared_state.type_info.structs.get(struct_name) {
                for (field_name, field_ty) in struct_def {
                    let field_name_str = shared_state.symtab.to_str(*field_name).to_string();
                    let (_field_val, field_constraints) = generate_symbolic_value(field_ty, shared_state, solver, info)?;

                    for (var_name, ty_str) in field_constraints {
                        param_names.push(format!("{}.{}", field_name_str, var_name));
                        all_constraints.push((format!("{}.{}", field_name_str, var_name), ty_str));
                    }
                }
            }

            Ok((param_names, all_constraints))
        }
        _ => {
            let (val, constraints) = generate_symbolic_value(ty, shared_state, solver, info)?;
            let param_names = constraints.iter().map(|(name, _)| name.clone()).collect();
            Ok((param_names, constraints))
        }
    }
}

pub fn get_instruction_list<B: BV>(
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
)  -> HashMap<String, (Name, Ty<Name>, String, Vec<String>, Vec<(String, String)>)> {
    use crate::smt::{Config, Context, Solver};

        let mut results: Vec<(Option<String>, (Name, Ty<Name>, String, Vec<String>, Vec<(String, String)>))> = Vec::new();

    for (n, ty) in shared_state.type_info.unions.get(
        &shared_state.symtab.lookup("zinstruction")
    ).unwrap().iter() {
        let inst_union_name_str = String::from_str(shared_state.symtab.to_str(*n)).unwrap();
        let s = &inst_union_name_str;

        // 生成参数和约束
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::new(&ctx);
        let info = SourceLoc::unknown();

        // 获取所有可能的汇编名称
        let assembly_names = get_assembly_names_all(s, shared_state, regs, lets);

        // 获取参数类型信息
        let (params, constraints) = extract_type_params(ty, shared_state, &mut solver, info).unwrap_or((vec![], vec![]));

        // 检查是否有汇编名称
        let has_assembly = !assembly_names.is_empty();

        // 为每个汇编名称创建一个条目
        for assembly_name in assembly_names {
            results.push((
                Some(assembly_name.clone()),
                (*n, ty.clone(), inst_union_name_str.clone(), params.clone(), constraints.clone())
            ));
        }

        // 如果没有找到任何汇编名称，仍然记录这个指令（使用None）
        if !has_assembly {
            results.push((
                None,
                (*n, ty.clone(), inst_union_name_str.clone(), params, constraints)
            ));
        }
    }

    // 找出没有汇编名称的指令
    let no_assembly: Vec<_> = results.iter()
        .filter(|(asm, _)| asm.is_none())
        .map(|(_, (_n, _ty, inst_union_name_str, _params, _constraints))| inst_union_name_str.clone())
        .collect();

    if !no_assembly.is_empty() {
        eprintln!("警告: 以下 {} 个指令没有汇编名称映射:", no_assembly.len());
        for name in &no_assembly {
            // 调试：检查指令类型
            if let Some(union_members) = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")) {
                if let Some((_, ty)) = union_members.iter().find(|(n, _)| shared_state.symtab.to_str(*n) == *name) {
                    eprintln!("  - {} (类型: {:?})", name, ty);
                } else {
                    eprintln!("  - {} (不在 union 中)", name);
                }
            }
        }
    }

    let instruction_list = results.iter().filter_map(
            |(k, v)|
                k.as_ref().map(|key| (key.clone(), v.clone()))
        ).collect::<HashMap<_,_>>();

    instruction_list
}
 */

#[cfg(feature = "debug_instruction")]
pub fn test_instruction_list_main<B: BV>(
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) {
    println!("test_instruction_list_main");

    let assembly_names = get_assembly_names_all("zECALL", shared_state, regs, lets);

    println!("{:?}", assembly_names);
    ()
}
