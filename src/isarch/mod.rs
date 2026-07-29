pub mod args;
pub mod args_yaml;
pub mod clause;
pub mod exec;
pub mod memory_builder;
pub mod target;
mod timeout_report;

use crate::isarch::args::{ArgStruct, InstructionMap};
use isla_lib::bitvector::BV;
use isla_lib::dprint::colors;
use isla_lib::error::ExecError;
use isla_lib::executor::{backtrace_string, execute_ir_function, LocalFrame, Run};
use isla_lib::ir::UVal;
use isla_lib::register::RegisterBindings;
use isla_lib::smt::{checkpoint, Config, Context, Model};
use isla_lib::smt::{Checkpoint, Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::{dlog, log, zencode};
use isla_lib::{ir::*, smt};
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

fn configure_nested_timeout_smt_dump<'ir, B: BV>(
    error: &ExecError,
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
) {
    frame.configure_timeout_smt_dump(error, shared_state);
}

/**
 * instruction list gen
 */
pub fn get_assembly_name<B: BV>(
    arg: Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<String> {
    try_get_assembly_name(arg, shared_state, regs, lets)
        .unwrap_or_else(|error| panic!("get_assembly_name failed: {}", error))
}

pub fn try_get_assembly_name<B: BV>(
    arg: Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<String>, ExecError> {
    // 根据构造函数的参数类型生成默认值
    let arg_value = arg;

    // 执行 zassembly_forwards 函数
    // MatchFailure 错误会被 execute_ir_function 静默处理
    let collected: Arc<Mutex<Option<Result<Val<B>, ExecError>>>> = Arc::new(Mutex::new(None));
    execute_ir_function(
        "zassembly_forwards",
        &[arg_value],
        shared_state,
        regs,
        lets,
        &collected,
        &|_thread, _task_id, exec_result, shared_state, solver, collected| match exec_result {
            Ok((run, frame)) => {
                if let Run::Finished(ret_val) = run {
                    match print_frame_args("zassembly_forwards", &frame, shared_state, solver) {
                        Ok(()) => *collected.lock().unwrap() = Some(Ok(ret_val)),
                        Err(error) => {
                            configure_nested_timeout_smt_dump(&error, &frame, shared_state);
                            *collected.lock().unwrap() = Some(Err(error));
                        }
                    }
                }
            }
            Err((error, frame)) => match error {
                ExecError::MatchFailure(_) => {}
                error @ (ExecError::Timeout | ExecError::Smt(_)) => {
                    configure_nested_timeout_smt_dump(&error, &frame, shared_state);
                    *collected.lock().unwrap() = Some(Err(error));
                }
                error => {
                    log!(log::SYM_EXEC, &format!("执行错误: {:?}", error));
                    log!(
                        log::SYM_EXEC,
                        &format!("调用栈: {:?}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                    );
                }
            },
        },
    );
    let ret_val = collected.lock().unwrap().take().transpose()?;
    Ok(ret_val.and_then(|val| match val {
        Val::String(s) => Some(s),
        _ => {
            eprint!("Warning: get_assembly_name中，zassembly_forwards返回值非字符串");
            None
        }
    }))
}

fn get_assembly_encdec_forwards<B: BV>(
    function_name: &'static str,
    arg: Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<Val<B>>, ExecError> {
    let collected: Arc<Mutex<Option<Result<Val<B>, ExecError>>>> = Arc::new(Mutex::new(None));
    execute_ir_function(
        function_name,
        &[arg],
        shared_state,
        regs,
        lets,
        &collected,
        &|_thread, _task_id, exec_result, shared_state, solver, collected| match exec_result {
            Ok((run, frame)) => {
                if let Run::Finished(ret_val) = run {
                    match print_frame_args(function_name, &frame, shared_state, solver) {
                        Ok(()) => *collected.lock().unwrap() = Some(Ok(ret_val)),
                        Err(error) => {
                            configure_nested_timeout_smt_dump(&error, &frame, shared_state);
                            *collected.lock().unwrap() = Some(Err(error));
                        }
                    }
                }
            }
            Err((error, frame)) => match error {
                ExecError::MatchFailure(_) => {}
                error @ (ExecError::Timeout | ExecError::Smt(_)) => {
                    configure_nested_timeout_smt_dump(&error, &frame, shared_state);
                    *collected.lock().unwrap() = Some(Err(error));
                }
                error => {
                    log!(log::SYM_EXEC, &format!("执行错误: {:?}", error));
                    log!(
                        log::SYM_EXEC,
                        &format!("调用栈: {:?}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                    );
                }
            },
        },
    );
    let result = collected.lock().unwrap().take().transpose();
    result
}

pub fn get_assembly_encdec<B: BV>(
    arg: Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<Val<B>> {
    try_get_assembly_encdec(arg, shared_state, regs, lets)
        .unwrap_or_else(|error| panic!("get_assembly_encdec failed: {}", error))
}

pub fn try_get_assembly_encdec<B: BV>(
    arg: Val<B>,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<Option<Val<B>>, ExecError> {
    match get_assembly_encdec_forwards("zencdec_forwards", arg.clone(), shared_state, regs, lets)? {
        Some(value) => Ok(Some(value)),
        None => get_assembly_encdec_forwards("zencdec_compressed_forwards", arg, shared_state, regs, lets),
    }
}

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
                Val::Enum(isla_lib::smt::EnumId::from_name(*enum_name).first_member())
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
pub fn get_default_arg_all<'ir, B: BV>(
    instruction_name: &str, //like "zRTYPE/zMRET/zSTORE"
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<ArgStruct<'ir, B>> {
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

    // 使用 enumerate_possible_values 来获取所有可能的值

    // 对于复杂类型，先尝试获取枚举值并探索所有可能性

    let val = generate_default_value(ctor_ty, &shared_state);
    vec![ArgStruct::new(val, Some(instruction_name.to_string()), Checkpoint::new(), &shared_state)]
}

/// 打印 frame 中函数参数的符号变量值
fn print_frame_args<B: BV>(
    function_name: &str,
    frame: &LocalFrame<B>,
    shared_state: &SharedState<B>,
    mut solver: Solver<B>,
) -> Result<(), ExecError> {
    let mut found = false;

    // 首先调用 check_sat 来确保 solver 有可用的模型
    match solver.check_sat(SourceLoc::unknown()) {
        isla_lib::smt::SmtResult::Sat => (),
        isla_lib::smt::SmtResult::Error(error) => {
            return Err(ExecError::Smt(error));
        }
        isla_lib::smt::SmtResult::Unsat | isla_lib::smt::SmtResult::Unknown => {
            dlog!("  符号求解失败: UNSAT 或 UNKNOWN");
            return Ok(());
        }
    }

    let mut model = Model::new(&solver);

    // 获取函数的参数名
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, _, _) = shared_state.functions.get(&function_id).unwrap();
    for (arg_name, _arg_ty) in func_args.iter() {
        if let Some(uval) = frame.vars().get(arg_name) {
            if let UVal::Init(val) = uval {
                // 递归查找符号变量
                let mut syms = Vec::new();
                collect_syms(val, &mut syms);
                if !syms.is_empty() {
                    if !found {
                        dlog!("=== 函数参数符号变量求解结果 [{}] ===", function_name);
                        found = true;
                    }
                    let arg_name_str = shared_state.symtab.to_str(*arg_name);
                    dlog!("  {} = {}", arg_name_str, val.to_str_fmt(shared_state));

                    // 求解每个符号变量的值
                    for sym in &syms {
                        match model.get_var(*sym) {
                            Ok(model_val) => match model_val {
                                isla_lib::smt::ModelVal::Exp(exp) => {
                                    dlog!("    |||Sym({:?}) = {:?}", sym, exp);
                                }
                                isla_lib::smt::ModelVal::Arbitrary(ty) => {
                                    dlog!("    Sym({:?}) = Arbitrary ({:?})", sym, ty);
                                }
                            },
                            Err(e @ ExecError::Smt(_)) => return Err(e),
                            Err(e) => {
                                dlog!("    Sym({:?}) = Error: {:?}", sym, e);
                            }
                        }
                    }
                }
            }
        }
    }

    if found {
        dlog!("==============================");
    }
    Ok(())
}

/// 收集符号变量
fn collect_syms<B: BV>(val: &Val<B>, syms: &mut Vec<Sym>) {
    match val {
        Val::Symbolic(s) => {
            if !syms.contains(s) {
                syms.push(*s);
            }
        }
        Val::MixedBits(segs) => {
            for seg in segs {
                if let BitsSegment::Symbolic(s) = seg {
                    if !syms.contains(s) {
                        syms.push(*s);
                    }
                }
            }
        }
        Val::Vector(vs) | Val::List(vs) => {
            for v in vs {
                collect_syms(v, syms);
            }
        }
        Val::Struct(fields) => {
            for (_, v) in fields {
                collect_syms(v, syms);
            }
        }
        Val::Ctor(_, v) => {
            collect_syms(v, syms);
        }
        _ => {}
    }
}

/// 枚举类型的所有可能值
/// 对于枚举类型，返回所有可能的值；对于其他类型，返回包含单个默认值的向量
pub fn enumerate_possible_values<'ir, B: BV>(
    clause_name: Option<&str>,
    ty: &Ty<Name>,
    shared_state: &'ir SharedState<'ir, B>,
) -> Result<(Vec<ArgStruct<'ir, B>>, Vec<(String, String)>), ExecError> {
    let mut constraints = Vec::new();

    match ty {
        Ty::Enum(enum_name) => {
            // 对于枚举类型，返回所有可能的枚举值
            if let Some(members) = shared_state.type_info.enums.get(enum_name) {
                let num_members = members.len();
                let mut values = Vec::new();

                //num_members是enum可能取值的个数，对每一种取值进行遍历
                for i in 0..num_members {
                    //为每一种enum取值可能性创建一个独立solver/checkpoint
                    let mut cfg = Config::new();
                    cfg.set_param_value("model", "true");
                    let ctx = Context::new(cfg);
                    let mut solver = Solver::new(&ctx);
                    // 使用默认方式创建枚举值
                    let enum_id = isla_lib::smt::EnumId::from_name(*enum_name);
                    let enum_member = isla_lib::smt::EnumMember { enum_id, member: i };
                    let member_val = Val::Enum(enum_member);
                    // 获取成员名称
                    let member_name = members.iter().nth(i).copied().unwrap_or(*enum_name);
                    let member_name_str = shared_state.symtab.to_str(member_name);
                    constraints.push((member_name_str.to_string(), format!("enum({})", member_name_str)));
                    values.push((member_val, checkpoint(&mut solver)));
                }

                Ok((
                    values.into_iter().map(|t| ArgStruct::from_tuple(t, clause_name, shared_state)).collect(),
                    constraints,
                ))
            } else {
                panic!("Enum {}{} not found", enum_name.to_str(shared_state), enum_name);
                //Ok((vec![Val::Poison], vec![]))
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
                                let enum_id = isla_lib::smt::EnumId::from_name(*enum_name);

                                let mut new_combinations = Vec::new();
                                for mut combo in combinations.drain(..) {
                                    for i in 0..num_members {
                                        let enum_member = isla_lib::smt::EnumMember { enum_id, member: i };
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
                        //为每一种enum取值可能性创建一个独立solver/checkpoint
                        let mut cfg = Config::new();
                        cfg.set_param_value("model", "true");
                        let ctx = Context::new(cfg);
                        let mut solver = Solver::new(&ctx);
                        //把值加进去
                        for (field_name, field_ty) in struct_def {
                            if !combo.contains_key(field_name) {
                                combo.insert(
                                    *field_name,
                                    generate_symbolic_value(field_ty, shared_state, &mut solver, SourceLoc::unknown())?,
                                );
                            }
                        }
                        values.push((Val::Struct(combo), checkpoint(&mut solver)));
                    }

                    Ok((
                        values.into_iter().map(|t| ArgStruct::from_tuple(t, clause_name, shared_state)).collect(),
                        constraints,
                    ))
                } else {
                    // 没有枚举字段，使用默认值
                    let mut cfg = Config::new();
                    cfg.set_param_value("model", "true");
                    let ctx = Context::new(cfg);
                    let mut solver = Solver::new(&ctx);

                    let val = generate_symbolic_value(ty, shared_state, &mut solver, SourceLoc::unknown())?;

                    //没有枚举，所以只有一种情况
                    let values = vec![(val, checkpoint(&mut solver))];
                    Ok((
                        values.into_iter().map(|t| ArgStruct::from_tuple(t, clause_name, shared_state)).collect(),
                        constraints,
                    ))
                }
            } else {
                let mut cfg = Config::new();
                cfg.set_param_value("model", "true");
                let ctx = Context::new(cfg);
                let mut solver = Solver::new(&ctx);

                let val = generate_symbolic_value(ty, shared_state, &mut solver, SourceLoc::unknown())?;

                //没有枚举，所以只有一种情况
                let values = vec![(val, checkpoint(&mut solver))];
                Ok((
                    values.into_iter().map(|t| ArgStruct::from_tuple(t, clause_name, shared_state)).collect(),
                    constraints,
                ))
            }
        }
        Ty::Unit => {
            let mut cfg = Config::new();
            cfg.set_param_value("model", "true");
            let ctx = Context::new(cfg);
            let mut solver = Solver::new(&ctx);

            let val = generate_symbolic_value(ty, shared_state, &mut solver, SourceLoc::unknown())?;

            //没有枚举，所以只有一种情况
            let values = vec![(val, checkpoint(&mut solver))];
            Ok((values.into_iter().map(|t| ArgStruct::from_tuple(t, clause_name, shared_state)).collect(), constraints))
        }
        _ => {
            // 对于其他类型，如果有就pannic
            panic!("TODO enumerate_possible_values: Ctor参数类型({:?})枚举化未实现", ty);
            /* let val = generate_default_value(ty, shared_state);
            Ok((vec![val], constraints)) */
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
    use isla_lib::primop_util::symbolic;

    symbolic(ty, shared_state, solver, info)
}

pub fn get_symbolic_arg_all<'ir, B: BV>(
    instruction_name: &str, //like "zRTYPE/zMRET/zSTORE"
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<ArgStruct<'ir, B>> {
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

    // 使用 enumerate_possible_values 来获取所有可能的值

    // 对于复杂类型，先尝试获取枚举值并探索所有可能性
    let (arg_values_and_checkpoints, _constraints) =
        enumerate_possible_values(Some(instruction_name), ctor_ty, shared_state).unwrap();

    arg_values_and_checkpoints
}
/// 获取指令的所有可能汇编名称
/// 探索所有枚举值的可能性，返回所有可能的汇编名称列表
pub fn get_assembly_names_all<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<String> {
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

    // 对于复杂类型，先尝试获取枚举值并探索所有可能性
    let arg_values_and_checkpoints = get_symbolic_arg_all(instruction_name, shared_state, regs, lets);
    // 对于每个可能的值，执行一次
    for ArgStruct { arg_value, checkpoint, .. } in arg_values_and_checkpoints {
        dlog!("{}：Ctor是有参数的{:?},\n{}", instruction_name, ctor_ty, arg_value.to_str_fmt(shared_state));
        let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value.clone()));

        // 创建新的 solver 和 checkpoint
        //let cfg = crate::smt::Config::new();
        //let ctx = crate::smt::Context::new(cfg);
        //let mut new_solver = Solver::new(&ctx);
        //let cp = checkpoint(&mut new_solver);

        let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
        let collected: Vec<_> = Vec::new();
        let collected: Arc<Mutex<Vec<_>>> = Arc::new(Mutex::new(collected));

        isla_lib::executor::execute_ir_function_with_checkpoint(
            "zassembly_forwards",
            &[instr_value],
            shared_state,
            regs,
            lets,
            &collected,
            &|_thread, _task_id, exec_result, shared_state, solver, collected| match exec_result {
                Ok((run, frame)) => {
                    if let Run::Finished(ret_val) = run {
                        dlog!(
                            "||||:_thread={:?},_task_id={:?},Ok((Run::Finished(ret_val:{}), _frame)) ",
                            _thread,
                            _task_id,
                            ret_val.clone().to_str_fmt(&shared_state)
                        );
                        if let Err(error) = print_frame_args("zassembly_forwards", &frame, shared_state, solver) {
                            log!(log::SYM_EXEC, &format!("zassembly_forwards 参数求解失败: {}", error));
                        }
                        collected.lock().unwrap().push(ret_val.clone().to_str_fmt(&shared_state));
                        *result.lock().unwrap() = Some(ret_val);
                    }
                }
                Err((error, frame)) => match &error {
                    ExecError::MatchFailure(_) => {}
                    _ => {
                        log!(log::SYM_EXEC, &format!("执行错误: {:?}", error));
                        log!(
                            log::SYM_EXEC,
                            &format!("调用栈: {:?}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                        );
                    }
                },
            },
            checkpoint.clone(),
            None,
        );

        /*let res = { result.lock().unwrap().as_ref().cloned() };
        if let Some(Val::String(s)) = &res {
            assembly_names.push(s.clone());
        }*/
        assembly_names.extend(collected.lock().unwrap().drain(..));
    }

    assembly_names
}

#[allow(non_snake_case)]
pub fn ir_assembly_names_to_InstructionMap_step1_symbolic_exec<'ir, B: BV>(
    instruction_name: &str,
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<(String, ArgStruct<'ir, B>)> {
    // 查找指令的构造函数名称
    let encoded_name = format!("{}", instruction_name);
    let ctor_name = shared_state.symtab.lookup(&encoded_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));

    let Some(union_members) = instruction_union else {
        panic!("get_assembly_names_all: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let (_, ctor_ty) = union_members.iter().find(|(n, _ty)| *n == ctor_name).unwrap();

    let mut arg_structs = Vec::new();

    // 使用 enumerate_possible_values 来获取所有可能的值

    // 对于复杂类型，先尝试获取枚举值并探索所有可能性
    let arg_values_and_checkpoints = get_symbolic_arg_all(instruction_name, shared_state, regs, lets);
    // 对于每个可能的值，执行一次
    for ArgStruct { arg_value, checkpoint, .. } in arg_values_and_checkpoints {
        // clone arg_value 以避免闭包中的生命周期问题
        let arg_value = arg_value.clone();
        dlog!("{}：Ctor是有参数的{:?},\n{}", instruction_name, ctor_ty, arg_value.to_str_fmt(shared_state));
        let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value.clone()));

        // 闭包只收集 (assembly_str, checkpoint)，不包含 shared_state 引用
        let collected: Arc<Mutex<Vec<(String, Checkpoint<B>)>>> = Arc::new(Mutex::new(Vec::new()));

        isla_lib::executor::execute_ir_function_with_checkpoint(
            "zassembly_forwards",
            &[instr_value],
            &shared_state,
            regs,
            lets,
            &collected,
            &|_thread, _task_id, exec_result, shared_state, mut solver, collected| match exec_result {
                Ok((run, _frame)) => match run {
                    Run::Finished(ret_val) => {
                        dlog!(
                            "||||:_thread={:?},_task_id={:?},Ok((Run::Finished(ret_val:{}), _frame)) ",
                            _thread,
                            _task_id,
                            ret_val.clone().to_str_fmt(&shared_state)
                        );
                        let assembly_str = match ret_val.clone() {
                            Val::String(s) => s,
                            _ => panic!("return value error: {:#?}", &ret_val),
                        };

                        /* if solver.check_sat(SourceLoc::unknown()) != isla_lib::smt::SmtResult::Sat {
                            dlog!("  符号求解失败: UNSAT 或 UNKNOWN");
                            return;
                        }
                        let mut model = Model::new(&solver); */
                        match arg_value.clone() {
                            Val::Struct(map) => {
                                dlog!(
                                    colors::YELLOW,
                                    "{:#?}",
                                    map.iter()
                                        .map(|(n, v)| (zencode::decode(&n.to_str(&shared_state)), v))
                                        .collect::<HashMap<_, _>>()
                                );
                            }
                            Val::Unit => {
                                dlog!(colors::YELLOW, "Unit",);
                            }
                            _ => {
                                panic!("TODO: 未考虑周全的参数类型{}:\n{:#?}", arg_value.type_string(), &arg_value);
                            }
                        }
                        let cp = smt::checkpoint(&mut solver);
                        // 只收集 (assembly_str, checkpoint)，不在闭包内创建 ArgStruct
                        collected.lock().unwrap().push((assembly_str, cp));
                    }
                    _ => {
                        log!(
                            log::PATH_RESULT,
                            &format!(
                                "执行异常终止: {}",
                                match run {
                                    Run::Dead => "Run::Dead",
                                    Run::Exit => "Run::Exit",
                                    Run::Suspended => "Run::Suspended",
                                    _ => "Unkown type",
                                }
                            )
                        );
                    }
                },
                Err((error, frame)) => match &error {
                    ExecError::MatchFailure(_) => {}
                    _ => {
                        log!(log::SYM_EXEC, &format!("执行错误: {:?}", error));
                        log!(
                            log::SYM_EXEC,
                            &format!("调用栈: {:?}", backtrace_string(frame.backtrace(), &shared_state.symtab))
                        );
                    }
                },
            },
            checkpoint.clone(),
            None,
        );

        /*let res = { result.lock().unwrap().as_ref().cloned() };
        if let Some(Val::String(s)) = &res {
            assembly_names.push(s.clone());
        }*/
        // 将收集到的 (assembly_str, checkpoint) 转换为 ArgStruct 并收集

        for (assembly_str, cp) in collected.lock().unwrap().drain(..) {
            let arg_struct = ArgStruct::new(arg_value.clone(), Some(instruction_name.to_string()), cp, shared_state);
            arg_structs.push((assembly_str, arg_struct));
        }
    }

    arg_structs
}
#[allow(non_snake_case)]
pub fn ir_assembly_names_to_InstructionMap_step2_merge<'ir, B: BV>(
    instruction_name: &str,
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    arg_structs: Vec<(String, ArgStruct<'ir, B>)>,
) -> InstructionMap<'ir, B> {
    let arg_structs_splited: Vec<(Option<&str>, &ArgStruct<'ir, B>)> = arg_structs
        .iter()
        .map(|(assembly_str, arg_struct)| (assembly_str.split_whitespace().next(), arg_struct))
        .collect::<Vec<_>>();

    let mut arg_structs_merged: Vec<(String, Vec<ArgStruct<'ir, B>>)> = Vec::new();
    let mut clause_has_no_inst_name: HashSet<String> = HashSet::new();

    for (inst_name_option, arg_struct) in arg_structs_splited {
        //在arg_structs_merged的key中，如果inst_name_option在里面没找到，说明是个新的，整个inst_name_and_arg_struct加进arg_structs_merged；
        //如果找到了，说明表里面有，就把arg_struct加到inst_name_option那一条里面去

        if let Some(inst_name) = inst_name_option {
            // 查找是否已存在该指令名
            if let Some(existing_entry) = arg_structs_merged.iter_mut().find(|(name, _)| name == inst_name) {
                // 找到了，把 arg_struct 加进去
                existing_entry.1.push(arg_struct.clone());
            } else {
                // 没找到，创建新条目
                arg_structs_merged.push((inst_name.to_string(), vec![arg_struct.clone()]));
            }
        } else {
            clause_has_no_inst_name.insert(arg_struct.clause_name.clone().unwrap());
        }
    }

    log!(log::ARCH_INFO, &format!("警告: 以下 {} 个指令没有汇编名称映射:", clause_has_no_inst_name.len()));
    clause_has_no_inst_name.iter().for_each(|name| {
        log!(log::ARCH_INFO, &format!("  - {}", name));
    });
    InstructionMap::from_vec_with_shared_state(&arg_structs_merged, &shared_state)
}
///给yaml用的
#[allow(non_snake_case)]
pub fn ir_assembly_names_to_InstructionMap<'ir, B: BV>(
    instruction_name: &str,
    shared_state: &'ir SharedState<'ir, B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> InstructionMap<'ir, B> {
    let step1_ret = ir_assembly_names_to_InstructionMap_step1_symbolic_exec(instruction_name, shared_state, regs, lets);
    let step2_ret =
        ir_assembly_names_to_InstructionMap_step2_merge(instruction_name, shared_state, regs, lets, step1_ret);
    step2_ret
}
/// 提取类型的参数信息，返回 (参数名列表, 约束列表)
/* fn extract_type_params<B: BV>(
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
 */

/* pub fn get_instruction_list<B: BV>(
    shared_state: &SharedState<B>,
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

pub fn test_instruction_list_main<B: BV>(
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
    clause: &str,
) {
    log!(log::SYM_EXEC, "test_instruction_list_main");

    let assembly_names = get_assembly_names_all(clause, shared_state, regs, lets);

    /* assembly_names.iter().for_each(|name| {
        println!("{}", name);
    }); */
    log!(log::PATH_RESULT, &format!("{:?}", assembly_names));

    ()
}

/// 枚举类型中所有枚举字段的具体值组合，非枚举字段使用具体默认值
/// 不创建 solver/symbolic 值，仅使用具体值
fn enumerate_concrete_values<B: BV>(ty: &Ty<Name>, shared_state: &SharedState<B>) -> Vec<Val<B>> {
    match ty {
        Ty::Unit => vec![Val::Unit],
        Ty::Enum(enum_name) => {
            let Some(members) = shared_state.type_info.enums.get(enum_name) else {
                return vec![Val::Poison];
            };
            let enum_id = isla_lib::smt::EnumId::from_name(*enum_name);
            (0..members.len()).map(|i| Val::Enum(isla_lib::smt::EnumMember { enum_id, member: i })).collect()
        }
        Ty::Struct(struct_name) => {
            let Some(struct_def) = shared_state.type_info.structs.get(struct_name) else {
                return vec![generate_default_value(ty, shared_state)];
            };
            // 找出所有枚举字段
            let enum_fields: Vec<(&Name, &Ty<Name>)> =
                struct_def.iter().filter(|(_, ty)| matches!(ty, Ty::Enum(_))).collect();
            if enum_fields.is_empty() {
                return vec![generate_default_value(ty, shared_state)];
            }
            // 枚举所有枚举组合
            let mut combos: Vec<ahash::HashMap<Name, Val<B>>> = vec![ahash::HashMap::default()];
            for (field_name, _field_ty) in &enum_fields {
                if let Ty::Enum(enum_name) = _field_ty {
                    let Some(members) = shared_state.type_info.enums.get(enum_name) else {
                        continue;
                    };
                    let enum_id = isla_lib::smt::EnumId::from_name(*enum_name);
                    let mut new_combos = Vec::new();
                    for mut combo in combos.drain(..) {
                        for i in 0..members.len() {
                            combo.insert(**field_name, Val::Enum(isla_lib::smt::EnumMember { enum_id, member: i }));
                            new_combos.push(combo.clone());
                        }
                    }
                    combos = new_combos;
                }
            }
            // 对非枚举字段填充默认值
            combos
                .into_iter()
                .map(|mut combo| {
                    for (field_name, field_ty) in struct_def {
                        if !combo.contains_key(field_name) {
                            combo.insert(*field_name, generate_default_value(field_ty, shared_state));
                        }
                    }
                    Val::Struct(combo)
                })
                .collect()
        }
        _ => vec![generate_default_value(ty, shared_state)],
    }
}

/// 从 zinstruction union 中提取所有 clause，对每个 clause 解析汇编指令名
/// 枚举枚举类型参数的所有组合，使用具体默认值快速获取指令名
pub fn list_instructions<B: BV>(
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Vec<(String, Vec<String>)> {
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));
    let Some(union_members) = instruction_union else {
        panic!("list_instructions: 在symtab中没找到符号'zinstruction'");
    };

    let mut clause_names: Vec<String> =
        union_members.iter().map(|(n, _)| shared_state.symtab.to_str(*n).to_string()).collect();
    clause_names.sort();

    let mut result = Vec::new();
    for clause in &clause_names {
        let display_name = zencode::decode(clause).to_string();
        let ctor_name = shared_state.symtab.lookup(clause);

        let Some((_, ctor_ty)) = union_members.iter().find(|(n, _)| *n == ctor_name) else {
            result.push((display_name, vec![]));
            continue;
        };

        let arg_combos = enumerate_concrete_values(ctor_ty, shared_state);

        let mut inst_names: HashSet<String> = HashSet::new();
        for arg_value in &arg_combos {
            let instr_value = Val::Ctor(ctor_name, Box::new(arg_value.clone()));
            if let Some(asm_str) = get_assembly_name(instr_value, shared_state, regs, lets) {
                if let Some(mnemonic) = asm_str.split_whitespace().next() {
                    inst_names.insert(mnemonic.to_string());
                }
            }
        }

        let mut names: Vec<String> = inst_names.into_iter().collect();
        names.sort();
        result.push((display_name, names));
    }
    result
}

/// 获取所有 clause 名称（编码后的原始名称，从 zinstruction union 中提取）
pub fn get_all_clause_names<B: BV>(shared_state: &SharedState<B>) -> Vec<String> {
    let instruction_union = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction"));
    let Some(union_members) = instruction_union else {
        return vec![];
    };
    union_members.iter().map(|(n, _)| shared_state.symtab.to_str(*n).to_string()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::timeout::{SmtDumpNames, SmtDumpSource, SmtOperation, SmtTimeout, TimeoutSmtDump};
    use std::time::Duration;

    struct NamesTimeoutDump;

    impl SmtDumpSource for NamesTimeoutDump {
        fn materialize(&self) -> Result<String, String> {
            panic!("timeout dump test must materialize with configured names")
        }

        fn materialize_with_names(&self, names: &SmtDumpNames) -> Result<String, String> {
            Ok(format!("{:?}", names))
        }
    }

    #[test]
    fn nested_execution_timeout_uses_the_nested_frame_symbol_names() {
        let nested_name_text = zencode::encode("nested_argument");
        let function_text = zencode::encode("test_function");
        let mut symtab = Symtab::new();
        let nested_name = symtab.intern(&nested_name_text);
        let function_name = symtab.intern(&function_text);
        let shared_state: SharedState<B64> = SharedState::empty(symtab);
        let instrs: Vec<Instr<Name, B64>> = vec![];
        let mut nested_frame = LocalFrame::new(function_name, &[], &Ty::Unit, None, &instrs);
        nested_frame.vars_mut().insert(nested_name, UVal::Init(Val::Symbolic(Sym::from_u32(23))));
        let timeout = Arc::new(SmtTimeout {
            source_loc: SourceLoc::unknown(),
            operation: SmtOperation::CheckSat,
            limit: Duration::from_secs(1),
            operation_wall: Duration::from_secs(1),
            dump: Arc::new(TimeoutSmtDump::new(Arc::new(NamesTimeoutDump))),
        });
        let error = ExecError::Smt(isla_lib::error::SmtError::Timeout(timeout.clone()));

        configure_nested_timeout_smt_dump(&error, &nested_frame, &shared_state);

        let dump = timeout.dump.materialize().unwrap();
        assert!(dump.contains("isla_nested_argument__s23"));
    }
}
