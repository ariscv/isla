// BSD 2-Clause License
//
// Copyright (c) 2025
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

//! Instruction architecture exploration module for symbolic execution of RISC-V instructions.

use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::error::ExecError;
use crate::executor::{backtrace_string, execute_ir_function, start_single, Collector, LocalFrame, Run, TaskId, TaskState};
use crate::ir::*;
use crate::register::RegisterBindings;
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::zencode;
use std::collections::HashMap;
use std::str::FromStr;
use std::sync::{Arc, Mutex, Weak};

/**
 * instruction list gen
  */

/// 通用的IR函数执行API
/// 执行指定的IR函数并返回结果
pub fn execute_ir_function_val<B: BV>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &&SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Option<Val<B>> {
    let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));

    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 执行任务
    let collected: Vec<Val<B>> = Vec::new();
    let collected = Arc::new(collected);

    start_single(task, shared_state, &collected, &|_thread, _task_id, exec_result, shared_state, _solver, _collected| {
        match exec_result {
            Ok((run, _frame)) => {
                match run {
                    Run::Finished(ret_val) => {
                        *result.lock().unwrap() = Some(ret_val);
                    }
                    _ => {}
                }
            }
            Err((error, backtrace)) => {
                // MatchFailure 可能由于以下原因发生：
                // 1. IR 文件包含了特定架构的指令（如 RV32 指令在 RV64 IR 中）
                // 2. 这些指令存在于 zinstruction union 中，但在 zassembly_forwards 中没有处理
                // 这是 IR 文件的设计特性，不是代码错误
                match &error {
                    ExecError::MatchFailure(_) => {
                        // 静默处理 - 指令没有汇编名称映射
                    }
                    _ => {
                        eprintln!("执行错误: {:?}", error);
                        eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                    }
                }
            }
        }
    });

    let res = result.lock().unwrap().as_ref().cloned();
    res
}

/// 使用checkpoint执行IR函数
/// 允许在执行前预先设置符号化变量
pub fn execute_ir_function_with_checkpoint<'ir, B: BV, R>(
    function_name: &str,
    args: &[Val<B>],
    shared_state: &&SharedState<'ir,B>,
    regs: &RegisterBindings<'ir,B>,
    lets: &Bindings<'ir,B>,
    collected: &R,
    collector: &Collector<'ir, B, R>,
    checkpoint: Checkpoint<B>,
) {
    // 获取函数信息
    let function_id = shared_state.symtab.lookup(function_name);
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    // 创建初始帧
    let mut initial_frame = LocalFrame::new(function_id, func_args, ret_ty, Some(args), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务，使用传入的checkpoint
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task_with_checkpoint(task_id, &task_state, checkpoint);

    start_single(task, shared_state, collected, collector);

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
            let ahash_fields: ahash::HashMap<Name, Val<B>> =
                fields.into_iter().collect();
            Val::Struct(ahash_fields)
        }
        Ty::Union(_) => Val::Unit, // Union 类型使用第一个构造函数的默认值
        _ => Val::Unit, // 对于其他类型，使用 Unit 作为默认值
    }
}

/// 枚举类型的所有可能值
/// 对于枚举类型，返回所有可能的值；对于其他类型，返回包含单个默认值的向量
pub fn enumerate_possible_values<B: BV>(
    ty: &Ty<Name>,
    shared_state: &SharedState<B>,
    _solver: &mut Solver<B>,
    _info: SourceLoc,
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
                let enum_fields: Vec<_> = struct_def.iter()
                    .filter(|(_, field_ty)| matches!(field_ty, Ty::Enum(_)))
                    .collect();

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
) -> Result<(Val<B>, Vec<(String, String)>), ExecError> {
    use crate::primop_util::symbolic;

    let mut constraints = Vec::new();

    let val = match ty {
        Ty::Unit => Val::Unit,
        Ty::I64 => {
            let val = symbolic(&Ty::I64, shared_state, solver, info)?;
            if let Val::Symbolic(sym) = val {
                constraints.push((format!("x{}", sym), "i64".to_string()));
            }
            val
        }
        Ty::I128 => {
            let val = symbolic(&Ty::I128, shared_state, solver, info)?;
            if let Val::Symbolic(sym) = val {
                constraints.push((format!("x{}", sym), "i128".to_string()));
            }
            val
        }
        Ty::Bool => {
            let val = symbolic(&Ty::Bool, shared_state, solver, info)?;
            if let Val::Symbolic(sym) = val {
                constraints.push((format!("x{}", sym), "bool".to_string()));
            }
            val
        }
        Ty::Bits(n) => {
            let val = symbolic(ty, shared_state, solver, info)?;
            if let Val::Symbolic(sym) = val {
                constraints.push((format!("x{}", sym), format!("bits({})", n)));
            }
            val
        }
        Ty::String => Val::String(String::new()),
        Ty::Vector(elem_ty) => {
            let (elem_val, elem_constraints) = generate_symbolic_value(elem_ty, shared_state, solver, info)?;
            constraints.extend(elem_constraints);
            Val::Vector(vec![elem_val])
        }
        Ty::List(elem_ty) => {
            let (elem_val, elem_constraints) = generate_symbolic_value(elem_ty, shared_state, solver, info)?;
            constraints.extend(elem_constraints);
            Val::List(vec![elem_val])
        }
        Ty::Enum(enum_name) => {
            // 对枚举类型进行符号化
            let enum_name_str = shared_state.symtab.to_str(*enum_name);
            symbolic(ty, shared_state, solver, info)?
        }
        Ty::Struct(struct_name) => {
            let mut fields: std::collections::HashMap<Name, Val<B>> = std::collections::HashMap::new();
            if let Some(struct_def) = shared_state.type_info.structs.get(struct_name) {
                for (field_name, field_ty) in struct_def {
                    let (field_val, field_constraints) = generate_symbolic_value(field_ty, shared_state, solver, info)?;
                    let field_name_str = shared_state.symtab.to_str(*field_name);
                    for (var_name, ty_str) in field_constraints {
                        constraints.push((format!("{}.{}", field_name_str, var_name), ty_str));
                    }
                    fields.insert(*field_name, field_val);
                }
            }
            let ahash_fields: ahash::HashMap<Name, Val<B>> = fields.into_iter().collect();
            Val::Struct(ahash_fields)
        }
        Ty::Union(union_name) => {
            // 对Union类型进行符号化
            symbolic(ty, shared_state, solver, info)?
        }
        _ => Val::Unit,
    };

    Ok((val, constraints))
}

/// 获取指令的所有可能汇编名称
/// 探索所有枚举值的可能性，返回所有可能的汇编名称列表
pub fn get_assembly_names_all<B: BV>(
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
    let instruction_union = shared_state.type_info.unions.get(
        &shared_state.symtab.lookup("zinstruction")
    );

    let Some(union_members) = instruction_union else {
        panic!("get_assembly_names_all: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        return vec![];
    };

    let mut assembly_names = Vec::new();

    // 使用 enumerate_possible_values 来获取所有可能的值
    match ctor_ty {
        Ty::Unit => {
            // 无参数，直接执行
            let instr_value = Val::<B>::Ctor(ctor_name, Box::new(Val::Unit));
            let cp = checkpoint(solver);

            let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
            let collected: Vec<Val<B>> = Vec::new();
            let collected = Arc::new(collected);

            execute_ir_function_with_checkpoint(
                "zassembly_forwards",
                &[instr_value],
                shared_state,
                regs,
                lets,
                &collected,
                &|_thread, _task_id, exec_result, shared_state, _solver, _collected| {
                    match exec_result {
                        Ok((run, _frame)) => {
                            if let Run::Finished(ret_val) = run {
                                *result.lock().unwrap() = Some(ret_val);
                            }
                        }
                        Err((error, backtrace)) => {
                            match &error {
                                ExecError::MatchFailure(_) => {}
                                _ => {
                                    eprintln!("执行错误: {:?}", error);
                                    eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                                }
                            }
                        }
                    }
                },
                cp,
            );

            let res = { result.lock().unwrap().as_ref().cloned() };
            if let Some(Val::String(s)) = &res {
                assembly_names.push(s.clone());
            }
        }
        _ => {
            // 对于复杂类型，先尝试获取枚举值并探索所有可能性
            if let Ok((arg_values, _constraints)) = enumerate_possible_values(ctor_ty, *shared_state, solver, info) {
                // 对于每个可能的值，执行一次
                for arg_value in arg_values {
                    let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value.clone()));

                    // 创建新的 solver 和 checkpoint
                    let cfg = crate::smt::Config::new();
                    let ctx = crate::smt::Context::new(cfg);
                    let mut new_solver = Solver::new(&ctx);
                    let cp = checkpoint(&mut new_solver);

                    let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
                    let collected: Vec<Val<B>> = Vec::new();
                    let collected = Arc::new(collected);

                    execute_ir_function_with_checkpoint(
                        "zassembly_forwards",
                        &[instr_value],
                        shared_state,
                        regs,
                        lets,
                        &collected,
                        &|_thread, _task_id, exec_result, shared_state, _solver, _collected| {
                            match exec_result {
                                Ok((run, _frame)) => {
                                    if let Run::Finished(ret_val) = run {
                                        *result.lock().unwrap() = Some(ret_val);
                                    }
                                }
                                Err((error, backtrace)) => {
                                    match &error {
                                        ExecError::MatchFailure(_) => {}
                                        _ => {
                                            eprintln!("执行错误: {:?}", error);
                                            eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                                        }
                                    }
                                }
                            }
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
) -> Option<String> {
    use crate::smt::checkpoint;

    // 查找指令的构造函数名称
    let encoded_name = format!("{}", instruction_name);
    let ctor_name = shared_state.symtab.lookup(&encoded_name);

    // 从 union 类型信息中获取构造函数的参数类型
    let instruction_union = shared_state.type_info.unions.get(
        &shared_state.symtab.lookup("zinstruction")
    );

    let Some(union_members) = instruction_union else {
        // zinstruction union 不存在
		panic!("get_assembly_name: 在symtab中没找到符号'zinstruction'");
    };

    // 查找当前构造函数的类型
    let Some((_, ctor_ty)) = union_members.iter().find(|(n, _ty)| *n == ctor_name) else {
        // 指令不在 zinstruction union 中（可能是其他架构的指令）
        return None;
    };

    // 生成参数（暂时使用默认值，测试checkpoint机制）
    let arg_value = match ctor_ty {
        Ty::Unit => Val::Unit,
        ty => generate_default_value(ty, *shared_state),
    };

    // 构造指令值
    let instr_value = Val::<B>::Ctor(ctor_name, Box::new(arg_value));

    // 创建checkpoint，包含符号化变量
    let cp = checkpoint(solver);

    // 使用checkpoint执行函数
    let result: Arc<Mutex<Option<Val<B>>>> = Arc::new(Mutex::new(None));
    let collected: Vec<Val<B>> = Vec::new();
    let collected = Arc::new(collected);

    execute_ir_function_with_checkpoint(
        "zassembly_forwards",
        &[instr_value],
        shared_state,
        regs,
        lets,
        &collected,
        &|_thread, _task_id, exec_result, shared_state, _solver, _collected| {
            match exec_result {
                Ok((run, _frame)) => {
                    match run {
                        Run::Finished(ret_val) => {
                            *result.lock().unwrap() = Some(ret_val);
                        }
                        _ => {}
                    }
                }
                Err((error, backtrace)) => {
                    match &error {
                        ExecError::MatchFailure(_) => {
                            // 静默处理
                        }
                        _ => {
                            eprintln!("执行错误: {:?}", error);
                            eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
                        }
                    }
                }
            }
        },
        cp,
    );

    // 提取字符串结果
    let res = match result.lock().unwrap().as_ref() {
        Some(Val::String(s)) => Some(s.clone()),
        Some(v) => {
            eprintln!("警告: zassembly_forwards 返回非字符串值: {:?}", v);
            None
        }
        None => None,
    };
    res
}
/// 提取类型的参数信息，返回 (参数名列表, 约束列表)
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
        let assembly_names = get_assembly_names_all(s, shared_state, regs, lets, &mut solver, info);

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



/**
 * 符号执行部分
  */
/// Information about an instruction extracted from the IR
#[derive(Clone, Debug)]
pub struct InstructionInfo {
    /// The encoded name in the IR (e.g., "zMRET")
    pub encoded_name: String,
    /// The assembly name (e.g., "mret")
    pub assembly_name: String,
    /// The function ID in the IR
    pub function_id: Name,
}

/// A condition on an execution path
#[derive(Clone, Debug)]
pub enum PathCondition {
    /// Initial entry point (no condition)
    Initial,
    /// Branch condition
    Branch {
        variable: Sym,
        is_true: bool,
        description: String,
    },
}

/// ISA state snapshot
#[derive(Clone, Debug)]
pub struct ISAState<B> {
    /// General purpose registers
    pub registers: HashMap<Name, Val<B>>,
    /// Control and status registers
    pub csrs: HashMap<String, Val<B>>,
    /// Special registers (PC, privilege level, etc.)
    pub special_regs: HashMap<String, Val<B>>,
}

/// An execution path with conditions and state
#[derive(Clone, Debug)]
pub struct ExecutionPath<B> {
    /// Path identifier
    pub path_id: usize,
    /// Conditions on this path
    pub conditions: Vec<PathCondition>,
    /// ISA state at the end of the path
    pub isa_state: ISAState<B>,
    /// Whether the path is satisfiable
    pub satisfiable: bool,
}

/// Result of solving a path
#[derive(Debug)]
pub enum SolveResult<B> {
    /// Satisfiable with concrete values
    Sat {
        /// Symbolic variable to concrete value mapping
        values: HashMap<String, Val<B>>,
    },
    /// Unsatifiable
    Unsat,
    /// Unknown (solver timeout or other issue)
    Unknown,
}

/// Error during instruction dictionary building
#[derive(Debug)]
pub enum BuildError {
    /// Function not found
    FunctionNotFound(String),
    /// Invalid IR structure
    InvalidIR(String),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            BuildError::FunctionNotFound(name) => write!(f, "Function not found: {}", name),
            BuildError::InvalidIR(msg) => write!(f, "Invalid IR structure: {}", msg),
        }
    }
}

impl std::error::Error for BuildError {}


/// Execute an instruction symbolically and collect execution paths
pub fn execute_instruction<B: BV>(
    instruction: &str,
    shared_state: &SharedState<B>,
    options: &ExecOptions,
) -> Result<Vec<ExecutionPath<B>>, ExecError> {
    // TODO: Implement symbolic execution
    // This will:
    // 1. Find the instruction in the IR
    // 2. Create a task for execution
    // 3. Use executor::start_single to explore paths
    // 4. Collect paths using a custom collector
    Ok(Vec::new())
}

/// 执行树节点
///
/// 表示指令符号执行过程中的一个状态点。节点通过 Arc 共享所有权，
/// 子节点持有父节点的 Weak 引用以避免循环引用。节点身份由其内存地址决定，
/// 不使用数值 ID。
///
/// 内部使用 Mutex 包装的可变状态，以支持运行时动态构建树。
pub struct TreeNode<B> {
    /// 节点类型（根节点、分支节点、路径节点或叶子节点）
    node_type: Mutex<NodeType<B>>,
    /// 父节点的弱引用（根节点为空 Weak）
    parent: Weak<TreeNode<B>>,
    /// 子节点列表
    children: Mutex<Vec<Arc<TreeNode<B>>>>,
}

impl<B> TreeNode<B> {
    /// 创建一个新的根节点
    ///
    /// # 参数
    /// * `node_type` - 节点类型（必须是 NodeType::Root）
    pub fn new_root(node_type: NodeType<B>) -> Arc<Self> {
        Arc::new(TreeNode {
            node_type: Mutex::new(node_type),
            parent: Weak::new(),
            children: Mutex::new(Vec::new()),
        })
    }

    /// 创建一个新的分支节点
    ///
    /// # 参数
    /// * `node_type` - 节点类型
    /// * `parent` - 父节点的 Arc 引用
    pub fn new_with_parent(node_type: NodeType<B>, parent: &Arc<TreeNode<B>>) -> Arc<Self> {
        let node = Arc::new(TreeNode {
            node_type: Mutex::new(node_type),
            parent: Arc::downgrade(parent),
            children: Mutex::new(Vec::new()),
        });

        // 将新节点添加到父节点的子节点列表
        let mut parent_children = parent.children.lock().unwrap();
        parent_children.push(Arc::clone(&node));

        node
    }

    /// 添加一个子节点
    ///
    /// # 参数
    /// * `child` - 要添加的子节点（Arc 包装）
    pub fn add_child(self: &Arc<Self>, child: Arc<TreeNode<B>>) {
        let mut children = self.children.lock().unwrap();
        children.push(child);
    }

    /// 获取父节点（升级弱引用）
    pub fn parent(&self) -> Option<Arc<TreeNode<B>>> {
        self.parent.upgrade()
    }

    /// 获取子节点数量
    pub fn child_count(&self) -> usize {
        let children = self.children.lock().unwrap();
        children.len()
    }

    /// 是否为叶子节点（没有子节点）
    pub fn is_leaf(&self) -> bool {
        self.child_count() == 0
    }

    /// 是否为根节点（没有父节点）
    pub fn is_root(&self) -> bool {
        self.parent.upgrade().is_none()
    }

    /// 获取节点类型（克隆副本）
    pub fn node_type_cloned(&self) -> NodeType<B>
    where
        NodeType<B>: Clone,
    {
        let node_type = self.node_type.lock().unwrap();
        node_type.clone()
    }

    /// 获取子节点列表（克隆）
    pub fn children_cloned(&self) -> Vec<Arc<TreeNode<B>>> {
        let children = self.children.lock().unwrap();
        children.iter().map(Arc::clone).collect()
    }

    /// 对节点类型执行操作
    pub fn with_node_type<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&NodeType<B>) -> R,
    {
        let node_type = self.node_type.lock().unwrap();
        f(&node_type)
    }

    /// 对子节点执行操作
    pub fn with_children<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[Arc<TreeNode<B>>]) -> R,
    {
        let children = self.children.lock().unwrap();
        f(&children)
    }
}

impl<B: std::fmt::Debug> std::fmt::Debug for TreeNode<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let child_count = self.child_count();
        let has_parent = self.parent.strong_count() > 0;
        f.debug_struct("TreeNode")
            .field("child_count", &child_count)
            .field("has_parent", &has_parent)
            .finish()
    }
}

/// 执行树
///
/// 封装根节点并提供了树级别的操作方法，包括遍历、查找、统计和添加节点。
pub struct Tree<B> {
    /// 根节点
    root: Arc<TreeNode<B>>,
}

impl<B> Tree<B> {
    /// 创建一个新的执行树
    ///
    /// # 参数
    /// * `root` - 根节点
    pub fn new(root: Arc<TreeNode<B>>) -> Self {
        Tree { root }
    }

    /// 获取根节点
    pub fn root(&self) -> &Arc<TreeNode<B>> {
        &self.root
    }

    /// 深度优先遍历（DFS）
    ///
    /// # 参数
    /// * `visitor` - 访问者函数，对每个节点调用，返回 true 继续遍历，false 停止
    pub fn dfs<F>(&self, mut visitor: F)
    where
        F: FnMut(&Arc<TreeNode<B>>) -> bool,
    {
        self.dfs_recursive(&self.root, &mut visitor);
    }

    fn dfs_recursive<F>(&self, node: &Arc<TreeNode<B>>, visitor: &mut F)
    where
        F: FnMut(&Arc<TreeNode<B>>) -> bool,
    {
        if !visitor(node) {
            return;
        }
        let children = node.children_cloned();
        for child in &children {
            self.dfs_recursive(child, visitor);
        }
    }

    /// 广度优先遍历（BFS）
    ///
    /// # 参数
    /// * `visitor` - 访问者函数，对每个节点调用，返回 true 继续遍历，false 停止
    pub fn bfs<F>(&self, mut visitor: F)
    where
        F: FnMut(&Arc<TreeNode<B>>) -> bool,
    {
        use std::collections::VecDeque;
        let mut queue = VecDeque::new();
        queue.push_back(Arc::clone(&self.root));

        while let Some(node) = queue.pop_front() {
            if !visitor(&node) {
                break;
            }
            let children = node.children_cloned();
            for child in &children {
                queue.push_back(Arc::clone(child));
            }
        }
    }

    /// 根据条件查找节点
    ///
    /// # 参数
    /// * `predicate` - 谓词函数，返回 true 表示匹配
    /// # 返回
    /// 第一个匹配的节点（Arc 引用）
    pub fn find<F>(&self, predicate: F) -> Option<Arc<TreeNode<B>>>
    where
        F: Fn(&TreeNode<B>) -> bool,
    {
        let mut result = None;
        self.dfs(|node| {
            if predicate(node) {
                result = Some(Arc::clone(node));
                false // 停止遍历
            } else {
                true // 继续遍历
            }
        });
        result
    }

    /// 统计树的总节点数
    pub fn node_count(&self) -> usize {
        let mut count = 0;
        self.dfs(|_| {
            count += 1;
            true
        });
        count
    }

    /// 统计叶子节点数
    pub fn leaf_count(&self) -> usize {
        let mut count = 0;
        self.dfs(|node| {
            if node.is_leaf() {
                count += 1;
            }
            true
        });
        count
    }

    /// 获取树的最大深度
    pub fn max_depth(&self) -> usize {
        self.max_depth_recursive(&self.root)
    }

    fn max_depth_recursive(&self, node: &Arc<TreeNode<B>>) -> usize {
        let children = node.children_cloned();
        if children.is_empty() {
            return 1;
        }
        1 + children
            .iter()
            .map(|child| self.max_depth_recursive(child))
            .max()
            .unwrap_or(0)
    }

    /// 获取所有叶子节点
    pub fn leaves(&self) -> Vec<Arc<TreeNode<B>>> {
        let mut leaves = Vec::new();
        self.dfs(|node| {
            if node.is_leaf() {
                leaves.push(Arc::clone(node));
            }
            true
        });
        leaves
    }

    /// 将树格式化为 ASCII 艺术
    ///
    /// # 参数
    /// * `num_paths` - 执行路径数量（用于显示）
    pub fn format_ascii(&self, num_paths: usize) -> String {
        let mut output = String::new();

        output.push_str(&format!("指令执行树 ({} 条路径):\n", num_paths));
        output.push_str("\n");

        // 递归打印树的辅助函数
        fn print_tree<B>(node: &Arc<TreeNode<B>>, output: &mut String, prefix: &str, is_last: bool) {
            node.with_node_type(|node_type| {
                match node_type {
                    NodeType::Root { instruction } => {
                        output.push_str(&format!("{}📋 指令: {}\n", prefix, instruction));
                    }
                    NodeType::Branch { fork_id, variable, location } => {
                        output.push_str(&format!("{}🔀 分岔 #{}: {} @ {}\n", prefix, fork_id, variable, location));
                    }
                    NodeType::Leaf { satisfiable, constructor_name, unfolded_value, .. } => {
                        let sat_str = if *satisfiable { "✓ 可满足" } else { "✗ 不可满足" };
                        output.push_str(&format!("{}🍁 {} ", prefix, sat_str));
                        if let Some(name) = constructor_name {
                            output.push_str(&format!("(返回: {})", name));
                        }
                        if let Some(unfolded) = unfolded_value {
                            output.push_str(&format!(" => {}", unfolded));
                        }
                        output.push_str("\n");
                    }
                    NodeType::Path { constraints, location, .. } => {
                        output.push_str(&format!("{}📍 路径 @ {}\n", prefix, location));
                        for (i, constraint) in constraints.iter().enumerate() {
                            output.push_str(&format!("{}   约束 {}: {}\n", prefix, i, constraint.format()));
                        }
                    }
                }
            });

            let children = node.children_cloned();
            let child_count = children.len();
            for (i, child) in children.iter().enumerate() {
                let is_last_child = i == child_count - 1;
                let new_prefix = if is_last_child {
                    format!("{}    ", prefix)
                } else {
                    format!("{}│   ", prefix)
                };
                let connector = if is_last_child { "└── " } else { "├── " };
                output.push_str(&format!("{}{}", prefix, connector));
                print_tree(child, output, &new_prefix, is_last_child);
            }
        }

        let root = &self.root;
        let root_children = root.children_cloned();
        print_tree(root, &mut output, "", root_children.len() <= 1);

        output
    }

    /// 将树格式化为 Graphviz DOT 格式
    pub fn format_graphviz(&self) -> String {
        let mut output = String::new();

        output.push_str("digraph ExecutionTree {\n");
        output.push_str("  rankdir=TB;\n");
        output.push_str("  node [shape=box, fontname=\"Courier\"];\n");
        output.push_str("  edge [fontname=\"Courier\"];\n");
        output.push_str("\n");

        // 使用节点指针地址作为唯一 ID
        fn generate_graphviz<B>(
            node: &Arc<TreeNode<B>>,
            output: &mut String,
            parent_id: Option<usize>,
            node_counter: &mut usize,
        ) {
            let current_id = *node_counter;
            *node_counter += 1;

            // 生成节点标签
            let label = node.with_node_type(|node_type| {
                match node_type {
                    NodeType::Root { instruction } => {
                        format!("指令:\\n{}", instruction)
                    }
                    NodeType::Branch { fork_id, variable, location } => {
                        // 缩短位置以增强可读性
                        let loc_short = location.lines().next().unwrap_or("");
                        format!("分岔 #{}:\\n{} @ {}", fork_id, variable, loc_short)
                    }
                    NodeType::Leaf { satisfiable, constructor_name, unfolded_value, .. } => {
                        let sat_str = if *satisfiable { "✓" } else { "✗" };
                        let mut label = format!("{} ", sat_str);
                        if let Some(name) = constructor_name {
                            label.push_str(&format!("返回:\\n{}", name));
                        }
                        if let Some(unfolded) = unfolded_value {
                            label.push_str(&format!("\\n=> {}", unfolded));
                        }
                        label
                    }
                    NodeType::Path { constraints, .. } => {
                        format!("路径\\n({} 个约束)", constraints.len())
                    }
                }
            });

            // 转义标签用于 graphviz
            let label_escaped = label.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n");

            output.push_str(&format!("  node{} [label=\"{}\"];\n", current_id, label_escaped));

            // 从父节点生成边
            if let Some(pid) = parent_id {
                output.push_str(&format!("  node{} -> node{};\n", pid, current_id));
            }

            // 递归处理子节点
            let children = node.children_cloned();
            for child in &children {
                generate_graphviz(child, output, Some(current_id), node_counter);
            }
        }

        let mut node_counter = 0;
        generate_graphviz(&self.root, &mut output, None, &mut node_counter);

        output.push_str("}\n");
        output
    }
}

/// 树节点类型
///
/// 定义了执行树中可能出现的各种节点类型。
#[derive(Clone, Debug)]
pub enum NodeType<B> {
    /// 根节点 - 执行树的入口
    Root {
        /// 正在执行的指令名称
        instruction: String,
    },
    /// 路径节点 - 携带约束条件并追踪数据
    Path {
        /// 此路径上累积的约束条件
        constraints: Vec<PathConstraint>,
        /// 遇到的符号变量
        variables: Vec<String>,
        /// 源代码位置
        location: String,
    },
    /// 分支节点 - 表示执行中的分岔点
    Branch {
        /// 来自执行器的分支 ID
        fork_id: u32,
        /// 被分支的符号变量
        variable: String,
        /// 分支的源代码位置
        location: String,
    },
    /// 叶子节点 - 执行完成，可能需要展开（zexecute 返回构造函数）
    Leaf {
        /// 此路径是否可满足
        satisfiable: bool,
        /// zexecute 的返回值（可能需要进一步执行的构造函数）
        return_value: Option<Val<B>>,
        /// 如果返回值是 Ctor，则为构造函数名称
        constructor_name: Option<String>,
        /// 展开后的值表示（用于显示）
        unfolded_value: Option<String>,
    },
}

impl<B> NodeType<B> {
    /// 获取节点的显示名称
    pub fn display_name(&self) -> &str {
        match self {
            NodeType::Root { .. } => "根节点",
            NodeType::Path { .. } => "路径节点",
            NodeType::Branch { .. } => "分支节点",
            NodeType::Leaf { .. } => "叶子节点",
        }
    }

    /// 判断是否为根节点
    pub fn is_root(&self) -> bool {
        matches!(self, NodeType::Root { .. })
    }

    /// 判断是否为路径节点
    pub fn is_path(&self) -> bool {
        matches!(self, NodeType::Path { .. })
    }

    /// 判断是否为分支节点
    pub fn is_branch(&self) -> bool {
        matches!(self, NodeType::Branch { .. })
    }

    /// 判断是否为叶子节点
    pub fn is_leaf(&self) -> bool {
        matches!(self, NodeType::Leaf { .. })
    }

    /// 获取指令名称（仅对根节点有效）
    pub fn as_root(&self) -> Option<&str> {
        match self {
            NodeType::Root { instruction } => Some(instruction),
            _ => None,
        }
    }

    /// 获取路径节点信息（仅对路径节点有效）
    pub fn as_path(&self) -> Option<(&[PathConstraint], &[String], &str)> {
        match self {
            NodeType::Path {
                constraints,
                variables,
                location,
            } => Some((constraints, variables, location)),
            _ => None,
        }
    }

    /// 获取分支节点信息（仅对分支节点有效）
    pub fn as_branch(&self) -> Option<(u32, &str, &str)> {
        match self {
            NodeType::Branch {
                fork_id,
                variable,
                location,
            } => Some((*fork_id, variable, location)),
            _ => None,
        }
    }

    /// 获取叶子节点信息（仅对叶子节点有效）
    pub fn as_leaf(&self) -> Option<LeafNodeInfo<B>> {
        match self {
            NodeType::Leaf {
                satisfiable,
                return_value,
                constructor_name,
                unfolded_value,
            } => Some(LeafNodeInfo {
                satisfiable: *satisfiable,
                return_value: return_value.as_ref(),
                constructor_name: constructor_name.as_deref(),
                unfolded_value: unfolded_value.as_deref(),
            }),
            _ => None,
        }
    }
}

/// 叶子节点信息的视图
///
/// 提供对叶子节点相关数据的只读访问，避免直接匹配枚举。
pub struct LeafNodeInfo<'a, B> {
    /// 此路径是否可满足
    pub satisfiable: bool,
    /// zexecute 的返回值
    pub return_value: Option<&'a Val<B>>,
    /// 构造函数名称（如果返回值是构造函数）
    pub constructor_name: Option<&'a str>,
    /// 展开后的值表示（用于显示）
    pub unfolded_value: Option<&'a str>,
}

/// 路径约束条件
///
/// 表示在符号执行过程中，对某个符号变量施加的约束。
#[derive(Clone, Debug)]
pub struct PathConstraint {
    /// 符号变量名称
    pub variable: String,
    /// 约束条件（例如 "x = true" 或 "x = false"）
    pub constraint: String,
    /// 分支编号（0 表示真，1 表示假）
    pub branch_num: u32,
}

impl PathConstraint {
    /// 创建一个新的路径约束
    ///
    /// # 参数
    /// * `variable` - 符号变量名称
    /// * `constraint` - 约束条件的字符串表示
    /// * `branch_num` - 分支编号（0 表示真分支，1 表示假分支）
    pub fn new(variable: String, constraint: String, branch_num: u32) -> Self {
        PathConstraint {
            variable,
            constraint,
            branch_num,
        }
    }

    /// 创建一个真值约束（变量为 true）
    ///
    /// # 参数
    /// * `variable` - 符号变量名称
    pub fn true_constraint(variable: String) -> Self {
        PathConstraint {
            variable,
            constraint: "true".to_string(),
            branch_num: 0,
        }
    }

    /// 创建一个假值约束（变量为 false）
    ///
    /// # 参数
    /// * `variable` - 符号变量名称
    pub fn false_constraint(variable: String) -> Self {
        PathConstraint {
            variable,
            constraint: "false".to_string(),
            branch_num: 1,
        }
    }

    /// 判断是否为真分支
    pub fn is_true_branch(&self) -> bool {
        self.branch_num == 0
    }

    /// 判断是否为假分支
    pub fn is_false_branch(&self) -> bool {
        self.branch_num == 1
    }

    /// 获取分支方向的描述
    pub fn branch_direction(&self) -> &str {
        if self.is_true_branch() {
            "真"
        } else {
            "假"
        }
    }

    /// 格式化约束为可读字符串
    pub fn format(&self) -> String {
        format!("{} = {}", self.variable, self.constraint)
    }
}

/// 符号执行结果（包含执行树）
///
/// 封装了符号执行的完整结果，包括执行树、路径统计和叶子节点信息。
pub struct ExecutionResult<B> {
    /// 执行树
    pub tree: Tree<B>,
    /// 探索的执行路径数量
    pub num_paths: usize,
    /// 所有叶子节点（执行终点）的信息
    pub leaves: Vec<LeafInfo<B>>,
}

impl<B: std::fmt::Debug> std::fmt::Debug for ExecutionResult<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExecutionResult")
            .field("num_paths", &self.num_paths)
            .field("leaf_count", &self.leaves.len())
            .field("tree_depth", &self.tree.max_depth())
            .finish()
    }
}

/// 叶子节点信息
///
/// 记录执行路径终点的相关信息。
#[derive(Clone, Debug)]
pub struct LeafInfo<B> {
    /// 通往此叶子节点的路径（Arc 节点引用列表）
    pub path: Vec<Arc<TreeNode<B>>>,
    /// 是否可满足
    pub satisfiable: bool,
    /// 返回值
    pub return_value: Option<Val<B>>,
}

/// 符号执行指令并收集执行树
///
/// 返回显示所有探索分支的执行树。
pub fn execute_instruction_tree<B: BV>(
    instruction_name: &str,
    shared_state: &SharedState<B>,
    regs: &RegisterBindings<B>,
    lets: &Bindings<B>,
) -> Result<ExecutionResult<B>, ExecError> {
    // 查找指令函数（zexecute 函数分派到指令处理器）
    let zexecute_id = shared_state.symtab.lookup("zexecute");

    // 通过调用构造函数创建指令值
    let encoded_name = format!("z{}", instruction_name);
    let ctor_id = shared_state.symtab.lookup(&encoded_name);

    // 获取构造函数类型并创建默认参数
    let instruction_value = if let Some(union_members) = shared_state.type_info.unions.get(&shared_state.symtab.lookup("zinstruction")) {
        if let Some((_, ctor_ty)) = union_members.iter().find(|(n, _)| *n == ctor_id) {
            let arg_value = generate_default_value(ctor_ty, shared_state);
            Val::Ctor(ctor_id, Box::new(arg_value))
        } else {
            return Err(ExecError::Unreachable(format!("指令 '{}' 在 zinstruction union 中未找到", instruction_name)));
        }
    } else {
        return Err(ExecError::Unreachable("zinstruction union 未找到".to_string()));
    };

    // 获取 zexecute 函数
    let (func_args, ret_ty, instrs) = shared_state.functions.get(&zexecute_id)
        .ok_or_else(|| ExecError::Unreachable("zexecute 函数未找到".to_string()))?;

    // 为 zexecute 创建初始帧
    let mut initial_frame = LocalFrame::new(zexecute_id, func_args, ret_ty, Some(&[instruction_value]), instrs);
    initial_frame.add_regs(regs);
    initial_frame.add_lets(lets);

    // 创建任务
    let task_state = TaskState::new();
    let task_id = TaskId::fresh();
    let task = initial_frame.task(task_id, &task_state);

    // 创建根节点
    let root = TreeNode::new_root(NodeType::Root {
        instruction: instruction_name.to_string(),
    });
    let tree = Tree::new(Arc::clone(&root));

    // TreeCollector 收集器上下文结构
    struct TreeCollectorContext<B> {
        result: Mutex<ExecutionResult<B>>,
        current_path: Mutex<Vec<Arc<TreeNode<B>>>>,
    }

    // 使用 Arc<Mutex<>> 包装结果以便在闭包中共享
    let collected: Arc<TreeCollectorContext<B>> = Arc::new(TreeCollectorContext {
        result: Mutex::new(ExecutionResult {
            tree: Tree::new(Arc::clone(&root)),
            num_paths: 0,
            leaves: Vec::new(),
        }),
        current_path: Mutex::new(Vec::new()),
    });

    let collector = | _thread: usize, _task_id: TaskId, exec_result: Result<(Run<B>, LocalFrame<B>), (ExecError, Vec<(Name, usize)>)>, shared_state: &SharedState<B>, solver: Solver<B>, collected: &Arc<TreeCollectorContext<B>>| {
        match exec_result {
            Ok((run, _frame)) => {
                // 从求解器跟踪中提取事件以构建树
                let events = solver.trace().to_vec();

                let mut result_guard = collected.result.lock().unwrap();
                let mut path_guard = collected.current_path.lock().unwrap();

                // 处理事件以构建树结构
                for event in events {
                    if let Event::Fork(fork_id, sym, _branch_num, loc) = event {
                        let var_name = sym.to_string();
                        let location = loc.location_string(shared_state.symtab.files());

                        // 创建分支节点
                        let branch_node = TreeNode::new_with_parent(
                            NodeType::Branch {
                                fork_id: *fork_id,
                                variable: var_name.clone(),
                                location: location.clone(),
                            },
                            &result_guard.tree.root,
                        );

                        // 跟踪当前路径
                        path_guard.push(Arc::clone(&branch_node));
                    }
                }

                match run {
                    Run::Finished(ret_val) => {
                        result_guard.num_paths += 1;

                        // 如果返回值是 Ctor，提取构造函数名称
                        let constructor_name = if let Val::Ctor(name, _) = &ret_val {
                            Some(shared_state.symtab.to_str(*name).to_string())
                        } else {
                            None
                        };

                        // 展开返回值以便更好地显示
                        let unfolded_value = Some(unfold_return_value(&ret_val, shared_state, regs, lets).0);

                        // 创建叶子节点
                        let leaf_node = if !path_guard.is_empty() {
                            // 如果有分支节点，添加到最后一个分支节点下
                            let last_branch = path_guard.last().unwrap();
                            TreeNode::new_with_parent(
                                NodeType::Leaf {
                                    satisfiable: true,
                                    return_value: Some(ret_val.clone()),
                                    constructor_name: constructor_name.clone(),
                                    unfolded_value,
                                },
                                last_branch,
                            )
                        } else {
                            // 否则直接添加到根节点下
                            TreeNode::new_with_parent(
                                NodeType::Leaf {
                                    satisfiable: true,
                                    return_value: Some(ret_val.clone()),
                                    constructor_name: constructor_name.clone(),
                                    unfolded_value,
                                },
                                &result_guard.tree.root,
                            )
                        };

                        // 记录叶子信息
                        result_guard.leaves.push(LeafInfo {
                            path: path_guard.clone(),
                            satisfiable: true,
                            return_value: Some(ret_val.clone()),
                        });

                        path_guard.clear();
                    }
                    Run::Dead => {
                        // 路径不可满足
                        result_guard.num_paths += 1;

                        // 创建不可满足的叶子节点
                        if !path_guard.is_empty() {
                            let last_branch = path_guard.last().unwrap();
                            TreeNode::new_with_parent(
                                NodeType::Leaf {
                                    satisfiable: false,
                                    return_value: None,
                                    constructor_name: None,
                                    unfolded_value: None,
                                },
                                last_branch,
                            );
                        } else {
                            TreeNode::new_with_parent(
                                NodeType::Leaf {
                                    satisfiable: false,
                                    return_value: None,
                                    constructor_name: None,
                                    unfolded_value: None,
                                },
                                &result_guard.tree.root,
                            );
                        }

                        result_guard.leaves.push(LeafInfo {
                            path: path_guard.clone(),
                            satisfiable: false,
                            return_value: None,
                        });

                        path_guard.clear();
                    }
                    _ => {}
                }
            }
            Err((error, backtrace)) => {
                eprintln!("执行错误: {:?}", error);
                eprintln!("调用栈: {:?}", backtrace_string(&backtrace, &shared_state.symtab));
            }
        }
    };

    start_single(task, shared_state, &collected, &collector);

    // 返回结果的克隆版本
    // 注意：这里需要特殊处理，因为 ExecutionResult 现在包含 Tree 而不是 TreeNode
    let result_guard = collected.result.lock().unwrap();

    // 手动克隆结果
    Ok(ExecutionResult {
        tree: Tree::new(Arc::clone(result_guard.tree.root())),
        num_paths: result_guard.num_paths,
        leaves: result_guard.leaves.clone(),
    })
}

/// Unfold a return value by recursively executing constructor functions
/// Returns a string representation of the unfolded value
pub fn unfold_return_value<B: BV>(
    val: &Val<B>,
    shared_state: &SharedState<B>,
    _regs: &RegisterBindings<B>,
    _lets: &Bindings<B>,
) -> (String, Option<Val<B>>) {
    use std::sync::{Arc, Mutex};

    match val {
        Val::Ctor(name, args) => {
            let ctor_name = shared_state.symtab.to_str(*name);

            // First, try to get the string representation directly
            let args_str = match &**args {
                Val::Unit => "Unit".to_string(),
                Val::I64(n) => format!("i64({})", n),
                Val::I128(n) => format!("i128({})", n),
                Val::Bool(b) => format!("bool({})", b),
                Val::Bits(bv) => format!("bits({})", bv),
                Val::String(s) => format!("\"{}\"", s),
                Val::Symbolic(sym) => format!("sym({})", sym),
                Val::Vector(v) => format!("vector[{}]", v.len()),
                Val::List(l) => format!("list[{}]", l.len()),
                Val::Enum(e) => format!("enum({:?})", e),
                Val::Struct(_s) => "struct{..}".to_string(),
                Val::Ctor(n, _) => {
                    let inner_name = shared_state.symtab.to_str(*n);
                    format!("{}(...)", inner_name)
                }
                Val::Poison => "Poison".to_string(),
                Val::Ref(r) => format!("ref({})", shared_state.symtab.to_str(*r)),
                _ => "<other>".to_string(),
            };

            (format!("{}({})", ctor_name, args_str), Some(val.clone()))
        }
        _ => {
            // For non-ctor values, just return the string representation
            let val_str = match val {
                Val::Unit => "Unit".to_string(),
                Val::I64(n) => format!("{}", n),
                Val::I128(n) => format!("{}", n),
                Val::Bool(b) => format!("{}", b),
                Val::Bits(bv) => format!("{}", bv),
                Val::String(s) => s.clone(),
                Val::Symbolic(sym) => format!("<sym:{}>", sym),
                Val::Poison => "Poison".to_string(),
                Val::Ref(r) => format!("<ref:{}>", shared_state.symtab.to_str(*r)),
                _ => "<complex>".to_string(),
            };
            (val_str, Some(val.clone()))
        }
    }
}

/// Execution options
pub struct ExecOptions {
    /// Use config defaults for unconstrained fields
    pub init_isa_with_config: bool,
    /// Timeout in seconds
    pub timeout: Option<u64>,
    /// Number of threads
    pub num_threads: usize,
}

/**
 * 数据依赖追踪
 */

/// Solve a path's constraints to get concrete values
pub fn solve_path<B: BV>(
    path: &ExecutionPath<B>,
    solver: &mut Solver<B>,
    isa_config: &ISAConfig<B>,
    init_with_config: bool,
) -> SolveResult<B> {
    // TODO: Implement constraint solving
    // This will:
    // 1. Build SMT constraints from path conditions
    // 2. Check satisfiability
    // 3. If sat, extract model values
    // 4. Fill unconstrained variables with defaults or random values
    SolveResult::Unknown
}

/// 将执行树格式化为 ASCII 艺术
pub fn format_tree_ascii<B: BV>(result: &ExecutionResult<B>) -> String {
    result.tree.format_ascii(result.num_paths)
}

/// 将执行树格式化为 Graphviz DOT 格式
pub fn format_tree_graphviz<B: BV>(result: &ExecutionResult<B>) -> String {
    result.tree.format_graphviz()
}
