use crate::bitvector::BV;
use crate::config::ISAConfig;
use crate::dprint::colors;
use crate::error::ExecError;
use crate::executor::{
    backtrace_string, execute_ir_function, start_single, Collector, LocalFrame, Run, TaskId, TaskState,
};
use crate::ir::UVal;
use crate::isarch_args::{ArgStruct, InstructionMap};
use crate::log;
use crate::register::RegisterBindings;
use crate::smt::{checkpoint, Config, Context, EnumMember, Model};
use crate::smt::{Checkpoint, Event, Solver, Sym};
use crate::source_loc::SourceLoc;
use crate::{d2, dlog, zencode};
use crate::{ir::*, smt};
use sha2::digest::generic_array::functional::FunctionalSequence;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::sync::{Arc, Mutex, Weak};

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

#[cfg(feature = "debug_exec")]
pub fn test_exec_main<B: BV>(shared_state: &SharedState<B>, regs: &RegisterBindings<B>, lets: &Bindings<B>) {
    println!("test_exec_main");

    ()
}
