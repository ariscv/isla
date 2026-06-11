// BSD 2-Clause License
//
// Copyright (c) 2020, 2021, 2022 Brian Campbell
// Copyright (c) 2020 Alasdair Armstrong
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

use crossbeam::queue::SegQueue;
use std::collections::{HashMap, HashSet};
use std::fs::OpenOptions;
use std::io::Write;
use std::ops::Range;
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use crate::isarch::context_state::GVAccessor;
use crate::isarch::target::{Target, TranslationTableInfo};

use isla_lib::bitvector::{b64::B64, BV};
use isla_lib::error::ExecError;
use isla_lib::executor;
use isla_lib::executor::{freeze_frame, Frame, LocalFrame, Run, StopConditions, TaskId, TaskState};
use isla_lib::ir::*;
use isla_lib::memory::{Address, Memory, SmtKind};
use isla_lib::primop_util::smt_sbits;
use isla_lib::register::RegisterBindings;
use isla_lib::simplify::write_events;
use isla_lib::smt;
use isla_lib::smt::smtlib;
use isla_lib::smt::smtlib::bits64;
use isla_lib::smt::{Checkpoint, Event, Model, ModelVal, ReadOpts, SmtResult, Solver, Sym, WriteOpts};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use isla_lib::{log, log_from};

/// 将 Isla 运行时值转换成 SMT 表达式，供后续约束构造使用。
fn smt_value<B: BV>(v: &Val<B>) -> Result<smtlib::Exp<Sym>, ExecError> {
    // 这里统一使用 unknown source location，因为调用方只关心约束表达式。
    isla_lib::primop_util::smt_value(v, SourceLoc::unknown())
}

/// 构造从 SMT 数组内存中读取连续字节的表达式。
fn smt_read_exp(memory: Sym, addr_exp: &smtlib::Exp<Sym>, addr_size: u32, bytes: u64) -> smtlib::Exp<Sym> {
    use smtlib::Exp;
    // 按当前 little-endian 约定把多个字节拼成一个 bitvector。
    let mut mem_exp = Exp::Select(Box::new(Exp::Var(memory)), Box::new(addr_exp.clone()));
    for i in 1..bytes {
        mem_exp = Exp::Concat(
            Box::new(Exp::Select(
                Box::new(Exp::Var(memory)),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(bits64(i as u64, addr_size)))),
            )),
            Box::new(mem_exp),
        )
    }
    mem_exp
}

// TODO: tagless tests for plain aarch64

// NB: does not support symbolic accesses to Concrete memory regions,
// or writes to the translation table.  The translation table is
// represented separately because adding a large amount of data to an
// array slowed down the solver unacceptably.

#[derive(Debug, Clone)]
struct SeqMemory {
    translation_table: Option<TranslationTableInfo>,
    memory_var: Sym,
    tag_memory_var: Sym,
    addr_size: u32,
    cap_addr_mask: u64,
    no_tags_in_regions: Vec<Range<Address>>,
}

impl SeqMemory {
    /// 为 tag 内存生成“某些区域不允许有 tag”的约束。
    fn tag_constraint<B: BV>(
        &self,
        solver: &mut Solver<B>,
        address: &smtlib::Exp<Sym>,
        tag: &smtlib::Exp<Sym>,
    ) -> Option<smtlib::Exp<Sym>> {
        use isla_lib::smt::smtlib::Exp::*;
        // 没有 no-tag 区域时不需要额外约束。
        let mut i = self.no_tags_in_regions.iter();
        if let Some(r) = i.next() {
            let addr_var = match address {
                Var(v) => *v,
                _ => {
                    let v = solver.fresh();
                    solver.add(smtlib::Def::DefineConst(v, address.clone()));
                    v
                }
            };
            let mut prop = Or(
                Box::new(Bvult(Box::new(Var(addr_var)), Box::new(bits64(r.start, self.addr_size)))),
                Box::new(Bvule(Box::new(bits64(r.end, self.addr_size)), Box::new(Var(addr_var)))),
            );
            for r in i {
                prop = And(
                    Box::new(prop),
                    Box::new(Or(
                        Box::new(Bvult(Box::new(Var(addr_var)), Box::new(bits64(r.start, self.addr_size)))),
                        Box::new(Bvule(Box::new(bits64(r.end, self.addr_size)), Box::new(Var(addr_var)))),
                    )),
                );
            }
            prop = Or(Box::new(Eq(Box::new(tag.clone()), Box::new(bits64(0, 1)))), Box::new(prop));
            Some(prop)
        } else {
            None
        }
    }
}

impl<B: BV> isla_lib::memory::MemoryCallbacks<B> for SeqMemory {
    /// 在符号执行读内存时，把读结果和 SeqMemory 的 SMT 数组状态关联起来。
    fn symbolic_read(
        &self,
        regions: &[isla_lib::memory::Region<B>],
        solver: &mut Solver<B>,
        value: &Val<B>,
        _read_kind: &Val<B>,
        address: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        opts: &ReadOpts,
    ) {
        use isla_lib::smt::smtlib::{Def, Exp};

        // 把读值、地址和可选 tag 都转成 SMT 约束。
        let read_exp = smt_value(value).unwrap_or_else(|err| panic!("Bad memory read value {:?}: {}", value, err));
        let addr_exp = smt_value(address).unwrap_or_else(|err| panic!("Bad read address value {:?}: {}", address, err));
        let mut read_prop = Exp::Eq(
            Box::new(read_exp.clone()),
            Box::new(smt_read_exp(self.memory_var, &addr_exp, self.addr_size, bytes as u64)),
        );
        let tag_exp = match tag {
            Some(tag_value) => {
                let tag_exp = smt_value(tag_value)
                    .unwrap_or_else(|err| panic!("Bad memory tag read value {:?}: {}", tag_value, err));
                let prop = Exp::Eq(
                    Box::new(tag_exp.clone()),
                    Box::new(Exp::Select(Box::new(Exp::Var(self.tag_memory_var)), Box::new(addr_exp.clone()))),
                );
                read_prop = Exp::And(Box::new(read_prop), Box::new(prop));
                if let Some(p) = self.tag_constraint(solver, &addr_exp, &tag_exp) {
                    read_prop = Exp::And(Box::new(read_prop), Box::new(p))
                };
                Some(tag_exp)
            }
            None => None,
        };
        let kind = if opts.is_ifetch {
            SmtKind::ReadInstr
        } else if opts.is_exclusive {
            // We produce a dummy read so that failed store exclusives still get address
            // constraints, but the memory must be writable.
            SmtKind::WriteData
        } else {
            SmtKind::ReadData
        };
        let address_constraint =
            isla_lib::memory::smt_address_constraint(regions, &addr_exp, bytes, kind, solver, tag_exp.as_ref());

        let full_constraint = match &self.translation_table {
            Some(tt_info) => {
                let tt_prop = crate::isarch::target::translation_table_exp(tt_info, read_exp, addr_exp, bytes);
                let tt_prop = match tag_exp {
                    Some(tag_exp) => {
                        Exp::And(Box::new(Exp::Eq(Box::new(tag_exp), Box::new(bits64(0, 1)))), Box::new(tt_prop))
                    }
                    None => tt_prop,
                };
                Exp::Ite(Box::new(address_constraint), Box::new(read_prop), Box::new(tt_prop))
            }
            None => Exp::And(Box::new(address_constraint), Box::new(read_prop)),
        };

        solver.add(Def::Assert(full_constraint));
    }

    /// 在符号执行写内存时，更新 SeqMemory 的 SMT 数组版本并添加地址约束。
    fn symbolic_write(
        &mut self,
        regions: &[isla_lib::memory::Region<B>],
        solver: &mut Solver<B>,
        _value: Sym,
        _read_kind: &Val<B>,
        address: &Val<B>,
        data: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        _opts: &WriteOpts,
    ) {
        use isla_lib::smt::smtlib::{Def, Exp};

        // 先把写入的数据和地址提取成 SMT 表达式。
        let data_exp = smt_value(data).unwrap_or_else(|err| panic!("Bad memory write value {:?}: {}", data, err));
        let addr_exp =
            smt_value(address).unwrap_or_else(|err| panic!("Bad write address value {:?}: {}", address, err));
        // 按当前 little-endian 约定把写入数据拆成逐字节 store。
        let mut mem_exp = Exp::Store(
            Box::new(Exp::Var(self.memory_var)),
            Box::new(addr_exp.clone()),
            Box::new(Exp::Extract(7, 0, Box::new(data_exp.clone()))),
        );
        for i in 1..bytes {
            mem_exp = Exp::Store(
                Box::new(mem_exp),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(bits64(i as u64, self.addr_size)))),
                Box::new(Exp::Extract(i * 8 + 7, i * 8, Box::new(data_exp.clone()))),
            )
        }
        self.memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.memory_var, mem_exp));
        // When clearing capability tags we might not start with an aligned address
        let tag_addr_exp = Exp::Bvand(
            Box::new(addr_exp.clone()),
            Box::new(Exp::Bvnot(Box::new(bits64(self.cap_addr_mask, self.addr_size)))),
        );
        let tag_exp = match tag {
            Some(tag_value) => {
                let tag_exp = smt_value(tag_value)
                    .unwrap_or_else(|err| panic!("Bad memory tag write value {:?}: {}", tag_value, err));
                if let Some(p) = self.tag_constraint(solver, &tag_addr_exp, &tag_exp) {
                    solver.add(Def::Assert(p));
                };
                tag_exp
            }
            None => bits64(0, 1),
        };
        let tag_mem_exp =
            Exp::Store(Box::new(Exp::Var(self.tag_memory_var)), Box::new(tag_addr_exp), Box::new(tag_exp.clone()));
        self.tag_memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.tag_memory_var, tag_mem_exp));

        let kind = SmtKind::WriteData;
        let address_constraint =
            isla_lib::memory::smt_address_constraint(regions, &addr_exp, bytes, kind, solver, Some(&tag_exp));
        solver.add(Def::Assert(address_constraint));
    }

    /// 在符号执行只写 tag 时，更新 tag memory 的 SMT 数组版本。
    fn symbolic_write_tag(
        &mut self,
        regions: &[isla_lib::memory::Region<B>],
        solver: &mut Solver<B>,
        _value: Sym,
        _write_kind: &Val<B>,
        address: &Val<B>,
        tag: &Val<B>,
    ) {
        use isla_lib::smt::smtlib::{Def, Exp};

        // tag 写入直接约束 tag memory 数组中的目标地址。
        let addr_exp =
            smt_value(address).unwrap_or_else(|err| panic!("Bad write address value {:?}: {}", address, err));
        let tag_exp = smt_value(tag).unwrap_or_else(|err| panic!("Bad memory tag write value {:?}: {}", tag, err));
        let tag_mem_exp =
            Exp::Store(Box::new(Exp::Var(self.tag_memory_var)), Box::new(addr_exp.clone()), Box::new(tag_exp.clone()));
        self.tag_memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.tag_memory_var, tag_mem_exp));

        let kind = SmtKind::WriteData;
        // Only insist on the start address being in range, leave the size and alignment to the
        // model
        let address_constraint =
            isla_lib::memory::smt_address_constraint(regions, &addr_exp, 1, kind, solver, Some(&tag_exp));
        solver.add(Def::Assert(address_constraint));
    }
}

enum PCResolved<B: BV> {
    SymbolicPC(Sym),
    ConcretePC(B),
}

// TODO: generalize this so that we can use it in other places where making a register
// concrete is useful.
/// 尝试把当前 PC 解析成具体值；无法唯一确定时保留符号 PC。
fn resolve_concrete_pc<'ir, B: BV>(
    registers: &mut RegisterBindings<'ir, B>,
    pc_id: Name,
    pc_accessor: Vec<GVAccessor<String>>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
) -> Result<PCResolved<B>, String> {
    use isla_lib::smt::smtlib::Exp;
    use PCResolved::*;

    // 先从寄存器文件中取出 PC，再根据 accessor 进入真实地址字段。
    match registers.get(pc_id, shared_state, solver, SourceLoc::unknown()).map_err(|e| format!("{}", e))? {
        Some(full_val) => {
            let pc_addr = apply_accessor_val(shared_state, full_val, &pc_accessor);
            match pc_addr {
                Val::Symbolic(v) => {
                    if solver.check_sat(SourceLoc::unknown()).is_unsat().map_err(|e| format!("{}", e))? {
                        return Err(String::from("Unsatisfiable in post-processing"));
                    }
                    let model_val = {
                        let mut model = Model::new(solver);
                        model.get_var(*v).map_err(|e| format!("{}", e))?
                    };
                    match model_val {
                        ModelVal::Exp(Exp::Bits64(result)) => {
                            if solver
                                .check_sat_with(
                                    &Exp::Neq(Box::new(Exp::Var(*v)), Box::new(Exp::Bits64(result))),
                                    SourceLoc::unknown(),
                                )
                                .is_unsat()
                                .map_err(|e| format!("{}", e))?
                            {
                                let bits = B::new(result.lower_u64(), result.len());
                                // Cache the concrete value
                                let mut new = full_val.clone();
                                let new_pc = apply_accessor_val_mut(shared_state, &mut new, &pc_accessor);
                                *new_pc = Val::Bits(bits);
                                registers.assign(pc_id, new, shared_state);
                                Ok(ConcretePC(bits))
                            } else {
                                Ok(SymbolicPC(*v))
                            }
                        }
                        _ => Ok(SymbolicPC(*v)),
                    }
                }
                Val::Bits(bits) => Ok(ConcretePC(*bits)),
                value => Err(format!("Unexpected PC value: {:?}", value)),
            }
        }
        None => Err(String::from("Missing PC register")),
    }
}

/// 在关键阶段检查当前约束是否仍可满足。
fn just_check<B: BV>(solver: &mut Solver<B>, s: &str) -> Result<(), String> {
    // 把 SMT 的三态结果转换成 postprocess 使用的字符串错误。
    match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => Ok(()),
        SmtResult::Unsat => Err(format!("Unsatisfiable at {}", s)),
        SmtResult::Unknown => Err(format!("Solver returned unknown at {}", s)),
    }
}

/// 执行单条指令后进行收尾检查，并把最终 frame/checkpoint 返回给上下文提取。
fn postprocess<'ir, B: BV, T: Target>(
    target: &T,
    tid: usize,
    _task_id: TaskId,
    mut local_frame: LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    _events: &Vec<Event<B>>,
) -> Result<(Frame<'ir, B>, Checkpoint<B>), String> {
    use isla_lib::smt::smtlib::{Def, Exp};
    use PCResolved::*;

    // postprocess 的核心目标是让后续取指地址仍落在可执行代码区域。
    log_from!(tid, log::VERBOSE, "Postprocessing");

    just_check(&mut solver, "start of postprocessing")?;

    // Ensure the new PC can be placed in memory
    // (currently this is used to prevent an exception)
    let alignment_pow = T::pc_alignment_pow();
    let (pc_name, pc_acc) = target.pc_reg();
    let pc_id = shared_state.symtab.lookup(&pc_name);
    match resolve_concrete_pc(local_frame.regs_mut(), pc_id, pc_acc, shared_state, &mut solver)? {
        SymbolicPC(v) => {
            let pc_exp = Exp::Var(v);
            let pc_constraint =
                local_frame.memory().smt_address_constraint(&pc_exp, 4, SmtKind::ReadInstr, &mut solver, None);
            solver.add(Def::Assert(pc_constraint));
            just_check(&mut solver, "post-instruction PC constraint")?;
            // Alignment constraint
            if alignment_pow > 0 {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(alignment_pow - 1, 0, Box::new(pc_exp))),
                    Box::new(bits64(0, alignment_pow)),
                )));
                just_check(&mut solver, "post-instruction PC alignment constraint")?;
            }
        }
        ConcretePC(b) => {
            if let Ok(pc_i) = b.try_into() {
                let alignment = 1 << alignment_pow;
                // Note that this isn't a definitive check that we can get the next instruction
                // in memory; on x86 we don't even know how long that instruction will be
                if local_frame.memory().access_check(pc_i, alignment, SmtKind::ReadInstr) {
                    if pc_i % alignment as u64 != 0 {
                        return Err(format!("Unaligned concrete PC: {}", pc_i));
                    }
                    // The target can optionally recognise an exception handler elsewhere
                    // and tell us where it jumps to
                } else {
                    return Err(format!("Concrete PC out of allowed ranges: {}", pc_i));
                }
            } else {
                return Err(format!("PC value far too large: {}", b));
            }
        }
    }

    target.postprocess(shared_state, &local_frame, &mut solver)?;

    let result = match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => Ok((freeze_frame(&local_frame), smt::checkpoint(&mut solver))),
        SmtResult::Unsat => Err(String::from("unsatisfiable")),
        SmtResult::Unknown => Err(String::from("solver returned unknown")),
    };
    log_from!(tid, log::VERBOSE, "Postprocessing complete");
    result
}

// Get a single opcode for debugging
/// 从 checkpoint 的模型中取出当前放入内存的 opcode 具体值。
fn get_opcode<B: BV>(checkpoint: Checkpoint<B>, opcode_var: Sym) -> Result<u32, String> {
    // 重新打开 checkpoint 并要求 SMT solver 给出完整模型。
    let mut cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(String::from("Unsatisfiable at recheck")),
        SmtResult::Unknown => return Err(String::from("Solver returned unknown at recheck")),
    };
    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));
    let opcode = model.get_var(opcode_var).unwrap().unwrap_exp();
    match opcode {
        smt::smtlib::Exp::Bits64(bits) => Ok(bits.lower_u64() as u32),
        _ => Err(String::from("Bad model value")),
    }
}

pub enum RegSource {
    Concrete(u64),
    Symbolic(Sym),
    Uninit,
}

/// 根据字段/元素 accessor 在类型中定位子类型。
pub fn apply_accessor_type<'a, B: BV>(
    shared_state: &'a SharedState<B>,
    mut ty: &'a Ty<Name>,
    accessor: &[GVAccessor<String>],
) -> &'a Ty<Name> {
    // 顺序应用 accessor，支持 struct field 和 vector element 两种路径。
    for acc in accessor {
        match acc {
            GVAccessor::Field(s) => {
                let name =
                    shared_state.symtab.get(&zencode::encode(&s)).unwrap_or_else(|| panic!("No field called {}", s));
                match ty {
                    Ty::Struct(struct_name) => {
                        ty = shared_state.type_info.structs.get(struct_name).unwrap().get(&name).unwrap()
                    }
                    _ => panic!("Bad type for struct {:?}", ty),
                }
            }
            GVAccessor::Element(_i) => match ty {
                Ty::Vector(element_ty) => ty = element_ty,
                Ty::FixedVector(_, element_ty) => ty = element_ty,
                _ => panic!("Bad type for vector {:?}", ty),
            },
        }
    }
    ty
}

/// 根据字段/元素 accessor 在可变值中定位子值。
pub fn apply_accessor_val_mut<'a, B: BV>(
    shared_state: &'a SharedState<B>,
    mut val: &'a mut Val<B>,
    accessor: &[GVAccessor<String>],
) -> &'a mut Val<B> {
    // 顺序进入嵌套结构，最终返回目标子值的可变引用。
    for acc in accessor {
        match acc {
            GVAccessor::Field(s) => {
                let name =
                    shared_state.symtab.get(&zencode::encode(&s)).unwrap_or_else(|| panic!("No field called {}", s));
                match val {
                    Val::Struct(field_vals) => val = field_vals.get_mut(&name).unwrap(),
                    _ => panic!("Bad val for struct {}", val.to_string(shared_state)),
                }
            }
            GVAccessor::Element(i) => match val {
                Val::Vector(elements) => val = &mut elements[*i],
                _ => panic!("Bad val for vector {}", val.to_string(shared_state)),
            },
        }
    }
    val
}

/// 根据字段/元素 accessor 在不可变值中定位子值。
pub fn apply_accessor_val<'a, B: BV>(
    shared_state: &'a SharedState<B>,
    mut val: &'a Val<B>,
    accessor: &[GVAccessor<String>],
) -> &'a Val<B> {
    // 顺序进入嵌套结构，最终返回目标子值引用。
    for acc in accessor {
        match acc {
            GVAccessor::Field(s) => {
                let name =
                    shared_state.symtab.get(&zencode::encode(&s)).unwrap_or_else(|| panic!("No field called {}", s));
                match val {
                    Val::Struct(field_vals) => val = field_vals.get(&name).unwrap(),
                    _ => panic!("Bad val for struct {}", val.to_string(shared_state)),
                }
            }
            GVAccessor::Element(i) => match val {
                Val::Vector(elements) => val = &elements[*i],
                _ => panic!("Bad val for vector {}", val.to_string(shared_state)),
            },
        }
    }
    val
}

/// 把指定寄存器子字段替换成符号变量，并返回新建的 SMT 符号。
fn setup_val<'a, B: BV>(
    shared_state: &'a SharedState<B>,
    val: &mut Val<B>,
    ty: &'a Ty<Name>,
    accessor: &Vec<GVAccessor<String>>,
    solver: &mut Solver<B>,
) -> Sym {
    // 先定位 accessor 指向的子值和子类型，再按类型声明符号变量。
    let val = apply_accessor_val_mut(shared_state, val, accessor);
    let ty = apply_accessor_type(shared_state, ty, accessor);
    match ty {
        Ty::Bits(len) => {
            let var = solver.fresh();
            solver.add(smtlib::Def::DeclareConst(var, smtlib::Ty::BitVec(*len)));
            *val = Val::Symbolic(var);
            var
        }
        Ty::Bool => {
            let var = solver.fresh();
            solver.add(smtlib::Def::DeclareConst(var, smtlib::Ty::Bool));
            *val = Val::Symbolic(var);
            var
        }
        _ => panic!("Register setup found unsupported type {:?}", ty),
    }
}

/// 符号化目标寄存器、约束初始 PC，并安装顺序符号内存回调。
pub fn setup_init_regs<'ir, B: BV, T: Target>(
    shared_state: &SharedState<'ir, B>,
    frame: Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    register_types: &HashMap<Name, Ty<Name>>,
    init_pc: u64,
    target: &T,
    no_tags_in_regions: &'ir [Range<Address>],
) -> (Frame<'ir, B>, Checkpoint<B>, HashMap<(String, Vec<GVAccessor<String>>), Sym>) {
    // 从初始化后的 checkpoint 恢复 solver/frame，随后把目标寄存器符号化。
    let mut local_frame = executor::unfreeze_frame(&frame);
    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let mut reg_vars = HashMap::new();

    for (reg, accessor) in target.regs() {
        let ex_var = shared_state
            .symtab
            .get(&zencode::encode(&reg))
            .unwrap_or_else(|| panic!("Register {} missing during setup", reg));
        let mut ex_val = local_frame
            .regs_mut()
            .get(ex_var, shared_state, &mut solver, SourceLoc::unknown())
            .unwrap_or_else(|e| panic!("Fail to lookup register {} during setup: {}", reg, e))
            .unwrap_or_else(|| panic!("No value for register {} during setup", reg))
            .clone();
        let ty = register_types.get(&ex_var).unwrap();
        let var = if let Some((var, val)) =
            target.special_reg_init(&reg, &accessor, ty, shared_state, &mut local_frame, &ctx, &mut solver)
        {
            ex_val = val;
            var
        } else {
            setup_val(shared_state, &mut ex_val, &ty, &accessor, &mut solver)
        };
        local_frame.regs_mut().assign(ex_var, ex_val, shared_state);
        reg_vars.insert((reg, accessor), var);
    }

    let (pc_str, pc_acc) = target.pc_reg();
    let pc_id = shared_state.symtab.lookup(&pc_str);
    let mut pc_full =
        local_frame.regs().get_last_if_initialized(pc_id).unwrap_or_else(|| panic!("PC not initialised")).clone();
    let pc_type = register_types.get(&pc_id).unwrap();
    let pc_addr = apply_accessor_val_mut(shared_state, &mut pc_full, &pc_acc);
    let pc_type = apply_accessor_type(shared_state, &pc_type, &pc_acc);
    match pc_type {
        Ty::Bits(n) => {
            use smtlib::{Def, Exp};
            solver.add(Def::Assert(Exp::Eq(
                Box::new(smt_value(pc_addr).unwrap()),
                Box::new(Exp::Bits64(B64::new(init_pc, *n))),
            )))
        }
        _ => panic!("Bad type for PC: {:?}", pc_type),
    };
    local_frame.regs_mut().assign(pc_id, pc_full, shared_state);

    let memory = solver.fresh();
    let tag_memory_var = solver.fresh();

    solver.add(smtlib::Def::DeclareConst(
        memory,
        smtlib::Ty::Array(Box::new(smtlib::Ty::BitVec(target.addr_size())), Box::new(smtlib::Ty::BitVec(8))),
    ));
    solver.add(smtlib::Def::DeclareConst(
        tag_memory_var,
        smtlib::Ty::Array(Box::new(smtlib::Ty::BitVec(target.addr_size())), Box::new(smtlib::Ty::BitVec(1))),
    ));

    target.init(shared_state, &mut local_frame, &mut solver, init_pc, &reg_vars);

    let memory_info: Box<dyn isla_lib::memory::MemoryCallbacks<B>> = Box::new(SeqMemory {
        translation_table: target.translation_table_info(),
        memory_var: memory,
        tag_memory_var,
        addr_size: target.addr_size(),
        cap_addr_mask: T::capability_address_mask(),
        no_tags_in_regions: Vec::from(no_tags_in_regions),
    });
    local_frame.memory_mut().set_client_info(memory_info);
    local_frame.memory().log();

    executor::reset_registers(
        0,
        &mut local_frame,
        &executor::TaskState::new(),
        shared_state,
        &mut solver,
        SourceLoc::unknown(),
    )
    .unwrap_or_else(|e| panic!("Unable to apply reset-time registers: {}", e));

    (freeze_frame(&local_frame), smt::checkpoint(&mut solver), reg_vars)
}

/// 在已有 solver/frame 上执行一个 Sail helper 函数，并回写新的 frame/checkpoint。
pub fn run_function_solver<'ctx, 'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    frame: &mut LocalFrame<'ir, B>,
    ctx: &'ctx smt::Context,
    solver: &mut Solver<'ctx, B>,
    function_name: &'ir str,
    args: Vec<Val<B>>,
) -> Val<B> {
    // 用当前 solver 建 checkpoint，执行后再恢复成调用方继续使用的 solver。
    let c = smt::checkpoint(solver);
    let (v, ff, cc) = run_function(shared_state, frame, c, function_name, args);
    *frame = ff;
    *solver = Solver::from_checkpoint(ctx, cc);
    v
}

/// 从指定 checkpoint 开始执行一个 Sail helper 函数，并返回其返回值和新状态。
pub fn run_function<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    frame: &mut LocalFrame<'ir, B>,
    checkpoint: Checkpoint<B>,
    function_name: &'ir str,
    args: Vec<Val<B>>,
) -> (Val<B>, LocalFrame<'ir, B>, Checkpoint<B>) {
    // helper 函数应当是确定性的，这里要求只产生一条完成路径。
    let fn_id = shared_state.symtab.lookup(&zencode::encode(function_name));
    let (arg_tys, ret_ty, instrs) =
        shared_state.functions.get(&fn_id).unwrap_or_else(|| panic!("Function \"{}\" not found", function_name));
    let results = SegQueue::new();
    let task_state = TaskState::new();
    let task = frame.new_call(fn_id, arg_tys, ret_ty, Some(&args), instrs).task_with_checkpoint(
        TaskId::fresh(),
        &task_state,
        checkpoint,
    );

    executor::start_single(
        task,
        &shared_state,
        &results,
        &move |_tid, _task_id, result, _shared_state, mut solver, results| match result {
            Ok((Run::Finished(val), frame)) => {
                results.push((val, frame, smt::checkpoint(&mut solver)));
            }
            Ok((Run::Exit | Run::Suspended | Run::Dead, _)) => (),
            Err((err, _frame)) => eprintln!("Helper function {} failed: {:?}", function_name, err),
        },
    );
    if results.len() != 1 {
        panic!("Expected execution of helper function {} to have one path, found {}", function_name, results.len());
    }
    let (val, frame, post_init_checkpoint) = results.pop().expect("pop failed");

    (val, frame, post_init_checkpoint)
}

/// 运行 Sail 初始化函数，得到后续指令执行使用的初始 frame/checkpoint。
pub fn init_model<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    lets: Bindings<'ir, B>,
    regs: RegisterBindings<'ir, B>,
    memory: &Memory<B>,
    init_fn_name: &str,
) -> (Frame<'ir, B>, Checkpoint<B>) {
    // 初始化阶段先把 lets/registers/memory 注入 LocalFrame。
    println!("Initialising model...");

    let init_fn = shared_state.symtab.lookup(&zencode::encode(init_fn_name));
    let (init_args, init_retty, init_instrs) = shared_state
        .functions
        .get(&init_fn)
        .unwrap_or_else(|| panic!("Initialisation function \"{}\" not found", init_fn_name));
    let init_result = SegQueue::new();
    let task_state = TaskState::new();
    let init_task = LocalFrame::new(init_fn, init_args, init_retty, None, init_instrs)
        .add_lets(&lets)
        .add_regs(&regs)
        .set_memory(memory.clone())
        .task(TaskId::fresh(), &task_state);

    executor::start_single(
        init_task,
        &shared_state,
        &init_result,
        &move |_tid, _task_id, result, _shared_state, mut solver, init_result| match result {
            Ok((_, frame)) => {
                init_result.push((freeze_frame(&frame), smt::checkpoint(&mut solver)));
            }
            Err((err, _frame)) => eprintln!("Initialisation failed: {:?}", err),
        },
    );
    if init_result.len() != 1 {
        eprintln!("Expected initialisation to have one path, found {}", init_result.len());
        exit(1);
    }
    let (frame, post_init_checkpoint) = init_result.pop().expect("pop failed");
    println!("...done");

    (frame, post_init_checkpoint)
}

/// 在当前 PC 对应的指令内存位置放入目标 opcode，并返回 opcode 约束符号。
pub fn setup_opcode<'ir, B: BV, T: Target>(
    target: &T,
    shared_state: &SharedState<'ir, B>,
    frame: &Frame<'ir, B>,
    opcode: B,
    opcode_mask: Option<u32>,
    prev_checkpoint: Checkpoint<B>,
) -> (Val<B>, Sym, Checkpoint<B>, bool) {
    use isla_lib::smt::smtlib::{Def, Exp, Ty};
    use isla_lib::smt::*;

    // 读取当前 PC 处的指令字节，再约束该读值等于待执行 opcode。
    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, prev_checkpoint);

    let local_frame = executor::unfreeze_frame(frame);

    let (pc_name, pc_acc) = target.pc_reg();
    let pc_id = shared_state.symtab.lookup(&pc_name);
    let pc = local_frame.regs().get_last_if_initialized(pc_id).unwrap();
    let pc = apply_accessor_val(shared_state, &pc, &pc_acc);
    // This will add a fake read event, but that shouldn't matter
    /*let read_kind_name = shared_state.symtab.get("zRead_ifetch").expect("Read_ifetch missing");
    let (read_kind_pos, read_kind_size) = shared_state.enum_members.get(&read_kind_name).unwrap();
    let read_kind = EnumMember { enum_id: solver.get_enum(*read_kind_size), member: *read_kind_pos };*/
    let read_opts = ReadOpts::ifetch();
    let read_size = Val::I128((opcode.len() / 8) as i128);
    let read_val = local_frame
        .memory()
        .read(Val::Unit /*Val::Enum(read_kind)*/, pc.clone(), read_size, &mut solver, false, read_opts)
        .unwrap();

    let opcode_var = solver.fresh();
    solver.add(Def::DeclareConst(opcode_var, Ty::BitVec(opcode.len())));

    // Working with a mask currently requires the model to be
    // sufficiently monomorphic, so prefer using a concrete value if
    // we can.  (Even if the variable bitvector length part of the
    // model is fully determined by the unmasked bits, the executor
    // doesn't attempt to replace them with a concrete value.)
    if let Some(opcode_mask) = opcode_mask {
        solver.add(Def::Assert(Exp::Eq(
            Box::new(Exp::Bvand(Box::new(Exp::Var(opcode_var)), Box::new(bits64(opcode_mask as u64, 32)))),
            Box::new(bits64(opcode.try_into().unwrap() & opcode_mask as u64, opcode.len())),
        )));
    } else {
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(opcode_var)), Box::new(smt_sbits(opcode)))));
    }
    let read_exp = smt_value(&read_val).unwrap();
    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(opcode_var)), Box::new(read_exp))));

    let ok = match solver.check_sat(SourceLoc::unknown()) {
        SmtResult::Sat => true,
        SmtResult::Unsat => {
            println!("Placing opcode in memory unsatisfiable");
            false
        }
        SmtResult::Unknown => {
            println!("Placing opcode in memory too hard for SMT solver (unknown)");
            false
        }
    };

    (pc.clone(), opcode_var, checkpoint(&mut solver), ok)
}

/// 按需从 solver 中取出事件 trace。
fn events_of<B: BV>(solver: &Solver<B>, active: bool) -> Vec<Event<B>> {
    // 非调试路径避免复制大量事件，减少开销。
    if active {
        solver.trace().to_vec().drain(..).cloned().collect()
    } else {
        vec![]
    }
}

/// 递归检查返回值中是否包含指定构造器。
fn value_contains_ctor<B: BV>(shared_state: &SharedState<B>, val: &Val<B>, ctor: &str) -> bool {
    // RISC-V step 返回值常嵌套在结构里，需要递归搜索。
    match val {
        Val::Ctor(name, inner) => {
            shared_state.symtab.to_str(*name) == ctor || value_contains_ctor(shared_state, inner, ctor)
        }
        Val::Struct(fields) => fields.values().any(|field| value_contains_ctor(shared_state, field, ctor)),
        Val::Vector(values) | Val::List(values) => {
            values.iter().any(|value| value_contains_ctor(shared_state, value, ctor))
        }
        _ => false,
    }
}

/// 从 Sail step 函数开始执行已放入内存的指令，并收集可行完成路径。
pub fn run_model_instruction<'ir, B: BV, T: Target>(
    target: &'ir T,
    model_function: &str,
    num_threads: usize,
    shared_state: &SharedState<'ir, B>,
    frame: &Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    opcode_var: Sym,
    stop_set: &StopConditions,
    dump_events: bool,
    assertion_reports: &Option<String>,
) -> Vec<(Frame<'ir, B>, Checkpoint<B>)> {
    // 构造 step 函数调用任务，执行结果只保留能正常 retire 的路径。
    let function_id = shared_state.symtab.lookup(&zencode::encode(model_function));
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();

    let local_frame = executor::unfreeze_frame(frame);

    let assertion_events = assertion_reports.is_some();

    let task_state = TaskState::new();
    let call_args = T::run_instruction_args();
    let mut task = local_frame.new_call(function_id, args, ret_ty, Some(&call_args), instrs).task_with_checkpoint(
        TaskId::fresh(),
        &task_state,
        checkpoint,
    );
    task.set_stop_conditions(stop_set);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(
        num_threads,
        None,
        vec![task],
        &shared_state,
        queue.clone(),
        &move |tid, task_id, result, shared_state, mut solver, collected| {
            log_from!(tid, log::VERBOSE, "Collecting");
            match result {
                Ok((Run::Finished(val), mut frame)) => {
                    target.post_instruction(shared_state, &mut frame, &mut solver);
                    let check = solver.check_sat(SourceLoc::unknown());
                    // We always need events to do the undefined bits check
                    let events = events_of(&solver, true);
                    if matches!(check, SmtResult::Sat) {
                        if let Some((ex_val, ex_loc)) = frame.get_exception() {
                            let s = ex_val.to_string(shared_state);
                            collected.push((Err(format!("Exception thrown: {} at {}", s, ex_loc)), events))
                        } else {
                            if let Err(m) = Ok::<HashMap<Sym, B>, String>(HashMap::new()) {
                                collected.push((Err(m), events))
                            } else {
                                if matches!(val, Val::Unit)
                                    || value_contains_ctor(shared_state, &val, "zRetire_Success")
                                {
                                    collected.push((
                                        postprocess(target, tid, task_id, frame, shared_state, solver, &events),
                                        events,
                                    ))
                                } else {
                                    log_from!(
                                        tid,
                                        log::VERBOSE,
                                        format!("Unexpected footprint return value: {:?}", val)
                                    );
                                    collected
                                        .push((Err(format!("Unexpected footprint return value: {:?}", val)), events))
                                }
                            }
                        }
                    } else {
                        log_from!(tid, log::VERBOSE, format!("Post-instruction check failed with {:?}", check));
                        collected.push((Err(format!("Post-instruction check failed with {:?}", check)), events))
                    }
                }
                Ok((Run::Exit | Run::Suspended | Run::Dead, _)) => {
                    let events = events_of(&solver, dump_events);
                    log_from!(tid, log::VERBOSE, "bad run");
                    collected.push((Err(String::from("bad run")), events))
                }
                Err((assertion @ ExecError::AssertionFailure(_, _), frame)) if assertion_events => {
                    let events = events_of(&solver, true);
                    log_from!(tid, log::VERBOSE, format!("Error {}", assertion));
                    let mut s = format!("{}\n", assertion);
                    for (f, pc) in frame.backtrace().iter().rev() {
                        s.push_str(&format!("  {} @ {}\n", shared_state.symtab.to_str(*f), pc));
                    }
                    collected.push((Err(s), events))
                }
                Err((err, frame)) => {
                    let events = events_of(&solver, dump_events);
                    log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
                    for (f, pc) in frame.backtrace().iter().rev() {
                        log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                    }
                    collected.push((Err(format!("Error {}", err)), events))
                }
            }
        },
    );

    println!("Execution took: {}ms", now.elapsed().as_millis());

    let mut result = vec![];

    loop {
        match queue.pop() {
            Some((Ok((new_frame, new_checkpoint)), mut events)) => {
                log!(
                    log::VERBOSE,
                    match get_opcode(new_checkpoint.clone(), opcode_var) {
                        Ok(model_opcode) => format!("Found {:#010x}", model_opcode),
                        Err(msg) => format!("Failed to retrieve opcode: {}", msg),
                    }
                );
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, shared_state);
                }
                result.push((new_frame, new_checkpoint));
            }

            // Error during execution
            Some((Err(msg), mut events)) => {
                println!("Failed path {}", msg);
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, shared_state);
                }
                if let Some(file_name) = assertion_reports {
                    if msg.starts_with("Assertion") {
                        let mut report_file = OpenOptions::new().append(true).create(true).open(file_name).unwrap();
                        write!(report_file, "{}", msg).unwrap();
                        let events: Vec<Event<B>> = events.drain(..).rev().collect();
                        write_events(&mut report_file, &events, shared_state);
                    }
                }
            }
            // Empty queue
            None => break,
        }
    }
    result
}

// Find a couple of scratch registers for the harness, and add a branch to one
// at the end of the test.
/// 为完整 testcase harness 选择 scratch 寄存器并追加最终跳转指令。
pub fn finalize<'ir, B: BV, T: Target>(
    target: &T,
    shared_state: &SharedState<'ir, B>,
    frame: &Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
) -> (u32, u32, Checkpoint<B>) {
    // 从事件 trace 里排除已被指令使用的 GPR，剩余寄存器用于 harness。
    let trace = checkpoint.trace().as_ref().expect("No trace!");
    let mut events = trace.to_vec();
    let mut regs: HashSet<u32> = (0..T::number_gprs()).collect();

    // TODO: move scratch register selection later, by splitting state
    // extraction into a symbolic bit then fill in values from the
    // model afterwards.

    // The events in the processor initialisation aren't relevant, so we take
    // them from the first instruction fetch.

    let mut post_init = false;
    for event in events.drain(..).rev() {
        match event {
            Event::ReadMem { .. } if event.is_ifetch() => post_init = true,
            Event::ReadReg(reg, _, _) | Event::WriteReg(reg, _, _) => {
                if post_init {
                    let name = shared_state.symtab.to_str(*reg);
                    if let Some(reg_num) = T::is_gpr(name) {
                        regs.remove(&reg_num);
                    }
                }
            }
            _ => (),
        }
    }

    let mut reg_iter = regs.iter();
    let entry_register = reg_iter.next().expect("No scratch registers available");
    let exit_register = reg_iter.next().expect("Not enough scratch registers available");

    // Add branch instruction at the end of the sequence
    let opcode: B = target.final_instruction(*exit_register);
    let (_, _, new_checkpoint, _) = setup_opcode(target, shared_state, &frame, opcode, None, checkpoint);

    (*entry_register, *exit_register, new_checkpoint)
}
