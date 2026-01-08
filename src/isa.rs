// BSD 2-Clause License
//
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
use sha2::digest::generic_array::functional;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::fs::File;
use std::io::{BufWriter, Read, Write};
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use isla_axiomatic::footprint_analysis::footprint_analysis;
use isla_axiomatic::litmus::assemble_instruction;
use isla_axiomatic::page_table;
use isla_axiomatic::page_table::setup::PageTableSetup;
use isla_elf::arch::AArch64;
use isla_elf::elf;
use isla_elf::relocation_types::SymbolicRelocation;
use isla_lib::bitvector::{b129::B129, BV};
use isla_lib::error::IslaError;
use isla_lib::{d, d1, d2, d3, executor};
use isla_lib::executor::{start_single, LocalFrame, LocalState, StopAction, StopConditions, TaskId, TaskState};
use isla_lib::init::{initialize_architecture, InitArchWithConfig};
use isla_lib::ir::*;
use isla_lib::log;
use isla_lib::memory::Memory;
use isla_lib::register::Register;
use isla_lib::simplify;
use isla_lib::simplify::{EventTree, WriteOpts};
use isla_lib::smt::{self, Sym};
use isla_lib::smt::{smtlib, Checkpoint, EvPath, Event, Solver};
use isla_lib::smt_parser;
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use isla_lib::dprint::*;
use isla_lib::fraction::Fraction;
use isla_lib::ir::Val;

mod opts;
use opts::CommonOpts;
use opts::Architecture;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

pub fn hex_bytes(s: &str) -> Result<Vec<u8>, std::num::ParseIntError> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16)).collect()
}

#[derive(Clone, Debug)]
enum InstructionSegment<B> {
    Concrete(B),
    Symbolic(String, u32),
}

impl<B: BV> std::fmt::Display for InstructionSegment<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            InstructionSegment::Concrete(bv) => write!(f, "{}", bv),
            InstructionSegment::Symbolic(s, len) => write!(f, "{}:{}", s, len),
        }
    }
}

fn instruction_to_string<B: BV>(opcode: &[InstructionSegment<B>]) -> String {
    let mut s = "".to_string();
    for seg in opcode {
        s += &format!("{} ", seg);
    }
    s
}

fn instruction_to_val<B: BV>(
    opcode: &[InstructionSegment<B>],
    constraints: &[String],
    solver: &mut Solver<B>,
) -> Val<B> {
    match opcode {
        [InstructionSegment::Concrete(bv)] => Val::Bits(*bv),
        _ => {
            print!("(segments");
            let mut var_map = HashMap::new();
            let val = Val::MixedBits(
                opcode
                    .iter()
                    .map(|segment| match segment {
                        InstructionSegment::Concrete(bv) => BitsSegment::Concrete(*bv),
                        InstructionSegment::Symbolic(name, size) => {
                            if let Some((size2, v)) = var_map.get(name) {
                                if size == size2 {
                                    BitsSegment::Symbolic(*v)
                                } else {
                                    panic!(
                                        "{} appears in instruction with different sizes, {} and {}",
                                        name, size, size2
                                    )
                                }
                            } else {
                                let v = solver.declare_const(smtlib::Ty::BitVec(*size), SourceLoc::unknown());
                                print!("\n  (|{}| {} v{})", name, size, v);
                                var_map.insert(name, (*size, v));
                                BitsSegment::Symbolic(v)
                            }
                        }
                    })
                    .collect(),
            );
            println!(")");
            for constraint in constraints {
                let mut lookup = |loc: &Loc<String>| match loc {
                    Loc::Id(name) => match var_map.get(&zencode::decode(name)) {
                        Some((_size, v)) => Ok(smtlib::Exp::Var(*v)),
                        None => Err(format!("No variable {} in constraint", name)),
                    },
                    _ => Err(format!("Only names can appear in instruction constraints, not {}", loc)),
                };
                let assertion = smt_parser::ExpParser::new().parse(constraint).expect("Bad instruction constraint");
                solver.add_event(Event::Assume(assertion.clone()));
                let assertion_exp = assertion.map_var(&mut lookup).expect("Bad instruction constraint");
                solver.add(smtlib::Def::Assert(assertion_exp));
            }
            val
        }
    }
}

fn opcode_bytes<B: BV>(opcode: Vec<u8>, little_endian: bool) -> B {
    if opcode.len() > 8 {
        eprintln!("Currently instructions greater than 8 bytes in length are not supported");
        exit(1);
    }

    if opcode.len() == 2 {
        let opcode: Box<[u8; 2]> = opcode.into_boxed_slice().try_into().unwrap();
        B::from_u16(if little_endian { u16::from_le_bytes(*opcode) } else { u16::from_be_bytes(*opcode) })
    } else if opcode.len() == 4 {
        let opcode: Box<[u8; 4]> = opcode.into_boxed_slice().try_into().unwrap();
        B::from_u32(if little_endian { u32::from_le_bytes(*opcode) } else { u32::from_be_bytes(*opcode) })
    } else {
        B::from_bytes(&opcode)
    }
}

fn parse_elf_function_offset(input: &str) -> Option<(&str, u64)> {
    let (symbol, offset) = input.split_once(':')?;

    match offset.parse::<u64>() {
        Ok(offset) => Some((symbol, offset)),
        Err(_) => {
            let bv = B129::from_str(offset)?;
            Some((symbol, bv.lower_u64()))
        }
    }
}

#[allow(dead_code)]
struct OpcodeInfo<'a, B> {
    call: Name,
    args: Vec<&'a str>,
    bits: B,
    mask: B,
    slice: Vec<(&'a str, u32, u32)>,
    see: Option<i64>,
}

impl<'a, B: BV> OpcodeInfo<'a, B> {
    fn parse<'b>(value: &'a toml::Value, symtab: &'b Symtab) -> Result<Self, String> {
        let Some(call_str) = value.get("call").and_then(toml::Value::as_str) else {
            return Err("Could not parse call field as string in opcode info".to_string());
        };

        let Some(call) = symtab.get(&zencode::encode(call_str)) else {
            return Err(format!("Could not find function {}", call_str));
        };

        let Some(args) = value
            .get("args")
            .and_then(toml::Value::as_array)
            .and_then(|arr| arr.iter().map(toml::Value::as_str).collect::<Option<Vec<_>>>())
        else {
            return Err(format!("Could not parse args field in opcode info for {}", call_str));
        };

        let bits = match value.get("bits").and_then(toml::Value::as_str) {
            Some(hex_str) => match hex_bytes(hex_str) {
                Ok(bytes) => opcode_bytes(bytes, false),
                Err(e) => return Err(format!("Could not parse hexadecimal bits {} for {}: {}", hex_str, call_str, e)),
            },
            None => return Err(format!("Expected string value for bits field in opcode info for {}", call_str)),
        };

        let mask = match value.get("mask").and_then(toml::Value::as_str) {
            Some(hex_str) => match hex_bytes(hex_str) {
                Ok(bytes) => opcode_bytes(bytes, false),
                Err(e) => return Err(format!("Could not parse hexadecimal mask {} for {}: {}", hex_str, call_str, e)),
            },
            None => return Err(format!("Expected string value for mask field in opcode info for {}", call_str)),
        };

        let slice = match value.get("slice").and_then(toml::Value::as_table) {
            Some(table) => {
                let mut slice = Vec::new();
                for (arg, indices) in table.iter() {
                    if let Some(ix) = indices.as_array() {
                        if ix.len() == 1 || ix.len() == 2 {
                            let Some(hi) = ix[0].as_integer().and_then(|i| u32::try_from(i).ok()) else {
                                return Err(format!("Failed to parse integer slice index {} for {}", arg, call_str));
                            };
                            let Some(lo) = ix[ix.len() - 1].as_integer().and_then(|i| u32::try_from(i).ok()) else {
                                return Err(format!("Failed to parse integer slice index {} for {}", arg, call_str));
                            };
                            slice.push((arg.as_str(), hi, lo))
                        } else {
                            return Err(format!("Incorrect slice length {} for {}", arg, call_str));
                        }
                    }
                }
                slice
            }
            None => return Err(format!("Expected table value for slice field in opcode info for {}", call_str)),
        };

        let see = match value.get("see") {
            Some(v) => {
                if let Some(i) = v.as_integer() {
                    Some(i)
                } else {
                    return Err(format!("Could not parse see field in opcode info for {}", call_str));
                }
            }
            None => None,
        };

        Ok(OpcodeInfo { call, args, bits, mask, slice, see })
    }

    fn to_instruction_segments(&self, constraints: &mut Vec<String>) -> Vec<InstructionSegment<B>> {
        let length = self.bits.len();
        let mut current = length - 1;

        let mut ordered_slices = self.slice.clone();
        ordered_slices.sort_by(|(_, hi1, _), (_, hi2, _)| hi2.cmp(hi1));

        let mut segments = Vec::new();
        for (field, hi, lo) in ordered_slices {
            if current > hi {
                segments.push(InstructionSegment::Concrete(self.bits.extract(current, hi + 1).unwrap()))
            }
            let bits = self.bits.extract(hi, lo).unwrap();
            let mask = self.mask.extract(hi, lo).unwrap();
            if mask == B::ones((hi - lo) + 1) {
                segments.push(InstructionSegment::Concrete(bits))
            } else if mask.is_zero() {
                segments.push(InstructionSegment::Symbolic(field.to_string(), (hi - lo) + 1))
            } else {
                segments.push(InstructionSegment::Symbolic(field.to_string(), (hi - lo) + 1));
                constraints.push(format!("(= (bvand {} {}) {})", field, mask, bits));
            }
            current = lo - 1
        }
        if current != u32::MAX {
            segments.push(InstructionSegment::Concrete(self.bits.extract(current, 0).unwrap()))
        }

        segments
    }
}

fn isla_main() -> i32 {
    let now = Instant::now();

    let mut opts = opts::common_opts();
    opts.reqopt("i", "instruction", "display footprint of instruction", "<instruction>");
    opts.optopt("e", "endianness", "instruction encoding endianness (default: little)", "big/little");
    opts.optopt("", "elf", "load an elf file, and use instructions from it", "<file>");
    opts.optflag("d", "dependency", "view instruction dependency info");
    opts.optflag("x", "hex", "parse instruction as hexadecimal opcode, rather than assembly");
    opts.optflag("s", "simplify", "simplify instruction footprint");
    opts.optflag("", "simplify-registers", "simplify register accesses in traces");
    opts.optflag("", "hide", "hide uninteresting trace elements");
    opts.optflag("t", "tree", "combine traces into tree");
    opts.optopt("f", "function", "use a custom footprint function", "<identifer>");
    opts.optflag("c", "continue-on-error", "continue generating traces upon encountering an error");
    opts.optopt("", "armv8-page-tables", "set up page tables with provided constraints", "<constraints>");
    opts.optflag("", "zero-memory", "treat all memory as being zero");
    opts.optflag("", "partial", "parse instruction as binary with unknown bits");
    opts.optopt("", "from-file", "parse instruction from opcodes file", "<file>");
    opts.optmulti("", "instruction-constraint", "add constraint on variables in a partial instruction", "<constraint>");
    opts.optflag("", "eval-carefully", "during simplification check the results of symbolic evaluation");
    opts.optmulti(
        "k",
        "kill-at",
        "stop executions early and discard if they reach this function (with optional context)",
        "<function name[, function_name]>",
    );
    opts.optmulti(
        "",
        "stop-at",
        "stop executions early and keep trace if they reach this function (with optional context)",
        "<function name[, function_name]>",
    );
    opts.optflag("", "pessimistic", "fail on any assertion that is not necessarily true");
    opts.optopt("", "timeout", "Add a timeout (in seconds)", "<n>");
    opts.optflag("", "executable", "make trace executable");

    let mut hasher = Sha256::new();
    let (matches, arch ) :(_, Architecture<B129>) = opts::parse(&mut hasher, &opts);
    if !matches.free.is_empty() {
        eprintln!("Unexpected arguments: {}", matches.free.join(" "));
        exit(1)
    }
    let CommonOpts { num_threads, mut arch, symtab, type_info, isa_config, source_path } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);









    // Note this is the opposite default to other tools
    let assertion_mode =
        if matches.opt_present("pessimistic") { AssertionMode::Pessimistic } else { AssertionMode::Optimistic };

    let use_model_reg_init = !matches.opt_present("no-model-reg-init");
    let iarch = initialize_architecture(&mut arch, symtab, type_info, &isa_config, assertion_mode, use_model_reg_init);
    let iarch_config = InitArchWithConfig::from_initialized(&iarch, &isa_config);
    let regs = &iarch.regs;
    let lets = &iarch.lets;
    let shared_state = &&iarch.shared_state;

    log!(log::VERBOSE, &format!("Parsing took: {}ms", now.elapsed().as_millis()));





    // let (initial_checkpoint, mut solver)= {
    let solver_cfg = smt::Config::new();
    let solver_ctx = smt::Context::new(solver_cfg);
    let mut solver = Solver::<B129>::new(&solver_ctx);;

    // Record register assumptions from defaults; others are recorded at reset-registers
    let mut sorted_regs: Vec<(&Name, &Register<_>)> = regs.iter().collect();
    sorted_regs.sort_by_key(|(name, _)| *name);
    for (name, reg) in sorted_regs {
        if let Some(value) = reg.read_last_if_initialized() {
            solver.add_event(Event::AssumeReg(*name, vec![], value.clone()))
        }
    }
    // (smt::checkpoint(&mut solver),solver)
    // };



    /* let function_id = shared_state.symtab.lookup("zfmod_int");
    let function_initvalue = Some([Val::<B129>::I128(2),Val::<B129>::I128(2)].as_slice()); */

	// let function_id = shared_state.symtab.lookup("execute_aarch64_instrs_memory_literal_simdfp");
    // let function_initvalue = Some([Val::<B129>::I128(2),Val::<B129>::I128(2)].as_slice());

	let function_id = shared_state.symtab.lookup("zneq_int");
    let function_initvalue = Some([Val::<B129>::I128(2),Val::<B129>::I128(2)].as_slice());

    //d1!(id,shared_state.symtab.to_str(Name::from_u32(29)));
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
    // let mut frame = LocalFrame::new(function_id, args, ret_ty, None, instrs);

    let mut frame =  LocalFrame::new(
        function_id ,args,ret_ty,
		
		// 初始化函数的两个形式参数
		// Some(&[Val::I128(2),Val::I128(2)]),
		// Some(&[Val::Symbolic(Sym::from_u32(1000)),Val::Symbolic(Sym::from_u32(1001)) ]),
		function_initvalue,

        instrs,
    );
    // frame.vars_mut().insert(shared_state.symtab.lookup("zn"), UVal::Init(Val::I128(2)) );
    // frame.vars_mut().insert(shared_state.symtab.lookup("zm"), UVal::Init(Val::I128(2)) );




    let task_state = TaskState::new();
    let task = {
        LocalFrame::new(REGISTER_INIT, &[], &Ty::Unit, None, instrs)
            .task(TaskId::fresh(), &task_state)
    };

    start_single(
        task,
        shared_state,
        &(),
        &move |_tid, _task_id, result, _shared_state, _solver, _| match result {
            Ok((_, frame)) => {
                println!("okkkkkkk");
            }
            Err(err) => log!(log::VERBOSE, &format!("Failed to evaluate register initialiser: {:?}", err)),
        },
    );


	shared_state.functions.keys().into_iter().for_each(|k|{
		let zname=shared_state.symtab.to_str(*k);

		println!("{}",zencode::decode(zname));
	}) ;

    0
}

