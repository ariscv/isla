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
use crate::ir::*;
use crate::smt::{Solver, Sym};
use crate::zencode;
use std::collections::HashMap;

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

/// Build a dictionary of instructions from the IR
///
/// This scans the IR for instructions by:
/// 1. Finding the zexecute function
/// 2. Extracting instruction dispatch tags (e.g., "jump zmergez3var is zMRET goto")
/// 3. Looking up assembly names via zassembly_forwards
pub fn build_instruction_dict<'ir, B: BV>(
    _arch: &[Def<Name, B>],
    symtab: &'ir Symtab<'ir>,
) -> Result<HashMap<String, InstructionInfo>, BuildError> {
    let mut instructions = HashMap::new();

    // Look for common RISC-V instructions in the symbol table
    // We encode the instruction name and look it up
    let known_instructions = [
        "mret", "sret", "uret", "ecall", "ebreak",
        "add", "sub", "mul", "div", "rem", "remu",
        "addi", "slti", "sltiu", "andi", "ori", "xori",
        "lw", "lh", "lb", "lhu", "lbu",
        "sw", "sh", "sb",
        "beq", "bne", "blt", "bge", "bltu", "bgeu",
        "jal", "jalr",
        "lui", "auipc",
        "slt", "sltu",
    ];

    for &instr_name in &known_instructions {
        // Try both lowercase and uppercase encodings
        for name_to_try in &[instr_name, &instr_name.to_uppercase()] {
            let encoded = zencode::encode(name_to_try);
            if let Some(name_id) = symtab.get(&encoded) {
                instructions.insert(
                    instr_name.to_string(), // Use lowercase as the key
                    InstructionInfo {
                        encoded_name: encoded,
                        assembly_name: instr_name.to_string(),
                        function_id: name_id,
                    },
                );
                break;
            }
        }
    }

    Ok(instructions)
}

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
    // 3. Use executor::start_multi to explore paths
    // 4. Collect paths using a custom collector
    Ok(Vec::new())
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

/// Format an execution tree as ASCII art
pub fn format_tree_ascii<B: BV>(paths: &[ExecutionPath<B>]) -> String {
    let mut output = String::new();

    if paths.is_empty() {
        output.push_str("(no paths)\n");
        return output;
    }

    // Simple tree rendering
    output.push_str(&format!("Instruction execution tree ({} paths):\n", paths.len()));
    output.push_str("\n");

    for (i, path) in paths.iter().enumerate() {
        output.push_str(&format!("Path {}:\n", i));
        for (j, cond) in path.conditions.iter().enumerate() {
            match cond {
                PathCondition::Initial => {
                    output.push_str(&format!("  [{}]: Entry point\n", j));
                }
                PathCondition::Branch { is_true, description, .. } => {
                    output.push_str(&format!("  [{}]: {} ({})\n", j, description, if *is_true { "true" } else { "false" }));
                }
            }
        }
        output.push_str(&format!("  -> Satisfiable: {}\n", path.satisfiable));
        output.push_str("\n");
    }

    output
}

/// Format an execution tree as Graphviz DOT format
pub fn format_tree_graphviz<B: BV>(paths: &[ExecutionPath<B>]) -> String {
    let mut output = String::new();

    output.push_str("digraph ExecutionTree {\n");
    output.push_str("  node [shape=box];\n");
    output.push_str("\n");

    // Create entry node
    output.push_str("  entry [label=\"Entry\"];\n");

    for (i, path) in paths.iter().enumerate() {
        let node_id = format!("path{}", i);
        let mut label = format!("Path {}\\n", i);

        for cond in &path.conditions {
            match cond {
                PathCondition::Initial => {
                    label.push_str("Entry point\\n");
                }
                PathCondition::Branch { is_true, description, .. } => {
                    label.push_str(&format!("{} ({})\\n", description, if *is_true { "T" } else { "F" }));
                }
            }
        }

        label.push_str(&format!("Sat: {}", path.satisfiable));
        output.push_str(&format!("  {} [label=\"{}\"];\n", node_id, label));
        output.push_str(&format!("  entry -> {};\n", node_id));
    }

    output.push_str("}\n");
    output
}
