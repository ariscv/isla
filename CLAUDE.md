# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

Isla is a symbolic execution engine for Sail instruction set architecture (ISA) specifications. It executes Sail IR (Jib Intermediate Representation) symbolically using Z3 SMT solver to explore all possible execution paths, primarily used for:
- Symbolic execution of ISA specifications (ARMv8/ARMv9, RISC-V)
- Axiomatic memory model checking (isla-axiomatic)
- Instruction footprint analysis
- Test generation

## Build and Development Commands

### Building
```bash
cargo build --release
```

### Testing
```bash
make test           # Run all tests
make test-github    # CI-compatible tests
make -C isla-lib test   # Test individual crate
```

### Formatting
```bash
make fmt            # Format all code
cargo fmt           # Format Rust code
```

### Dependencies
- **Required**: Z3 SMT solver (libz3-dev on Ubuntu, tested with 4.12.6)
- **Optional OCaml tools**: isla-sail (Sail to IR compiler), isla-litmus (litmus test parser)

## Architecture

### Workspace Structure

```
isla/
├── isla-lib/          # Core symbolic execution engine library
├── isla-axiomatic/    # Axiomatic memory model checking
├── isla-cat/          # Cat language parser (memory models)
├── isla-mml/          # Memory model language utilities
├── isla-sexp/         # S-expression parsing
├── isla-elf/          # ELF file handling
├── configs/           # ISA configuration files (armv8p4.toml, riscv64.toml, etc.)
├── src/               # CLI executables (isa, isa-try, isla-footprint, isla-axiomatic, etc.)
└── test/              # Test cases and litmus tests
```

### isla-lib (Core Library)

The heart of the symbolic execution engine. Key modules:

- **executor.rs** - Core symbolic execution with parallel task execution using work-stealing queues
- **ir.rs** - Intermediate Representation (Jib IR from Sail): `Ty<Name>`, `Val<B>`, `Instr<Name, B>`, `Def<Name, B>`
- **smt.rs** - Z3 SMT solver interface with event logging and checkpointing for backtracking
- **primop.rs** - Primitive operations and builtins implementation
- **simplify.rs** - Symbolic expression simplification
- **memory.rs** - Memory region management (concrete, symbolic, read-only)
- **init.rs** - Architecture initialization from IR
- **config.rs** - ISA configuration file parsing (TOML)
- **register.rs** - Register file abstraction
- **bitvector.rs** - Bitvector operations (B64, B129 variants)

### Key Types and Concepts

**Symbolic Execution Model:**
- `LocalFrame<'ir, B>` - Stack frame with variables, registers, lets
- `LocalState<'ir, B>` - Thread-local execution state
- `SharedState<'ir, B>` - Global shared state (IR, symbol table, config)
- `Solver<B>` - Z3 solver wrapper with event logging
- `Task<'ir, '_, B>` - Executable task with frame and state
- `TaskId` - Unique identifier for execution paths (used in parallel exploration)

**IR Types:**
- `Name` - Interned identifier (u32 wrapper, use `symtab` to resolve)
- `Ty<Name>` - Types: Bits, Struct, Union, Vector, Float, etc.
- `Val<B>` - Values: concrete `Bits(B)` or symbolic `Symbolic(Sym)`
- `Sym` - Symbolic variable identifier
- `Instr<Name, B>` - Instructions: goto, if, perform, call, etc.

**Execution Flow:**
```
Sail Specification -> isla-sail (OCaml) -> Jib IR (.ir file) ->
initialize_architecture() -> SharedState + LocalFrame ->
Executor (parallel path exploration) -> Z3 Solver + SMTLIB Trace
```

### isla-axiomatic (Concurrency Testing)

Combines symbolic execution with axiomatic memory models:
- **run_litmus.rs** - Litmus test execution infrastructure
- **footprint_analysis.rs** - Analyzes instruction memory access patterns
- **smt_events.rs** - Converts execution traces to SMT constraints
- **page_table.rs** - Virtual memory and address translation support

Workflow: Parse litmus test (TOML) -> Assemble instructions -> Extract footprints -> Convert to SMT -> Check against memory model

### CLI Tools (src/)

- **isa / isa-try** - Instruction symbolic execution
- **isla-axiomatic** - Run litmus tests against memory models
- **isla-footprint** - Generate instruction footprints
- **isla-property** - Check properties symbolically
- **zencode** - Encode/decode Z3 names

## Configuration System

Architecture configurations in `configs/` directory control:
- PC register name
- Toolchain settings (assembler, linker, objdump)
- Memory regions (threads base/top, symbolic addresses)
- MMU configuration (page tables)
- Default register values

Example: `configs/armv8p5.toml`, `configs/riscv64.toml`

## Symbolic Execution Patterns

### Path Exploration
Isla creates new tasks at branches (never merges) using `start_single()` or parallel execution. This simplifies the engine but can cause exponential path explosion.

### Function Linearisation
The `-L` flag statically rewrites if-statements into linear form using `ite` (if-then-else) expressions to avoid path explosion:
```
if undefined { x = x + 1 } else { x = x + 2 }
-->
let b = undefined; let x1 = x + 1; let x2 = x + 2; let x3 = ite(b, x1, x2)
```

### Checkpointing
Use `smt::checkpoint(&mut solver)` to snapshot solver state for efficient backtracking. Fork operations push checkpoints that can be popped later.

### Events
The `Event<B>` enum tracks execution:
- `Fork(counter, sym, branch_idx, info)` - Control flow split
- `Assume(exp)` - Path constraint
- `ReadReg`/`WriteReg` - Register access
- `ReadMem`/`WriteMem` - Memory access

## Current Development Branch (symble-isa-dev)

Active work on CFG construction for symbolic execution:
- **src/cfg.rs** - Control Flow Graph construction with path tracking
- **src/isa-try.rs** - New ISA symbolic execution tool with CFG integration

The CFG system tracks:
- `CFGNode<B>` - Instruction execution points with path IDs
- `ForkCondition` - Symbolic branch conditions
- `CFGTree<B>` - Complete CFG with path relationships

## Bit Width Parameterization

The codebase uses generic `B: BV` trait for bitvector operations:
- `B64` - 64-bit operations
- `B129` - 129-bit operations (used for 128-bit + tag)
- Most ISA code uses `B129` for ARMv8/ARMv9

## Testing Infrastructure

- `test/axiomatic/` - Litmus test cases (TOML format)
- `test/run_tests.rb` - Ruby test harness
- Per-crate tests in each subdirectory

## Documentation

- `README.md` - Project overview and build instructions
- `doc/manual.adoc` - Command-line tool manual
- `doc/axiomatic.adoc` - Axiomatic concurrency tool manual
- `doc/translation.adoc` - Virtual memory translation guide
