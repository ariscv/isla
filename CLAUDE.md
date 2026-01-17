# CLAUDE.md

所有的回答都使用中文

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Isla is a symbolic execution engine for Sail instruction set architecture specifications. It executes ISA specifications written in Sail (such as Armv8/Armv9 and RISC-V) and can evaluate them against axiomatic memory models using SMT solvers like Z3.

The project is a Rust workspace with multiple crates:
- `isla-lib` - Core symbolic execution engine library
- `isla-axiomatic` - Tool for checking axiomatic concurrency models
- `isla-cat` - Translator from cat memory models to SMTLIB
- `isla-mml`, `isla-sexp`, `isla-elf` - Supporting libraries
- `src/` - Multiple CLI utilities (property, footprint, execute-function, axiomatic, zencode, isarch)

## Build and Test Commands

### Building
```bash
cargo build --release
```

### Running tests
Tests are run via a Ruby script:
```bash
cd test && ruby run_tests.rb
```

### Building specific binaries
```bash
cargo build --bin isla-footprint --release
cargo build --bin isarch --release
# etc.
```

### Documentation
Generate and view local documentation:
```bash
cargo doc --open
```

## Architecture

### IR (Intermediate Representation)

Sail specifications are compiled to `.ir` files (see `rv32d.ir`, `rv64d.ir`). These are goto/conditional-branch languages that Isla symbolically executes.

Key IR concepts:
- **Functions**: Represented as `Def::Fn` with name, arguments, and body (a list of instructions)
- **Instructions**: `Decl`, `Init`, `Jump`, `Goto`, `Copy`, `Call`, etc.
- **Name encoding**: Sail names are encoded via `zencode` module (e.g., "MRET" → "zMRET")

### Symbolic Execution Engine (`isla-lib/src/executor.rs`)

Core structures:
- `SharedState<'ir, B>`: Contains functions, externs, symtab, type_info, registers, probes
- `LocalFrame<'ir, B>`: Execution stack frame with bindings
- `Task`: Unit of work for parallel execution
- `Frame<B>`: Union of `LocalFrame` or `UnfinishedFrame`

The executor explores execution paths by:
1. Creating tasks from local frames
2. Using `executor::start_multi` for parallel path exploration
3. Collecting results via a custom collector

### Z3 Integration (`isla-lib/src/smt.rs`)

- `Solver<B>`: SMT solver interface
- `Sym`: Symbolic variable wrapper
- `Event`: Execution events (read/write registers, memory ops, etc.)
- Checkpoints for thread sharing

### Configuration System

ISA configurations in `configs/*.toml` define:
- PC register name
- Initial register values
- Memory layout
- Toolchain paths
- Feature flags (RVC, PMP, etc.)

### Command Line Pattern

CLI tools follow a consistent pattern (see `src/opts.rs`):
1. Use `opts::common_opts()` to get shared options
2. Use `opts::parse()` to parse `-A` (arch) argument
3. Use `opts::parse_with_arch()` to get `CommonOpts` struct with symtab, arch, type_info, isa_config
4. Initialize architecture via `initialize_architecture()`

### Key Modules

- `ir.rs`, `ir_parser.lalrpop`, `ir_lexer.rs`: IR parsing (LALRPOP-based)
- `zencode.rs`: Name encoding/decoding for Sail identifiers
- `init.rs`: Architecture initialization (`initialize_architecture`)
- `smt.rs`: Z3 solver interface
- `executor.rs`, `executor/frame.rs`, `executor/task.rs`: Symbolic execution engine
- `config.rs`: ISA configuration loading

### IR Files

The `.ir` files (e.g., `rv32d.ir`) contain:
- Type definitions (`%union`, `%struct`, `%enum`)
- Function declarations (`val`, `fn`)
- Function bodies with `jump`, `goto`, assignments
- The `zexecute` function dispatches to instruction-specific handlers
- The `zassembly_forwards` function provides assembly name mappings

## Development Notes

### Adding a new CLI tool

1. Add `[[bin]]` entry to `Cargo.toml`
2. Create `src/<tool>.rs` following the pattern in `footprint.rs`:
   - Use `mod opts;` and `opts::common_opts()`
   - Call `opts::parse_with_arch()` to get `CommonOpts`
   - Use `initialize_architecture()` to initialize

### Working with symbolic names

- Use `zencode::encode()` to encode Sail names
- Use `zencode::decode()` to decode them
- Names in the symbol table (`Symtab`) are always encoded

### Debugging flags

Pass `-D <flags>` to tools:
- `f`: Control flow forks
- `m`: Memory accesses
- `l`: Litmus test compilation
- `p`: Probe information
- `g`: Graph visualization

### Z3 version

Tested with Z3 4.12.6. Install via:
```bash
apt install libz3-dev  # Ubuntu
opam install z3        # Alternative
```

Or place `libz3.so` in the repository root and set `LD_LIBRARY_PATH`.

## Isarch Tool

The `isarch` tool (in `src/isarch.rs` and `isla-lib/src/isarch.rs`) is a CLI utility for exploring RISC-V instruction execution through symbolic execution.

### Commands

```bash
# List all available instructions
cargo run --bin isarch --release -- -A ./rv32d.ir -C configs/riscv32.toml list-instructions

# Show execution path tree for an instruction (ASCII format)
cargo run --bin isarch --release -- -A ./rv32d.ir -C configs/riscv32.toml tree <instruction>

# Show execution path tree (Graphviz format)
cargo run --bin isarch --release -- -A ./rv32d.ir -C configs/riscv32.toml tree -g <instruction>
cargo run --bin isarch --release -- -A ./rv64d.ir -C configs/riscv64.toml tree -g <instruction>

# Solve for concrete ISA state values
cargo run --bin isarch --release -- -A ./rv32d.ir -C configs/riscv32.toml solve-state <instruction>
```

### Implementation Status

- `list-instructions`: ✅ Completed - identifies 27 RISC-V instructions
- `tree`: 🚧 In progress - requires symbolic execution integration
- `solve-state`: ⏳ Planned - requires Z3 solver integration

