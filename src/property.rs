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

use sha2::{Digest, Sha256};
use std::process::exit;

use isla_lib::bitvector::b64::B64;
use isla_lib::executor::{ExecutionLimits, LocalFrame, TaskState};
use isla_lib::init::{initialize_architecture, Initialized};
use isla_lib::ir::*;
use isla_lib::zencode;

mod opts;
#[path = "property/paths.rs"]
mod paths;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

#[allow(clippy::mutex_atomic)]
fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("p", "property", "check property in architecture", "<id>");
    opts.optflag("", "optimistic", "assume assertions succeed");
    paths::add_options(&mut opts);

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B64>(&mut hasher, &opts);
    let CommonOpts { num_threads, mut arch, symtab, type_info, mut isa_config, source_path: _, .. } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);
    let path_options = match paths::PathOptions::parse(&matches) {
        Ok(options) => options,
        Err(error) => {
            eprintln!("{error}");
            return 3;
        }
    };
    if matches.opt_present("path-merging") {
        isa_config.execution_limits.get_or_insert_with(Default::default).path_merge.enabled = Some(true);
    }
    if let Some(config) = &isa_config.execution_limits {
        let options = isla_lib::config::RegionOptions::from_config(config);
        if let Err(error) = options.validate() {
            eprintln!("{error}");
            return 3;
        }
        options.configure();
        isla_lib::smt::configure_solver_options(isla_lib::smt::SolverOptions {
            incremental_choice_dag: config.path_merge.incremental_choice_dag,
            coi_query_slicing: config.path_merge.coi_query_slicing,
            ..Default::default()
        });
    }
    let use_model_reg_init = !matches.opt_present("no-model-reg-init");

    let assertion_mode =
        if matches.opt_present("optimistic") { AssertionMode::Optimistic } else { AssertionMode::Pessimistic };

    let Initialized { regs, lets, shared_state } =
        initialize_architecture(&mut arch, symtab, type_info, &isa_config, assertion_mode, use_model_reg_init);

    let property = zencode::encode(&matches.opt_str("property").unwrap());

    let function_id = shared_state.symtab.lookup(&property);
    let (args, ret_ty, instrs) = shared_state.functions.get(&function_id).unwrap();
    let task_state = TaskState::new();
    let task_state = match &isa_config.execution_limits {
        Some(config) => {
            let limits = ExecutionLimits::default().with_config(config, &shared_state.symtab);
            let enabled = limits.path_merging;
            task_state.with_execution_limits(limits.with_region_loop_analysis(enabled))
        }
        None => task_state,
    };
    let task_state = path_options.task_state(task_state);
    let mut frame = LocalFrame::new(function_id, args, ret_ty, None, instrs);
    frame.add_lets(&lets).add_regs(&regs);
    let task = path_options.task(&mut frame, &task_state);
    path_options.run(num_threads, task, &shared_state)
}
