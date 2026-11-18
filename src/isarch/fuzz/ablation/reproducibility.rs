//! 用相同父输入、目标类和随机流重复首个请求；只诊断通用取点，不执行硬件。
use super::super::{corpus::ClassIdentity, io, mutator::SolverMutator, random_stream, Mutator, Options};
use crate::isarch::{resident::ResidentPath, target::Target};
use isla_lib::{
    bitvector::BV,
    executor::samples::Sample,
    ir::SharedState,
    smt::{Config, Context, Solver},
};
use rand::RngCore;
use serde_json::{json, Value};

pub(in crate::isarch::fuzz) fn run<B: BV>(
    options: &Options,
    corpus: &[Sample],
    paths: &[ResidentPath<B>],
    shared: &SharedState<B>,
    target: &dyn Target<B>,
) {
    let mut comparisons = Vec::new();
    let mut all_equal = true;
    for input in corpus {
        let path = paths.iter().find(|path| path.signature == input.path_signature).unwrap();
        let context = Context::new(Config::new());
        let mut solver = Solver::from_checkpoint(&context, path.checkpoint.clone());
        let parent_row = path
            .path
            .judge(&mut solver, shared, input, &path.records, path.signature, |sample, model| {
                sample.isa_state = crate::isarch::samples::isa_state(target, sample, model, shared)?;
                Ok(())
            })
            .unwrap()
            .expect("重复性探针父输入未被指定路径接纳");
        let identity = ClassIdentity {
            scenario_config_id: options.scenario.clone(),
            path_signature: path.signature,
            guard_vector: parent_row.guard_vector,
        };
        let mut expected = None::<Value>;
        for trial in 0..options.budget {
            let context = Context::new(Config::new());
            let mutator = SolverMutator::new(path, &context, shared, target, &options.mutation_config);
            let mut rng = random_stream(options.random_seed, &options.scenario, 0);
            // 与campaign相同：先消耗形态A/B选择，再把剩余随机流交给求解器。
            rng.next_u64();
            let solver_seed = rng.clone().next_u64() as u32;
            let record = json!({"sample_id":0,"target_identity":identity,"operator":"A"});
            let sample = mutator.try_mutate(&parent_row.sample, &record, &mut rng).expect("重复性探针目标类不应耗尽");
            let state = json!({"pre_registers":sample.pre_registers,"pre_memory":sample.pre_memory});
            let equal = expected.as_ref().is_none_or(|value| value == &state);
            let differences = expected.as_ref().map(|previous| {
                state["pre_registers"]
                    .as_object()
                    .unwrap()
                    .iter()
                    .filter(|(name, value)| previous["pre_registers"][*name] != **value)
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>()
            });
            io::write_json(&options.output.join(format!("parent-{}-trial-{trial}.json", input.sample_id)), &state);
            comparisons.push(json!({"parent_sample_id":input.sample_id,"trial":trial,"solver_seed":solver_seed,"same_input":equal,"different_registers":differences}));
            eprintln!("[REPRODUCIBILITY_PROBE] {}", comparisons.last().unwrap());
            all_equal &= equal;
            expected.get_or_insert(state);
        }
    }
    io::write_json(
        &options.output.join("reproducibility.json"),
        &json!({"same_input":all_equal,"comparisons":comparisons,"seed":options.random_seed,"scenario":options.scenario,"scope":"同进程中独立上下文的首个请求；父输入仅指定路径judge"}),
    );
    assert!(all_equal, "相同随机流、父输入和目标类产生了不同输入");
}
