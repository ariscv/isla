//! 选路和守卫类枚举保持原预算，可选在每个已取代表的类内检查共同输入域。
use super::{
    ablation::{check_constructible, input_domain::InputDomain},
    generation::{replace_witness, Replacement},
    random_stream, testcase,
};
use crate::isarch::{resident::ResidentPath, samples::isa_state, target::Target};
use isla_lib::{
    bitvector::BV,
    error::ExecError,
    executor::{
        samples::{outputs::SampleOutputs, Sample, SampleRandomization},
        ExecutionLimits, MergeEnumeration, TaskState,
    },
    ir::SharedState,
    smt::{smtlib::Exp, Model, Solver},
};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
    sync::Mutex,
};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub(super) struct Sampling {
    pub path_stride: usize,
    pub path_offset: usize,
    pub exclude_model_errors: bool,
    pub input_domain: Option<InputDomain>,
    pub domain_witness: bool,
    pub domain_witness_attempts: usize,
    pub domain_witness_timeout_ms: u32,
    pub platform: Option<PathBuf>,
}
impl Default for Sampling {
    fn default() -> Self {
        Self {
            path_stride: 1,
            path_offset: 0,
            exclude_model_errors: false,
            input_domain: None,
            domain_witness: false,
            domain_witness_attempts: 4,
            domain_witness_timeout_ms: 1000,
            platform: None,
        }
    }
}
impl Sampling {
    pub fn selected(&self, index: usize) -> bool {
        assert!(self.path_stride > 0 && self.path_offset < self.path_stride, "路径抽样参数越界");
        index % self.path_stride == self.path_offset
    }
}
pub(super) fn limits(source: &ExecutionLimits) -> ExecutionLimits {
    let mut limits = source.clone();
    limits.merge_enumeration.enabled = true;
    limits.merge_enumeration.mode = isla_lib::config::MergeEnumerationMode::Samples;
    limits.merge_enumeration.class_cap = 1;
    // 路径间并行；保留调用方的每路径上限和输出步长。
    limits.merge_enumeration.enumeration_threads = 1;
    limits.merge_enumeration.max_output_bytes = None;
    limits
}

#[derive(Clone, Copy, Default, Serialize)]
pub(super) struct WitnessStats {
    original_ok: usize,
    replaced: usize,
    empty_in_domain: usize,
    budget_exhausted: usize,
    classes_total: usize,
}

impl WitnessStats {
    pub fn add(&mut self, other: Self) {
        self.original_ok += other.original_ok;
        self.replaced += other.replaced;
        self.empty_in_domain += other.empty_in_domain;
        self.budget_exhausted += other.budget_exhausted;
        self.classes_total += other.classes_total;
    }
}

pub(super) struct WitnessExport<'a> {
    sampling: &'a Sampling,
    platform: Option<testcase::Platform>,
    provenance: Mutex<BufWriter<File>>,
}

impl<'a> WitnessExport<'a> {
    pub fn open(sampling: &'a Sampling, config: &Path, output: &Path) -> Self {
        assert!(
            sampling.domain_witness_attempts > 0 && sampling.domain_witness_timeout_ms > 0,
            "同类替代见证的次数和单次求解限时必须大于零"
        );
        let platform = sampling.platform.as_ref().map(|path| {
            let path = config.parent().unwrap().join(path);
            serde_json::from_reader(File::open(path).expect("读取构造平台失败")).expect("构造平台配置非法")
        });
        let provenance = Mutex::new(BufWriter::new(File::create(output.join("domain-witness.jsonl")).unwrap()));
        Self { sampling, platform, provenance }
    }

    pub fn finish(self) {
        self.provenance.into_inner().unwrap().flush().expect("写入见证来源失败");
    }

    pub fn export_path<B: BV>(
        &self,
        resident: &ResidentPath<B>,
        solver: &mut Solver<B>,
        shared: &SharedState<B>,
        target: &dyn Target<B>,
        limits: &ExecutionLimits,
        writer: &SampleOutputs,
        seed: u64,
    ) -> Result<(Value, WitnessStats), ExecError> {
        let domain = InputDomain::compile_optional(self.sampling.input_domain.as_ref(), &resident.path, shared)
            .expect("导出输入域配置无效");
        let state = TaskState::new().with_execution_limits(limits.clone());
        let output_path = writer.start_path(resident.signature);
        let pending_class = Mutex::new(None);
        let outcomes = Mutex::new((WitnessStats::default(), BTreeSet::new()));
        let randomization = SampleRandomization {
            seed: &|_, _| 0,
            prepare: &|class, solution, _, condition| {
                assert_eq!(solution, 0, "初始 corpus 每类只取一个代表");
                assert!(pending_class.lock().unwrap().replace((class, condition.clone())).is_none());
                Ok(())
            },
        };
        let mut enumeration = MergeEnumeration {
            records: &resident.records,
            pure_definitions: &resident.pure_definitions,
            signature: resident.signature,
        }
        .enumerate_merges_randomized_output_with(
            solver,
            &state,
            shared,
            &resident.path.result,
            &|class, solution, slices, truncated, model: &mut Model<B>| {
                let (prepared_class, class_condition) = pending_class.lock().unwrap().take().unwrap();
                assert_eq!(class, prepared_class);
                let mut original =
                    resident.path.materialize(model, shared, "merge", resident.signature, Some(class))?;
                original.isa_state = isa_state(target, &original, model, shared)?;
                let in_domain = match model.get_exp(&domain)?.unwrap_exp() {
                    Exp::Bool(in_domain) => in_domain,
                    _ => panic!("输入域必须是布尔表达式"),
                };
                let check = |sample: &Sample| {
                    self.platform.as_ref().map_or(Ok(()), |platform| check_constructible(sample, platform))
                };
                let exclusion =
                    if in_domain { check(&original).err() } else { Some(json!({"reasons":["input_domain"]})) };
                // 这里已具体化完整样本。枚举的截断标记只在导出时写回。
                original.truncated = truncated;
                let mut outcomes = outcomes.lock().unwrap();
                outcomes.0.classes_total += 1;
                let Some(exclusion) = exclusion else {
                    outcomes.0.original_ok += 1;
                    assert!(writer.append(output_path, solution, slices, original));
                    return Ok(());
                };
                let mut rng = random_stream(seed ^ resident.signature, "domain-witness", class as u64);
                let replacement = replace_witness(
                    resident,
                    shared,
                    target,
                    &original,
                    class_condition,
                    domain.clone(),
                    self.sampling.domain_witness_attempts,
                    self.sampling.domain_witness_timeout_ms,
                    || rng.next_u64(),
                    |sample| check(sample).is_ok(),
                )?;
                let (status, replacement) = match replacement {
                    Replacement::Found(sample) => {
                        outcomes.0.replaced += 1;
                        ("replaced", Some(sample))
                    }
                    Replacement::EmptyInDomain => {
                        outcomes.0.empty_in_domain += 1;
                        ("empty_in_domain", None)
                    }
                    Replacement::BudgetExhausted => {
                        outcomes.0.budget_exhausted += 1;
                        ("budget_exhausted", None)
                    }
                };
                let mut provenance = self.provenance.lock().unwrap();
                serde_json::to_writer(
                    &mut *provenance,
                    &json!({
                        "path_signature":resident.signature,"class_id":class,"domain_witness":status,
                        "source":"original","exclusion":exclusion,"sample":original
                    }),
                )
                .expect("记录原见证失败");
                writeln!(provenance).unwrap();
                if let Some(sample) = replacement {
                    serde_json::to_writer(
                        &mut *provenance,
                        &json!({
                            "path_signature":resident.signature,"class_id":class,"domain_witness":status,
                            "source":"replacement","sample":sample
                        }),
                    )
                    .expect("记录替代见证失败");
                    writeln!(provenance).unwrap();
                    assert!(writer.append(output_path, solution, slices, sample));
                } else {
                    outcomes.1.insert(class);
                }
                Ok(())
            },
            None,
            false,
            Some(&randomization),
        )?
        .expect("初始 corpus 必须开启枚举");
        let (stats, omitted) = outcomes.into_inner().unwrap();
        assert_eq!(enumeration["exported_samples"], stats.classes_total);
        let exported = stats.original_ok + stats.replaced;
        enumeration["exported_samples"] = json!(exported);
        enumeration["enumerated_total"] = json!(exported);
        for class in enumeration["guard_classes"].as_array_mut().unwrap() {
            if omitted.contains(&(class["class_id"].as_u64().unwrap() as usize)) {
                class["solution_count"] = json!(0);
            }
        }
        writer.finish_path(output_path, enumeration["path_truncated"].as_bool().unwrap());
        Ok((enumeration, stats))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isarch::target::RV64;
    use isla_lib::{
        bitvector::b64::B64,
        config::{SampleOutputConfig, SampleOutputFormat},
        executor::{
            samples::{SampleChecker, SamplePath, Terminal},
            RegionMergeRecord,
        },
        ir::{regions::RegionPoint, Symtab, Val},
        smt::{
            self,
            smtlib::{bits64, Ty},
            Config, Context, Event,
        },
        source_loc::SourceLoc,
        zencode,
    };
    use std::collections::BTreeMap;

    #[test]
    fn export_replaces_one_class_and_proves_the_other_empty_without_renumbering() {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let info = SourceLoc::unknown();
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let address = solver.declare_bitvector(64, info);
        let guard = solver.declare_const(Ty::Bool, info);
        let at = |value| Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(value, 64)));
        solver.assert(Exp::Ite(
            Box::new(Exp::Var(guard)),
            Box::new(at(0x1020)),
            Box::new(Exp::Or(Box::new(at(0x1000)), Box::new(at(0x1008)))),
        ));
        let mut symtab = Symtab::new();
        let entry = zencode::encode("entry");
        let function = symtab.intern(&entry);
        let shared = SharedState::empty(symtab);
        let resident = ResidentPath {
            checkpoint: smt::checkpoint(&mut solver),
            path: SamplePath {
                terminal: Terminal::Normal,
                pre: BTreeMap::from([("address".into(), Val::Symbolic(address))]),
                post: BTreeMap::new(),
                result: Val::Unit,
                memory: vec![Event::ReadMem {
                    value: Val::Bits(B64::new(7, 8)),
                    read_kind: Val::Unit,
                    address: Val::Symbolic(address),
                    bytes: 1,
                    tag_value: None,
                    opts: Default::default(),
                    region: "mem",
                }],
                memory_guards: BTreeMap::new(),
            },
            records: vec![RegionMergeRecord {
                record_id: 5,
                parent_record: None,
                arm: "root",
                function,
                branch_pc: 0,
                join: RegionPoint::FunctionExit,
                condition: guard,
                source_loc: info,
                depth: 1,
                dead: false,
                value_symbols: Default::default(),
                input_symbols: Default::default(),
                single_arm_reads: Vec::new(),
                memory_reads: Vec::new(),
            }],
            signature: 17,
            pure_definitions: vec![],
        };
        let scratch = std::env::temp_dir().join(format!("isarch-domain-witness-{}", std::process::id()));
        std::fs::create_dir(&scratch).unwrap();
        let target = RV64::<B64>::default();
        let limits = limits(&ExecutionLimits::default());
        let output = |name| SampleOutputConfig { format: SampleOutputFormat::V1Jsonl, path: scratch.join(name) };
        let baseline = output("baseline.jsonl");
        let writer = SampleOutputs::open(&[baseline.clone()]);
        let representative = SampleRandomization { seed: &|_, _| 0, prepare: &|_, _, _, _| Ok(()) };
        let baseline_enumeration = crate::isarch::samples::export_cached_path_randomized(
            &resident,
            &mut solver,
            &shared,
            &target,
            &limits,
            Some(&writer),
            None,
            Some(&representative),
        )
        .unwrap()
        .unwrap();
        writer.finish();
        let baseline = SampleChecker::load(&baseline.path, None).unwrap().samples;
        assert_eq!(baseline.len(), 2);
        assert_eq!(baseline[0].class_id, Some(0));
        assert_eq!(baseline[1].class_id, Some(1));
        let first_address = baseline[0].pre_memory[0].address;
        let alternative_address = if first_address == 0x1000 { 0x1008 } else { 0x1000 };
        let sampling = Sampling {
            domain_witness: true,
            input_domain: Some(InputDomain {
                check_whole_slot: true,
                slot_width: Some(8),
                allowed_ranges: vec![[alternative_address, alternative_address + 8]],
                ..Default::default()
            }),
            domain_witness_timeout_ms: 10_000,
            ..Default::default()
        };
        let witnesses = WitnessExport::open(&sampling, &scratch.join("sampling.json"), &scratch);
        let accepted = output("accepted.jsonl");
        let writer = SampleOutputs::open(&[accepted.clone()]);
        let (enumeration, stats) =
            witnesses.export_path(&resident, &mut solver, &shared, &target, &limits, &writer, 0).unwrap();
        witnesses.finish();
        writer.finish();
        assert_eq!(stats.classes_total, 2);
        assert_eq!(stats.replaced, 1);
        assert_eq!(stats.empty_in_domain, 1);
        assert_eq!(stats.budget_exhausted, 0);
        assert_eq!(enumeration["exported_samples"], 1);
        assert_eq!(enumeration["counted_classes"], baseline_enumeration["counted_classes"]);
        for (class, baseline) in enumeration["guard_classes"]
            .as_array()
            .unwrap()
            .iter()
            .zip(baseline_enumeration["guard_classes"].as_array().unwrap())
        {
            assert_eq!(class["class_id"], baseline["class_id"]);
            assert_eq!(class["guard_assignment"], baseline["guard_assignment"]);
        }
        assert_eq!(enumeration["guard_classes"][1]["solution_count"], 0);
        let accepted = SampleChecker::load(&accepted.path, None).unwrap().samples;
        assert_eq!(accepted.len(), 1);
        assert_eq!(accepted[0].class_id, Some(0));
        assert_eq!(accepted[0].pre_memory[0].address, alternative_address);
        let judged = resident
            .path
            .judge(&mut solver, &shared, &accepted[0], &resident.records, resident.signature, |_, _| Ok(()))
            .unwrap()
            .unwrap();
        assert_eq!(judged.guard_vector, "0");
        let rejected_by_constructor = replace_witness(
            &resident,
            &shared,
            &target,
            &baseline[0],
            Exp::Not(Box::new(Exp::Var(guard))),
            Exp::Bool(true),
            1,
            10_000,
            || 0,
            |_| false,
        )
        .unwrap();
        assert!(matches!(rejected_by_constructor, Replacement::BudgetExhausted));
        let lines = std::fs::read_to_string(scratch.join("domain-witness.jsonl")).unwrap();
        let rows: Vec<Value> = lines.lines().map(|line| serde_json::from_str(line).unwrap()).collect();
        assert_eq!(rows.len(), 3);
        assert_eq!(rows[0]["source"], "original");
        assert_eq!(rows[1]["source"], "replacement");
        assert_eq!(rows[0]["class_id"], rows[1]["class_id"]);
        assert_eq!(rows[0]["domain_witness"], "replaced");
        assert_eq!(rows[2]["domain_witness"], "empty_in_domain");
        std::fs::remove_dir_all(scratch).unwrap();
    }
}
