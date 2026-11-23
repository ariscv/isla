//! 样本路径、合并记录与静态事实的完整镜像。
use super::{
    event::{Event, RegionPoint},
    expr::Exp,
    value::Val,
    CheckpointData,
};
use crate::executor::RegionRecordOutcome;
use crate::{bitvector::BV, ir::Name, smt::Accessor, source_loc::SourceLoc};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Facts {
    pub guard_unique: bool,
    pub post_unique: bool,
    pub simple_pre: bool,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PathData<B> {
    pub terminal: crate::executor::samples::Terminal,
    pub pre: BTreeMap<String, Val<B>>,
    pub post: BTreeMap<String, Val<B>>,
    pub result: Val<B>,
    pub memory: Vec<Event<B>>,
    pub memory_guards: Vec<(u64, Exp)>,
}
impl<B: BV> From<crate::executor::samples::SamplePath<B>> for PathData<B> {
    fn from(value: crate::executor::samples::SamplePath<B>) -> Self {
        Self {
            terminal: value.terminal,
            pre: value.pre.into_iter().map(|(n, v)| (n, v.into())).collect(),
            post: value.post.into_iter().map(|(n, v)| (n, v.into())).collect(),
            result: value.result.into(),
            memory: value.memory.into_iter().map(Into::into).collect(),
            memory_guards: value.memory_guards.into_iter().map(|(i, g)| (i.try_into().unwrap(), g.into())).collect(),
        }
    }
}
impl<B: BV> From<PathData<B>> for crate::executor::samples::SamplePath<B> {
    fn from(value: PathData<B>) -> Self {
        Self {
            terminal: value.terminal,
            pre: value.pre.into_iter().map(|(n, v)| (n, v.into())).collect(),
            post: value.post.into_iter().map(|(n, v)| (n, v.into())).collect(),
            result: value.result.into(),
            memory: value.memory.into_iter().map(Into::into).collect(),
            memory_guards: value
                .memory_guards
                .into_iter()
                .map(|(i, g)| (i.try_into().expect("缓存访存索引越界"), g.into()))
                .collect(),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Arm {
    Root,
    Then,
    Else,
    // 在已有枚举尾部追加投影角色，保持原记录的 JSON 和 bincode 布局。
    ProjectedRoot,
    ProjectedThen,
    ProjectedElse,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct GuardedRead<B> {
    pub register: Name,
    pub accessor: Vec<Accessor>,
    pub value: Val<B>,
    pub guard: Exp,
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Record<B> {
    pub record_id: u64,
    pub parent_record: Option<u64>,
    pub arm: Arm,
    pub function: Name,
    pub branch_pc: u64,
    pub join: RegionPoint,
    pub condition: u32,
    pub source_loc: SourceLoc,
    pub depth: u64,
    pub dead: bool,
    pub value_symbols: Vec<u32>,
    pub input_symbols: Vec<u32>,
    pub single_arm_reads: Vec<GuardedRead<B>>,
    pub memory_reads: Vec<(u64, Exp, Event<B>)>,
}
impl<B: Clone> From<crate::executor::RegionMergeRecord<B>> for Record<B> {
    fn from(value: crate::executor::RegionMergeRecord<B>) -> Self {
        let mut value_symbols = value.value_symbols.iter().map(|s| s.id).collect::<Vec<_>>();
        value_symbols.sort_unstable();
        let mut input_symbols = value.input_symbols.iter().map(|s| s.id).collect::<Vec<_>>();
        input_symbols.sort_unstable();
        Self {
            record_id: value.record_id.try_into().unwrap(),
            parent_record: value.parent_record.map(|i| i.try_into().unwrap()),
            arm: match (value.arm, value.outcome == RegionRecordOutcome::Projected) {
                ("root", false) => Arm::Root,
                ("then", false) => Arm::Then,
                ("else", false) => Arm::Else,
                ("root", true) => Arm::ProjectedRoot,
                ("then", true) => Arm::ProjectedThen,
                ("else", true) => Arm::ProjectedElse,
                (arm, _) => panic!("缓存记录臂无效：{arm}"),
            },
            function: value.function,
            branch_pc: value.branch_pc.try_into().unwrap(),
            join: value.join.into(),
            condition: value.condition.id,
            source_loc: value.source_loc,
            depth: value.depth.try_into().unwrap(),
            dead: value.outcome == RegionRecordOutcome::Dead,
            value_symbols,
            input_symbols,
            single_arm_reads: value
                .single_arm_reads
                .iter()
                .cloned()
                .map(|r| GuardedRead {
                    register: r.register,
                    accessor: r.accessor,
                    value: r.value.into(),
                    guard: r.guard.into(),
                })
                .collect(),
            memory_reads: value
                .memory_reads
                .iter()
                .cloned()
                .map(|(i, g, e)| (i.try_into().unwrap(), g.into(), e.into()))
                .collect(),
        }
    }
}
impl<B> From<Record<B>> for crate::executor::RegionMergeRecord<B> {
    fn from(value: Record<B>) -> Self {
        let outcome = match (&value.arm, value.dead) {
            (Arm::ProjectedRoot | Arm::ProjectedThen | Arm::ProjectedElse, false) => RegionRecordOutcome::Projected,
            (Arm::ProjectedRoot | Arm::ProjectedThen | Arm::ProjectedElse, true) => panic!("死亡记录不能是投影片段"),
            (_, true) => RegionRecordOutcome::Dead,
            (_, false) => RegionRecordOutcome::Merged,
        };
        Self {
            record_id: value.record_id.try_into().expect("缓存记录编号越界"),
            parent_record: value.parent_record.map(|i| i.try_into().expect("缓存父记录编号越界")),
            arm: match value.arm {
                Arm::Root | Arm::ProjectedRoot => "root",
                Arm::Then | Arm::ProjectedThen => "then",
                Arm::Else | Arm::ProjectedElse => "else",
            },
            function: value.function,
            branch_pc: value.branch_pc.try_into().unwrap(),
            join: value.join.into(),
            condition: crate::smt::Sym::from_u32(value.condition),
            source_loc: value.source_loc,
            depth: value.depth.try_into().unwrap(),
            outcome,
            value_symbols: std::sync::Arc::new(
                value.value_symbols.into_iter().map(crate::smt::Sym::from_u32).collect(),
            ),
            input_symbols: std::sync::Arc::new(
                value.input_symbols.into_iter().map(crate::smt::Sym::from_u32).collect(),
            ),
            single_arm_reads: value
                .single_arm_reads
                .into_iter()
                .map(|r| crate::executor::GuardedRegisterRead {
                    register: r.register,
                    accessor: r.accessor,
                    value: r.value.into(),
                    guard: r.guard.into(),
                })
                .collect(),
            memory_reads: value
                .memory_reads
                .into_iter()
                .map(|(i, g, e)| (i.try_into().expect("缓存访存索引越界"), g.into(), e.into()))
                .collect(),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CachedPath<B> {
    pub signature: u64,
    pub checkpoint: CheckpointData,
    pub path: PathData<B>,
    pub records: Vec<Record<B>>,
    pub facts: Facts,
    pub pure_definitions: Vec<(u32, u32)>,
}
