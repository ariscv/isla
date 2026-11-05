//! 函数内区域的纯静态分析，不调用解释器或 SMT 求解器。
//!
//! 图中的 pc 均指原始指令序列。虚拟出口用 [`RegionPoint::FunctionExit`]
//! 表示，绝不作为真实指令交给调用者。调用形态的 Sail exit 没有固定的
//! `Name`，分析未经规范化的 IR 时须通过 [`RegionOptions::terminal_calls`]
//! 传入相应名字；解析后的 `Exit`、match failure 和断言失败直接识别。
//!
//! 区域只说明控制流结构；它不证明调用纯度、没有递归或没有内存副作用。

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::sync::{Arc, OnceLock};

use petgraph::algo::dominators::{simple_fast, Dominators};
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::{EdgeRef, Reversed};
use petgraph::Direction;

use super::ssa::{Edge, Terminator, CFG};
use super::{Exp, Instr, LabeledInstr, Loc, Name, Op, RETURN, SAIL_ASSERT};
use crate::bitvector::BV;
use crate::primop;

/// 区域边界或 CFG 后继；函数出口独立于任何 pc。
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RegionPoint {
    Instruction(usize),
    FunctionExit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeKind {
    Jump(bool),
    Goto,
    Continue,
    Terminate,
    AssertionFailure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionKind {
    Reconvergent,
    /// 两臂在统一出口汇合；可能包含返回、Arbitrary 或异常终止。
    /// 执行层仍须检查终止原因是否允许合并。
    FunctionReturn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region {
    pub branch_pc: usize,
    pub join: RegionPoint,
    /// 入口 Jump 与 join 均不包含在内，按原始 pc 排序。
    pub nodes: BTreeSet<usize>,
    pub kind: RegionKind,
    /// 区域内 Decl/Init 且区域离开后不再读取的名字，可在提交处丢弃。
    pub local_variables: BTreeSet<Name>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionRejection {
    NotJump,
    ExceptionCheck,
    NoJoin,
    HasBackEdge,
    ExitsRegion { from: usize, to: RegionPoint },
}

/// `None` 保留异常边，供诊断和对比使用。`Some(name)` 按边的极性剔除。
#[derive(Clone, Copy, Debug)]
pub struct RegionOptions<'a> {
    pub have_exception: Option<Name>,
    /// 原始 Call 形式的无返回函数（包括 Sail exit），由调用者解析名字。
    pub terminal_calls: &'a [Name],
}

/// 统一出口的指令级 CFG。结构边来自 SSA CFG，边界保留 Jump 的真/落空极性。
///
/// SSA CFG 的字段和后继均公开，但变量枚举方法仅供其模块内部使用。
/// 本模块复用 `Exp::collect_ids` 枚举表达式读取，再补充子位置与地址逃逸。
/// SSA CFG 不接受 PrimopReset，也不识别调用形态的终止；仅在建图副本中
/// 把它们规范化，原始指令始终用于变量分析。
pub struct RegionCfg {
    graph: Graph<RegionPoint, EdgeKind>,
    pcs: Vec<NodeIndex>,
    exit: NodeIndex,
    postdominators: Dominators<NodeIndex>,
    declarations: HashMap<Name, BTreeSet<usize>>,
    jump_pcs: HashSet<usize>,
    exception_pcs: HashSet<usize>,
}

fn exception_polarity(exp: &Exp<Name>, name: Name) -> Option<bool> {
    match exp {
        Exp::Id(id) if *id == name => Some(true),
        Exp::Call(Op::Not, args) if matches!(args.as_slice(), [Exp::Id(id)] if *id == name) => Some(false),
        _ => None,
    }
}

impl RegionCfg {
    pub fn new<B: BV>(instrs: &[Instr<Name, B>], options: RegionOptions<'_>) -> Self {
        let len = instrs.len();
        // 每条指令带标签：复用 SSA 的基本块切分、跳转目标解析和后继构造，
        // 同时使每个块对应一个原始 pc。尾部补 End，保留空函数和尾部非终止指令。
        let binary_primops = primop::binary_primops::<B>();
        let assertions = [binary_primops["optimistic_assert"], binary_primops["pessimistic_assert"]];
        let mut failure_pcs = HashSet::new();
        let mut jump_pcs = HashSet::new();
        let mut exception_pcs = HashSet::new();
        let mut normalized = Vec::with_capacity(len + 1);
        for (pc, instr) in instrs.iter().enumerate() {
            let mut assertion = None;
            match instr {
                Instr::Goto(target) | Instr::Jump(_, target, _) => {
                    assert!(*target <= len, "跳转目标超出函数：{} → {}", pc, target)
                }
                _ => (),
            }
            match instr {
                Instr::Call(_, _, name, args, _) if *name == SAIL_ASSERT => {
                    assert_eq!(args.len(), 2, "断言必须有条件和消息两个参数");
                    assertion = Some(&args[0]);
                }
                Instr::PrimopBinary(_, f, condition, _, _)
                    if assertions.iter().any(|assertion| std::ptr::fn_addr_eq(*assertion, *f)) =>
                {
                    assertion = Some(condition);
                }
                Instr::Jump(condition, _, _) => {
                    jump_pcs.insert(pc);
                    if options.have_exception.and_then(|name| exception_polarity(condition, name)).is_some() {
                        exception_pcs.insert(pc);
                    }
                }
                _ => (),
            }
            if let Some(condition) = assertion {
                if !matches!(condition, Exp::Bool(true)) {
                    failure_pcs.insert(pc);
                }
            }
            let normalized_instr = match instr {
                Instr::Call(_, _, name, _, info) if options.terminal_calls.contains(name) => {
                    Instr::Exit(super::ExitCause::Explicit, *info)
                }
                Instr::Call(_, _, _, _, info) | Instr::PrimopBinary(_, _, _, _, info)
                    if matches!(assertion, Some(Exp::Bool(false))) =>
                {
                    Instr::Exit(super::ExitCause::AssertionFailure, *info)
                }
                Instr::PrimopReset(loc, _, _, info) => Instr::Copy(loc.clone(), Exp::Unit, *info),
                _ => instr.clone(),
            };
            normalized.push(LabeledInstr::Labeled(pc, normalized_instr));
        }
        normalized.push(LabeledInstr::Labeled(len, Instr::End));
        let cfg = CFG::new(&normalized);
        assert_eq!(cfg.graph.node_count(), len + 1, "SSA CFG 必须保留所有指令标签");
        let mut declarations: HashMap<Name, BTreeSet<usize>> = HashMap::new();
        for ix in cfg.graph.node_indices() {
            let block = &cfg.graph[ix];
            for instr in &block.instrs {
                if let Some(name) = instr.declares() {
                    declarations.entry(name).or_default().insert(block.label.expect("指令基本块必须有标签"));
                }
            }
        }
        let mut graph = Graph::new();
        let pcs: Vec<_> = (0..len).map(|pc| graph.add_node(RegionPoint::Instruction(pc))).collect();
        let exit = graph.add_node(RegionPoint::FunctionExit);
        let indices: Vec<_> = cfg
            .graph
            .node_indices()
            .map(|ix| {
                let label = cfg.graph[ix].label.expect("指令基本块必须有标签");
                if label == len {
                    exit
                } else {
                    pcs[label]
                }
            })
            .collect();
        for edge in cfg.graph.edge_references() {
            let source = indices[edge.source().index()];
            let target = indices[edge.target().index()];
            let kind = match edge.weight().1 {
                Edge::Jump(polarity) => {
                    let RegionPoint::Instruction(pc) = graph[source] else { panic!("虚拟出口不能跳转") };
                    let Instr::Jump(condition, _, _) = &instrs[pc] else { panic!("Jump 边必须来自 Jump") };
                    if options.have_exception.and_then(|name| exception_polarity(condition, name)) == Some(polarity) {
                        continue;
                    }
                    EdgeKind::Jump(polarity)
                }
                Edge::Goto => EdgeKind::Goto,
                Edge::Continue => EdgeKind::Continue,
                Edge::MultiJump(_) => panic!("原始指令不能生成 MultiJump"),
            };
            graph.add_edge(source, target, kind);
        }
        for ix in cfg.graph.node_indices() {
            let source = indices[ix.index()];
            if source != exit
                && matches!(cfg.graph[ix].terminator, Terminator::End | Terminator::Arbitrary | Terminator::Exit(..))
            {
                graph.add_edge(source, exit, EdgeKind::Terminate);
            }
        }
        for pc in failure_pcs {
            if !graph.contains_edge(pcs[pc], exit) {
                graph.add_edge(pcs[pc], exit, EdgeKind::AssertionFailure);
            }
        }
        let postdominators = simple_fast(Reversed(&graph), exit);
        Self { graph, pcs, exit, postdominators, declarations, jump_pcs, exception_pcs }
    }

    pub fn instruction_count(&self) -> usize {
        self.pcs.len()
    }

    /// 返回的边保留极性，即使真边与落空边指向同一节点也不合并。
    pub fn successors(&self, pc: usize) -> impl Iterator<Item = (RegionPoint, EdgeKind)> + '_ {
        self.graph.edges(self.pcs[pc]).map(|edge| (self.graph[edge.target()], *edge.weight()))
    }

    /// 在完整 CFG 上证明每条路径有限终止；normal_return 决定是否允许正常返回。
    /// 两个入口状态分别表示 have_exception 为假/真，不能依赖调用前已有异常。
    /// 从未证明开始反向传播，环和未经证明的递归调用不会自行获得证明。
    pub fn always_terminates<B: BV>(
        &self,
        instrs: &[Instr<Name, B>],
        have_exception: Name,
        terminal_calls: &HashSet<Name>,
        terminating_calls: &HashMap<Name, bool>,
        normal_return: bool,
    ) -> bool {
        assert_eq!(instrs.len(), self.pcs.len(), "终止分析必须使用建图时的指令");
        if instrs.is_empty() {
            return false;
        }
        assert!(self.exception_pcs.is_empty(), "终止证明不能剔除异常边");
        let mut proven = vec![[false; 2]; instrs.len()];
        let mut pending: VecDeque<_> = (0..instrs.len()).rev().collect();
        let mut queued = vec![true; instrs.len()];
        while let Some(pc) = pending.pop_front() {
            queued[pc] = false;
            for exception in [false, true] {
                if proven[pc][exception as usize] {
                    continue;
                }
                let mut next_exception = Some(exception);
                let terminal = match &instrs[pc] {
                    Instr::Exit(..) => Some(true),
                    Instr::End | Instr::Arbitrary => Some(normal_return || exception),
                    Instr::Call(_, _, callee, _, _) if terminal_calls.contains(callee) => Some(true),
                    Instr::Call(_, _, callee, _, _) if terminating_calls.get(callee) == Some(&false) => Some(false),
                    Instr::Call(..) => {
                        // 未知调用可能设置或清除异常，两种后继都必须终止。
                        next_exception = None;
                        None
                    }
                    Instr::Copy(loc, exp, _) if loc.id() == have_exception => {
                        next_exception = if let Exp::Bool(value) = exp { Some(*value) } else { None };
                        None
                    }
                    Instr::Init(name, _, exp, _) if *name == have_exception => {
                        next_exception = if let Exp::Bool(value) = exp { Some(*value) } else { None };
                        None
                    }
                    Instr::Decl(name, ..) | Instr::Monomorphize(name, ..) if *name == have_exception => {
                        next_exception = None;
                        None
                    }
                    Instr::PrimopUnary(loc, ..)
                    | Instr::PrimopBinary(loc, ..)
                    | Instr::PrimopVariadic(loc, ..)
                    | Instr::PrimopReset(loc, ..)
                        if loc.id() == have_exception =>
                    {
                        next_exception = None;
                        None
                    }
                    // 间接赋值可能覆盖异常状态，不能保留先前的证明。
                    Instr::Copy(Loc::Addr(_), ..)
                    | Instr::PrimopUnary(Loc::Addr(_), ..)
                    | Instr::PrimopBinary(Loc::Addr(_), ..)
                    | Instr::PrimopVariadic(Loc::Addr(_), ..)
                    | Instr::PrimopReset(Loc::Addr(_), ..) => {
                        next_exception = None;
                        None
                    }
                    _ => None,
                };
                let succeeds = terminal.unwrap_or_else(|| {
                    let condition = match &instrs[pc] {
                        Instr::Jump(Exp::Bool(value), ..) => Some(*value),
                        Instr::Jump(exp, ..) => {
                            exception_polarity(exp, have_exception)
                                .map(|positive| if positive { exception } else { !exception })
                        }
                        _ => None,
                    };
                    self.successors(pc).all(|(target, kind)| {
                        if matches!(kind, EdgeKind::Jump(polarity) if condition.is_some_and(|value| value != polarity))
                        {
                            return true;
                        }
                        match target {
                            RegionPoint::Instruction(next) => next_exception
                                .map_or(proven[next] == [true, true], |value| proven[next][value as usize]),
                            // 除已单独处理的 End/Arbitrary 外，虚拟出口来自断言失败等终止。
                            RegionPoint::FunctionExit => {
                                matches!(kind, EdgeKind::AssertionFailure | EdgeKind::Terminate)
                            }
                        }
                    })
                });
                if succeeds {
                    proven[pc][exception as usize] = true;
                    for predecessor in self.graph.neighbors_directed(self.pcs[pc], Direction::Incoming) {
                        let RegionPoint::Instruction(previous) = self.graph[predecessor] else {
                            panic!("虚拟出口不能有出边")
                        };
                        if !queued[previous] {
                            queued[previous] = true;
                            pending.push_back(previous);
                        }
                    }
                }
            }
        }
        proven[0] == [true, true]
    }

    /// 从函数入口可达的真实指令；终止调用后的指令不会进入传递效应上界。
    pub fn reachable_instructions(&self) -> BTreeSet<usize> {
        let mut reachable = BTreeSet::new();
        let mut pending = vec![RegionPoint::Instruction(0)];
        while let Some(RegionPoint::Instruction(pc)) = pending.pop() {
            if pc < self.pcs.len() && reachable.insert(pc) {
                pending.extend(self.successors(pc).filter_map(|(point, _)| match point {
                    RegionPoint::Instruction(_) => Some(point),
                    RegionPoint::FunctionExit => None,
                }));
            }
        }
        reachable
    }

    pub fn immediate_postdominator(&self, pc: usize) -> Result<RegionPoint, RegionRejection> {
        self.postdominators.immediate_dominator(self.pcs[pc]).map(|ix| self.graph[ix]).ok_or(RegionRejection::NoJoin)
    }

    /// 校验候选节点集的所有出边与无环性，可用于审计外部提供的区域边界。
    /// 自动求得的可达闭包天然对后继闭合；手工边界则可能返回 ExitsRegion。
    /// pc 越界或把入口/join 放入节点集属于调用者违反不变量，直接 panic。
    pub fn validate_region(
        &self,
        branch_pc: usize,
        join: RegionPoint,
        nodes: &BTreeSet<usize>,
    ) -> Result<(), RegionRejection> {
        assert!(branch_pc < self.pcs.len(), "区域入口 pc 越界");
        if !self.jump_pcs.contains(&branch_pc) {
            return Err(RegionRejection::NotJump);
        }
        assert!(!nodes.contains(&branch_pc), "区域不包含入口 Jump");
        if let RegionPoint::Instruction(pc) = join {
            assert!(pc < self.pcs.len() && pc != branch_pc && !nodes.contains(&pc), "join 必须在区域外");
        }
        for pc in nodes.iter().copied().chain([branch_pc]) {
            for (to, _) in self.successors(pc) {
                if to == join {
                    continue;
                }
                if let RegionPoint::Instruction(target) = to {
                    if target == branch_pc || nodes.contains(&target) {
                        continue;
                    }
                }
                return Err(RegionRejection::ExitsRegion { from: pc, to });
            }
        }
        // 显式栈的三色 DFS：灰色节点恰是当前路径的祖先。
        // 把入口也纳入子图，捕获自环、不可约环及返回入口的边。
        let mut colors: HashMap<usize, u8> = nodes.iter().copied().chain([branch_pc]).map(|pc| (pc, 0)).collect();
        for root in nodes.iter().copied().chain([branch_pc]) {
            if colors[&root] != 0 {
                continue;
            }
            let mut pending = vec![(root, false)];
            while let Some((pc, finished)) = pending.pop() {
                if finished {
                    *colors.get_mut(&pc).unwrap() = 2;
                    continue;
                }
                match colors[&pc] {
                    1 => return Err(RegionRejection::HasBackEdge),
                    2 => continue,
                    0 => (),
                    _ => unreachable!(),
                }
                *colors.get_mut(&pc).unwrap() = 1;
                pending.push((pc, true));
                for (to, _) in self.successors(pc) {
                    if to == join {
                        continue;
                    }
                    let RegionPoint::Instruction(target) = to else { unreachable!() };
                    pending.push((target, false));
                }
            }
        }
        Ok(())
    }
}

struct FunctionAnalysis {
    cfg: RegionCfg,
    full_cfg: RegionCfg,
    future_reads: Vec<HashSet<Name>>,
    address_taken: HashSet<Name>,
}

/// 调用者持有的函数缓存。借用不可变指令序列，避免函数改写后复用陈旧结果。
/// CFG、后支配树及活跃性在首次查询时计算；每个 Jump 的结果（含拒绝）单独缓存。
pub struct FunctionRegions<B> {
    // 拥有函数指令副本，使 SharedState 的并发缓存不引入生命周期不变性。
    instrs: Arc<[Instr<Name, B>]>,
    have_exception: Option<Name>,
    terminal_calls: Vec<Name>,
    analysis: OnceLock<FunctionAnalysis>,
    regions: HashMap<usize, Result<Arc<Region>, RegionRejection>>,
}

impl<B: BV> FunctionRegions<B> {
    pub fn new(instrs: &[Instr<Name, B>], have_exception: Name) -> Self {
        Self::with_options(instrs, RegionOptions { have_exception: Some(have_exception), terminal_calls: &[] })
    }

    pub fn with_options(instrs: &[Instr<Name, B>], options: RegionOptions<'_>) -> Self {
        Self {
            instrs: Arc::from(instrs),
            have_exception: options.have_exception,
            terminal_calls: options.terminal_calls.to_vec(),
            analysis: OnceLock::new(),
            regions: HashMap::new(),
        }
    }

    pub fn is_initialized(&self) -> bool {
        self.analysis.get().is_some()
    }
    pub fn cached_regions(&self) -> usize {
        self.regions.len()
    }
    pub fn cfg(&self) -> &RegionCfg {
        &self.analysis().cfg
    }

    fn analysis(&self) -> &FunctionAnalysis {
        self.analysis.get_or_init(|| {
            let cfg = RegionCfg::new(
                &self.instrs,
                RegionOptions { have_exception: self.have_exception, terminal_calls: &self.terminal_calls },
            );
            // 活跃性保留异常边；异常路径和绕行中的读也不能被误判为已死亡。
            let full_cfg = RegionCfg::new(
                &self.instrs,
                RegionOptions { have_exception: None, terminal_calls: &self.terminal_calls },
            );
            let mut reads = vec![HashSet::new(); self.instrs.len() + 1];
            let mut address_taken = HashSet::new();
            for (pc, instr) in self.instrs.iter().enumerate() {
                let mut expressions = Vec::new();
                let mut destination = None;
                match instr {
                    Instr::Decl(..) => (),
                    Instr::Init(_, _, exp, _) | Instr::Jump(exp, _, _) => expressions.push(exp),
                    Instr::Copy(loc, exp, _) | Instr::PrimopUnary(loc, _, exp, _) => {
                        destination = Some(loc);
                        expressions.push(exp);
                    }
                    Instr::Call(loc, _, _, args, _) | Instr::PrimopVariadic(loc, _, args, _) => {
                        destination = Some(loc);
                        expressions.extend(args);
                    }
                    Instr::PrimopBinary(loc, _, lhs, rhs, _) => {
                        destination = Some(loc);
                        expressions.extend([lhs, rhs]);
                    }
                    Instr::PrimopReset(loc, _, _, _) => destination = Some(loc),
                    Instr::Monomorphize(name, _, _) => {
                        reads[pc].insert(*name);
                    }
                    Instr::End => {
                        reads[pc].insert(RETURN);
                    }
                    Instr::Goto(_) | Instr::Exit(..) | Instr::Arbitrary => (),
                }
                if let Some(loc) = destination {
                    if matches!(loc, Loc::Field(..) | Loc::Addr(_)) {
                        reads[pc].insert(loc.id());
                    }
                }
                for exp in expressions {
                    exp.collect_ids(&mut reads[pc]);
                    // collect_ids 正确排除类型名/字段名，但不枚举 Ref。
                    // 只要地址可能逃逸，就保留整个函数中对应的局部名字。
                    let mut pending = vec![exp];
                    while let Some(exp) = pending.pop() {
                        match exp {
                            Exp::Ref(name) => {
                                address_taken.insert(*name);
                                reads[pc].insert(*name);
                            }
                            Exp::Kind(_, exp) | Exp::Unwrap(_, exp) | Exp::Field(exp, _) => pending.push(exp),
                            Exp::Call(_, args) => pending.extend(args),
                            Exp::Struct(_, fields) => pending.extend(fields.iter().map(|(_, exp)| exp)),
                            Exp::Id(_)
                            | Exp::Bool(_)
                            | Exp::Bits(_)
                            | Exp::String(_)
                            | Exp::Unit
                            | Exp::I64(_)
                            | Exp::I128(_)
                            | Exp::Undefined(_) => (),
                        }
                    }
                }
            }
            // 名字级保守活跃性：live_in = reads ∪ ⋃ live_in(successor)。
            // 不用赋值杀死名字，因为合并处删除的是局部槽位，而非某次定义的值。
            // 工作队列向前驱传播至不动点，覆盖绕行、重定义和任意回边。
            let mut queue: VecDeque<_> = full_cfg.graph.node_indices().collect();
            let mut queued = vec![true; reads.len()];
            while let Some(ix) = queue.pop_front() {
                queued[ix.index()] = false;
                for predecessor in full_cfg.graph.neighbors_directed(ix, Direction::Incoming) {
                    let (source, target) = (ix.index(), predecessor.index());
                    if source == target {
                        continue;
                    }
                    let additions: Vec<_> = reads[source].difference(&reads[target]).copied().collect();
                    if !additions.is_empty() {
                        reads[target].extend(additions);
                        if !queued[target] {
                            queued[target] = true;
                            queue.push_back(predecessor);
                        }
                    }
                }
            }
            FunctionAnalysis { cfg, full_cfg, future_reads: reads, address_taken }
        })
    }

    /// 对指定 Jump 求区域。pc 越界属于接口误用并 panic；非 Jump 等静态拒绝
    /// 用结构化错误返回。只识别结构，不判断该 Jump 在运行时是否为符号值。
    /// 返回共享句柄，持有外层区域时仍可查询内层；不复制节点集和活跃性集合。
    pub fn region(&mut self, branch_pc: usize) -> Result<Arc<Region>, RegionRejection> {
        assert!(branch_pc < self.instrs.len(), "区域入口 pc 越界");
        if !self.regions.contains_key(&branch_pc) {
            let result = self.compute_region(branch_pc).map(Arc::new);
            self.regions.insert(branch_pc, result);
        }
        self.regions[&branch_pc].clone()
    }

    fn compute_region(&self, branch_pc: usize) -> Result<Region, RegionRejection> {
        let analysis = self.analysis();
        let cfg = &analysis.cfg;
        if !cfg.jump_pcs.contains(&branch_pc) {
            return Err(RegionRejection::NotJump);
        }
        if cfg.exception_pcs.contains(&branch_pc) {
            return Err(RegionRejection::ExceptionCheck);
        }
        let join = cfg.immediate_postdominator(branch_pc)?;
        let mut nodes = BTreeSet::new();
        let mut pending: Vec<_> = cfg.successors(branch_pc).map(|(point, _)| point).collect();
        while let Some(point) = pending.pop() {
            if point == join {
                continue;
            }
            let RegionPoint::Instruction(pc) = point else { panic!("虚拟出口不能越过后支配点") };
            if cfg.postdominators.dominators(cfg.pcs[pc]).is_none() {
                return Err(RegionRejection::NoJoin);
            }
            if nodes.insert(pc) {
                pending.extend(cfg.successors(pc).map(|(point, _)| point));
            }
        }
        // 返回入口的路径由边界校验连同入口一起做 DFS 检查。
        nodes.remove(&branch_pc);
        cfg.validate_region(branch_pc, join, &nodes)?;
        let mut live_after = HashSet::new();
        let mut boundary = vec![match join {
            RegionPoint::Instruction(pc) => analysis.full_cfg.pcs[pc],
            RegionPoint::FunctionExit => analysis.full_cfg.exit,
        }];
        // 正常 join 之外，保守纳入被剔除异常边离开区域后的全部读取。
        for pc in nodes.iter().copied().chain([branch_pc]) {
            for (point, _) in analysis.full_cfg.successors(pc) {
                match point {
                    RegionPoint::Instruction(target) if !nodes.contains(&target) && target != branch_pc => {
                        boundary.push(analysis.full_cfg.pcs[target])
                    }
                    RegionPoint::FunctionExit => boundary.push(analysis.full_cfg.exit),
                    _ => (),
                }
            }
        }
        for ix in boundary {
            live_after.extend(analysis.future_reads[ix.index()].iter().copied());
        }
        let local_variables = analysis
            .full_cfg
            .declarations
            .iter()
            .filter_map(|(name, pcs)| {
                (*name != RETURN
                    && pcs.is_subset(&nodes)
                    && !analysis.address_taken.contains(name)
                    && !live_after.contains(name))
                .then_some(*name)
            })
            .collect();
        Ok(Region {
            branch_pc,
            join,
            nodes,
            kind: if join == RegionPoint::FunctionExit { RegionKind::FunctionReturn } else { RegionKind::Reconvergent },
            local_variables,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;
    use crate::ir::{Def, ExitCause, Symtab, Ty, HAVE_EXCEPTION, RETURN, SAIL_ASSERT};
    use crate::source_loc::SourceLoc;

    fn name(id: u32) -> Name {
        Name::from_u32(id + 100)
    }
    fn jump(pc: usize) -> Instr<Name, B64> {
        Instr::Jump(Exp::Id(name(0)), pc, SourceLoc::unknown())
    }
    fn copy(id: Name, exp: Exp<Name>) -> Instr<Name, B64> {
        Instr::Copy(Loc::Id(id), exp, SourceLoc::unknown())
    }
    fn decl(id: Name) -> Instr<Name, B64> {
        Instr::Decl(id, Ty::Bool, SourceLoc::unknown())
    }
    fn options() -> RegionOptions<'static> {
        RegionOptions { have_exception: Some(HAVE_EXCEPTION), terminal_calls: &[] }
    }

    #[test]
    fn regions_keep_outer_handle_while_querying_inner() {
        let body = vec![
            jump(4),
            jump(3),
            copy(name(1), Exp::Bool(false)),
            Instr::Goto(5),
            copy(name(1), Exp::Bool(true)),
            Instr::End,
        ];
        let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
        let outer = regions.region(0).unwrap();
        let inner = regions.region(1).unwrap();
        assert!(outer.nodes.contains(&inner.branch_pc));
        assert_eq!(outer.join, RegionPoint::Instruction(5));
        assert_eq!(inner.join, RegionPoint::Instruction(3));
        assert!(std::sync::Arc::ptr_eq(&outer, &regions.region(0).unwrap()));
    }

    #[test]
    fn regions_init_only_locals_and_outside_same_name() {
        let init = |id| Instr::Init(id, Ty::Bool, Exp::Bool(true), SourceLoc::unknown());
        let body = vec![jump(3), init(name(1)), Instr::Goto(4), init(name(2)), Instr::End];
        assert_eq!(
            FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables,
            [name(1), name(2)].into_iter().collect()
        );
        let body = vec![jump(3), init(name(1)), Instr::Goto(4), init(name(2)), init(name(1)), Instr::End];
        assert_eq!(
            FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables,
            [name(2)].into_iter().collect()
        );
    }

    #[test]
    fn regions_diamond_triangle_and_lazy_cache() {
        let body =
            vec![jump(3), copy(name(1), Exp::Bool(false)), Instr::Goto(4), copy(name(1), Exp::Bool(true)), Instr::End];
        let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
        assert!(!regions.is_initialized());
        assert_eq!(regions.cached_regions(), 0);
        let region = regions.region(0).unwrap();
        assert_eq!(region.join, RegionPoint::Instruction(4));
        assert_eq!(region.nodes, [1, 2, 3].into_iter().collect());
        assert_eq!(region.kind, RegionKind::Reconvergent);
        let address = Arc::as_ptr(&region);
        assert_eq!(Arc::as_ptr(&regions.region(0).unwrap()), address);
        assert_eq!(regions.cached_regions(), 1);
        let triangle = vec![jump(2), copy(name(1), Exp::Bool(true)), Instr::End];
        assert_eq!(FunctionRegions::new(&triangle, HAVE_EXCEPTION).region(0).unwrap().nodes, [1].into_iter().collect());
    }

    #[test]
    fn regions_four_term_or_chain_and_shared_join() {
        let body = vec![
            jump(11),
            jump(8),
            jump(5),
            copy(name(1), Exp::Bool(false)),
            Instr::Goto(6),
            copy(name(1), Exp::Bool(true)),
            copy(name(2), Exp::Id(name(1))),
            Instr::Goto(9),
            copy(name(2), Exp::Bool(true)),
            copy(name(3), Exp::Id(name(2))),
            Instr::Goto(12),
            copy(name(3), Exp::Bool(true)),
            Instr::End,
        ];
        let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
        for (pc, join) in [(0, 12), (1, 9), (2, 6)] {
            assert_eq!(regions.region(pc).unwrap().join, RegionPoint::Instruction(join));
        }
        let shared = vec![
            jump(4),
            jump(4),
            copy(name(1), Exp::Bool(false)),
            Instr::Goto(5),
            copy(name(1), Exp::Bool(true)),
            Instr::End,
        ];
        let mut regions = FunctionRegions::new(&shared, HAVE_EXCEPTION);
        for pc in [0, 1] {
            assert_eq!(regions.region(pc).unwrap().join, RegionPoint::Instruction(5));
        }
    }

    #[test]
    fn regions_cycles_use_graph_not_pc_order() {
        // 数值向后的边 4→1 没有构成环。
        let acyclic =
            vec![jump(4), copy(name(1), Exp::Bool(true)), Instr::Goto(5), Instr::Arbitrary, Instr::Goto(1), Instr::End];
        assert!(FunctionRegions::new(&acyclic, HAVE_EXCEPTION).region(0).is_ok());
        for body in [
            vec![jump(3), jump(3), Instr::Goto(1), Instr::End],
            vec![jump(3), Instr::Goto(0), Instr::Arbitrary, Instr::End],
        ] {
            assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0), Err(RegionRejection::HasBackEdge));
        }
        let no_exit = vec![jump(0), Instr::Goto(0)];
        assert_eq!(FunctionRegions::new(&no_exit, HAVE_EXCEPTION).region(0), Err(RegionRejection::NoJoin));
    }

    #[test]
    fn regions_exception_edges_follow_polarity_after_pure_call() {
        let exception = name(8);
        for negated in [false, true] {
            let condition = if negated { Exp::Id(exception).bool_not() } else { Exp::Id(exception) };
            let target = if negated { 6 } else { 8 };
            let body = vec![
                jump(3),
                copy(name(1), Exp::Bool(false)),
                Instr::Goto(7),
                Instr::Call(Loc::Id(name(1)), false, name(9), vec![], SourceLoc::unknown()),
                Instr::Jump(condition, target, SourceLoc::unknown()),
                if negated { Instr::Arbitrary } else { copy(name(1), Exp::Bool(true)) },
                if negated { copy(name(1), Exp::Bool(true)) } else { Instr::Goto(7) },
                Instr::End,
                Instr::Arbitrary,
            ];
            let mut regions = FunctionRegions::new(&body, exception);
            assert_eq!(regions.region(0).unwrap().join, RegionPoint::Instruction(7));
            assert_eq!(
                regions.cfg().successors(4).collect::<Vec<_>>(),
                vec![(
                    RegionPoint::Instruction(if negated { 6 } else { 5 }),
                    if negated { EdgeKind::Jump(true) } else { EdgeKind::Jump(false) }
                )]
            );
            let mut unfiltered =
                FunctionRegions::with_options(&body, RegionOptions { have_exception: None, terminal_calls: &[] });
            assert_eq!(unfiltered.region(0).unwrap().join, RegionPoint::FunctionExit);
        }
    }

    #[test]
    fn regions_all_terminal_forms_and_return_goto() {
        let info = SourceLoc::unknown();
        for terminal in [
            Instr::Arbitrary,
            Instr::Exit(ExitCause::Explicit, info),
            Instr::Exit(ExitCause::MatchFailure, info),
            Instr::Exit(ExitCause::AssertionFailure, info),
            Instr::Call(Loc::Id(name(2)), false, name(9), vec![], info),
            Instr::Call(Loc::Id(name(2)), false, SAIL_ASSERT, vec![Exp::Bool(false), Exp::String("失败".into())], info),
        ] {
            let body = vec![jump(3), terminal, Instr::Goto(4), copy(RETURN, Exp::Bool(true)), Instr::End];
            let mut regions = FunctionRegions::with_options(
                &body,
                RegionOptions { have_exception: Some(HAVE_EXCEPTION), terminal_calls: &[name(9)] },
            );
            let region = regions.region(0).unwrap();
            assert_eq!(region.join, RegionPoint::FunctionExit);
            assert_eq!(region.kind, RegionKind::FunctionReturn);
            assert!(!region.nodes.contains(&2));
        }
        let body = vec![
            jump(3),
            copy(RETURN, Exp::Bool(false)),
            Instr::Goto(5),
            copy(RETURN, Exp::Bool(true)),
            Instr::Goto(5),
            Instr::End,
        ];
        assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().join, RegionPoint::Instruction(5));
        let body = vec![jump(3), copy(RETURN, Exp::Bool(false)), Instr::End, copy(RETURN, Exp::Bool(true)), Instr::End];
        assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().join, RegionPoint::FunctionExit);
    }

    #[test]
    fn regions_non_returning_call_has_only_virtual_exit_and_keeps_full_liveness() {
        let info = SourceLoc::unknown();
        let callee = name(9);
        let body = vec![
            jump(3),
            copy(RETURN, Exp::Bool(false)),
            Instr::Goto(6),
            Instr::Call(Loc::Id(RETURN), false, callee, vec![], info),
            copy(name(1), Exp::Bool(true)),
            Instr::Goto(6),
            Instr::End,
        ];
        let mut regions = FunctionRegions::with_options(
            &body,
            RegionOptions { have_exception: Some(HAVE_EXCEPTION), terminal_calls: &[callee] },
        );
        let region = regions.region(0).unwrap();
        assert_eq!(region.join, RegionPoint::FunctionExit);
        assert!(region.nodes.contains(&3));
        assert!(!region.nodes.contains(&4));
        assert!(!region.nodes.contains(&5));
        assert_eq!(
            regions.cfg().successors(3).collect::<Vec<_>>(),
            vec![(RegionPoint::FunctionExit, EdgeKind::Terminate)]
        );
    }

    #[test]
    fn regions_boundary_validation_reports_exit() {
        let body =
            vec![jump(3), copy(name(1), Exp::Bool(false)), Instr::Goto(4), copy(name(1), Exp::Bool(true)), Instr::End];
        let graph = RegionCfg::new(&body, options());
        assert!(matches!(
            graph.validate_region(0, RegionPoint::Instruction(4), &[1, 3].into_iter().collect()),
            Err(RegionRejection::ExitsRegion { from: 1, to: RegionPoint::Instruction(2) })
        ));
    }

    #[test]
    fn regions_local_liveness_bypasses_redefinitions_and_sub_locations() {
        let local = name(1);
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(4),
            decl(name(2)),
            jump(7),
            copy(local, Exp::Bool(false)),
            Instr::Goto(8),
            copy(name(3), Exp::Id(local)),
            Instr::End,
        ];
        let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
        assert_eq!(regions.region(0).unwrap().local_variables, [name(2)].into_iter().collect());
        for loc in [Loc::Field(Box::new(Loc::Id(local)), name(9)), Loc::Addr(Box::new(Loc::Id(local)))] {
            let body = vec![
                jump(3),
                decl(local),
                Instr::Goto(4),
                decl(name(2)),
                Instr::Copy(loc, Exp::Bool(true), SourceLoc::unknown()),
                Instr::End,
            ];
            assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        }
        // 重定义不杀死名字的活跃性，避免在后面的读取之前误删槽位。
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(4),
            decl(name(2)),
            copy(local, Exp::Bool(false)),
            copy(name(3), Exp::Id(local)),
            Instr::End,
        ];
        assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        let body = vec![jump(3), decl(local), Instr::Goto(4), decl(name(2)), Instr::End];
        assert_eq!(
            FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables,
            [local, name(2)].into_iter().collect()
        );
    }

    #[test]
    fn regions_liveness_tracks_later_loops_exception_reads_and_addresses() {
        let local = name(1);
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(4),
            decl(name(2)),
            jump(7),
            copy(name(3), Exp::Id(local)),
            Instr::Goto(4),
            Instr::End,
        ];
        assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(6),
            decl(name(2)),
            Instr::Jump(Exp::Id(HAVE_EXCEPTION), 7, SourceLoc::unknown()),
            Instr::Goto(6),
            Instr::End,
            copy(name(3), Exp::Id(local)),
            Instr::Arbitrary,
        ];
        assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        let body =
            vec![jump(4), decl(local), copy(name(3), Exp::Ref(local)), Instr::Goto(5), decl(name(2)), Instr::End];
        assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
    }

    #[test]
    fn regions_assertion_failure_edge_and_empty_trailing_ir() {
        let body = vec![
            jump(3),
            copy(name(1), Exp::Bool(true)),
            Instr::Goto(4),
            Instr::Call(
                Loc::Id(name(2)),
                false,
                SAIL_ASSERT,
                vec![Exp::Id(name(3)), Exp::String("失败".into())],
                SourceLoc::unknown(),
            ),
            Instr::End,
        ];
        assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().join, RegionPoint::FunctionExit);
        let empty: Vec<Instr<Name, B64>> = vec![];
        assert_eq!(RegionCfg::new(&empty, options()).instruction_count(), 0);
        let trailing = vec![jump(2), decl(name(1)), copy(name(2), Exp::Bool(true))];
        assert_eq!(
            FunctionRegions::new(&trailing, HAVE_EXCEPTION).region(0).unwrap().join,
            RegionPoint::Instruction(2)
        );
    }

    #[test]
    #[should_panic(expected = "跳转目标超出函数")]
    fn regions_invalid_target_panics() {
        RegionCfg::new(&[jump(9)], options());
    }

    #[test]
    fn regions_parallel_polarity_edges_and_cached_rejections() {
        let body = vec![jump(1), Instr::End];
        let graph = RegionCfg::new(&body, options());
        let edges: Vec<_> = graph.successors(0).collect();
        assert_eq!(edges.len(), 2);
        assert!(edges.contains(&(RegionPoint::Instruction(1), EdgeKind::Jump(true))));
        assert!(edges.contains(&(RegionPoint::Instruction(1), EdgeKind::Jump(false))));
        for condition in [Exp::Id(HAVE_EXCEPTION), Exp::Id(HAVE_EXCEPTION).bool_not()] {
            let body: Vec<Instr<Name, B64>> = vec![Instr::Jump(condition, 1, SourceLoc::unknown()), Instr::End];
            let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
            assert_eq!(regions.cfg().successors(0).count(), 1);
            for pc in [0, 0, 1, 1] {
                assert_eq!(
                    regions.region(pc),
                    Err(if pc == 0 { RegionRejection::ExceptionCheck } else { RegionRejection::NotJump })
                );
            }
            assert_eq!(regions.cached_regions(), 2);
        }
    }

    #[test]
    fn regions_nonreturning_arm_and_irreducible_loop_are_rejected() {
        let body = vec![jump(2), Instr::Goto(1), Instr::End];
        assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0), Err(RegionRejection::NoJoin));
        // 1、3 是同一 SCC 的两个入口，不能只检查单一循环头。
        let body = vec![jump(3), jump(4), Instr::Goto(3), jump(1), Instr::End];
        assert_eq!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0), Err(RegionRejection::HasBackEdge));
    }

    #[test]
    fn regions_primop_assertions_and_reset_preserve_control_flow() {
        let info = SourceLoc::unknown();
        let primops = primop::binary_primops::<B64>();
        for assertion in [primops["optimistic_assert"], primops["pessimistic_assert"]] {
            for condition in [Exp::Bool(false), Exp::Bool(true), Exp::Id(name(3))] {
                let successful = matches!(condition, Exp::Bool(true));
                let body = vec![
                    jump(3),
                    copy(name(1), Exp::Bool(true)),
                    Instr::Goto(4),
                    Instr::PrimopBinary(Loc::Id(name(2)), assertion, condition, Exp::String("失败".into()), info),
                    Instr::End,
                ];
                assert_eq!(
                    FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().join,
                    if successful { RegionPoint::Instruction(4) } else { RegionPoint::FunctionExit }
                );
            }
        }
        let local = name(1);
        let reset: super::super::Reset<B64> = std::sync::Arc::new(|memory, typedefs, solver| {
            let _ = (memory, typedefs, solver);
            panic!("纯分析不允许执行 reset")
        });
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(4),
            decl(name(2)),
            Instr::PrimopReset(Loc::Addr(Box::new(Loc::Id(local))), reset.clone(), primop::reset_effect(&reset), info),
            Instr::End,
        ];
        let mut regions = FunctionRegions::new(&body, HAVE_EXCEPTION);
        assert_eq!(regions.region(0).unwrap().join, RegionPoint::Instruction(4));
        assert!(!regions.region(0).unwrap().local_variables.contains(&local));
    }

    #[test]
    fn regions_variable_enumeration_uses_values_not_field_or_type_names() {
        let info = SourceLoc::unknown();
        let local = name(1);
        let expressions = [
            Exp::Id(local),
            Exp::Field(Box::new(Exp::Id(local)), name(9)),
            Exp::Struct(name(8), vec![(name(9), Exp::Id(local))]),
            Exp::Kind(name(8), Box::new(Exp::Id(local))),
            Exp::Unwrap(name(8), Box::new(Exp::Id(local))),
            Exp::Id(local).bool_not(),
        ];
        for exp in expressions {
            let body = vec![jump(3), decl(local), Instr::Goto(4), decl(name(2)), copy(name(3), exp), Instr::End];
            assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        }
        let body = vec![
            jump(3),
            decl(local),
            Instr::Goto(4),
            decl(name(2)),
            copy(name(3), Exp::Struct(local, vec![(local, Exp::Bool(true))])),
            Instr::End,
        ];
        assert!(FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        for reader in [
            Instr::Monomorphize(local, super::super::Ty::Bool, info),
            Instr::Init(name(3), super::super::Ty::Bool, Exp::Id(local), info),
            Instr::Call(Loc::Id(name(3)), false, name(9), vec![Exp::Id(local)], info),
            Instr::PrimopUnary(Loc::Id(name(3)), primop::unary_primops::<B64>()["not"], Exp::Id(local), info),
            Instr::PrimopVariadic(
                Loc::Id(name(3)),
                primop::variadic_primops::<B64>()["vector_update"],
                vec![Exp::Id(local)],
                info,
            ),
        ] {
            let body = vec![jump(3), decl(local), Instr::Goto(4), decl(name(2)), reader, Instr::End];
            assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(0).unwrap().local_variables.contains(&local));
        }
        // 同名声明出现在区域外时，不能删除该名字。
        let body = vec![decl(local), jump(4), decl(local), Instr::Goto(5), decl(name(2)), Instr::End];
        assert!(!FunctionRegions::new(&body, HAVE_EXCEPTION).region(1).unwrap().local_variables.contains(&local));
    }

    /// 运行：ISLA_REGIONS_IR=/绝对路径/rv64d.ir cargo test -p isla-lib regions_real_ir --offline --features smt-thread-interrupt -- --ignored --nocapture
    #[test]
    #[ignore = "需要外部 rv64d.ir；用 ISLA_REGIONS_IR 指定路径"]
    fn regions_real_ir() {
        let path = std::env::var("ISLA_REGIONS_IR").expect("必须设置 ISLA_REGIONS_IR");
        let text = std::fs::read_to_string(path).unwrap();
        let mut symtab = Symtab::new();
        // 只解析目标函数，使用正式词法器/语法器，避免整份架构的加载成本。
        for (function, expected_len, joins) in [
            ("zpte_is_invalid", 141, vec![(9, 138), (32, 135), (54, 132), (43, 52), (82, 129), (99, 108)]),
            ("zupdate_PTE_Bits", 101, vec![(20, 52), (63, 69), (77, 100)]),
        ] {
            let start = text.find(&format!("fn {}(", function)).unwrap();
            let end = start + text[start..].find("\n}").unwrap() + 2;
            let definition: Def<Name, B64> = crate::ir_parser::DefParser::new()
                .parse(&mut symtab, crate::ir_lexer::new_ir_lexer(&text[start..end]))
                .unwrap();
            let Def::Fn(_, _, body) = definition else { panic!("目标必须是函数") };
            assert_eq!(body.len(), expected_len);
            let exception = symtab.lookup("have_exception");
            let mut filtered = FunctionRegions::new(&body, exception);
            let mut original =
                FunctionRegions::with_options(&body, RegionOptions { have_exception: None, terminal_calls: &[] });
            for (pc, join) in joins {
                assert_eq!(filtered.region(pc).unwrap().join, RegionPoint::Instruction(join), "{} pc {}", function, pc);
                if function == "zpte_is_invalid" {
                    assert_eq!(original.region(pc).unwrap().join, RegionPoint::FunctionExit, "原图 pc {}", pc);
                }
            }
        }
    }
}
