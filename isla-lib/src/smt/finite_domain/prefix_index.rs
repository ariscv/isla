use super::*;
use std::cell::OnceCell;

pub(in crate::smt) const BUFFERED: usize = usize::MAX;

// 已发布的段号在建检查点后保持不变；缓冲区使用单独的段号。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Position(usize, usize);

#[derive(Default)]
pub(in crate::smt) struct PrefixIndex {
    symbols: ahash::AHashMap<Sym, Position>,
    rebindings: usize,
    assertions: Vec<Position>,
    bool_symbols: Vec<(Position, Sym)>,
    pub(super) branch: RefCell<Option<BranchCandidates>>,
}

pub(super) struct BranchCandidates {
    pub(super) predicate: Exp<Sym>,
    pub(super) subjects: Vec<Option<Vec<Candidate>>>,
}

pub(super) struct Candidate {
    pub(super) value: Exp<Sym>,
    pub(super) excluded: Option<bool>,
}

fn binding<B>(event: &Event<B>) -> Option<(Sym, bool)> {
    match event {
        Event::Smt(Def::DeclareConst(sym, ty), ..) => Some((*sym, matches!(ty, Ty::Bool))),
        Event::Smt(Def::DefineConst(sym, _) | Def::DeclareFun(sym, ..), ..) => Some((*sym, false)),
        _ => None,
    }
}

impl PrefixIndex {
    pub(in crate::smt) fn push<B>(&mut self, segment: usize, offset: usize, event: &Event<B>) {
        #[cfg(test)]
        PREFIX_EVENT_VISITS.set(PREFIX_EVENT_VISITS.get() + 1);
        let position = Position(segment, offset);
        if let Some((sym, boolean)) = binding(event) {
            if let std::collections::hash_map::Entry::Vacant(entry) = self.symbols.entry(sym) {
                entry.insert(position);
            } else {
                self.rebindings += 1;
            }
            if boolean {
                self.bool_symbols.push((position, sym));
            }
        } else if matches!(event, Event::Smt(Def::Assert(_), ..)) {
            self.assertions.push(position);
        } else {
            return;
        }
        self.invalidate_candidates();
    }

    pub(in crate::smt) fn remove_suffix<B>(&mut self, segment: usize, events: &[Event<B>], start: usize) {
        let first = Position(segment, start);
        self.assertions.truncate(self.assertions.partition_point(|position| *position < first));
        self.bool_symbols.truncate(self.bool_symbols.partition_point(|(position, _)| *position < first));
        for (index, event) in events.iter().enumerate().skip(start).rev() {
            if let Some((sym, _)) = binding(event) {
                let first = self.symbols[&sym];
                if first == Position(segment, index) {
                    self.symbols.remove(&sym);
                } else {
                    self.rebindings -= 1;
                }
            }
        }
        if start < events.len() {
            self.invalidate_candidates();
        }
    }

    pub(in crate::smt) fn invalidate_candidates(&mut self) {
        *self.branch.get_mut() = None;
    }

    pub(in crate::smt) fn heap_bytes(&self) -> usize {
        use crate::executor::stats::memory_stats::{exp_heap_bytes, map_bytes};
        use std::mem::size_of;

        map_bytes::<Sym, Position>(self.symbols.capacity())
            + self.assertions.capacity() * size_of::<Position>()
            + self.bool_symbols.capacity() * size_of::<(Position, Sym)>()
            + self.branch.borrow().as_ref().map_or(0, |branch| {
                exp_heap_bytes(&branch.predicate)
                    + branch.subjects.capacity() * size_of::<Option<Vec<Candidate>>>()
                    + branch
                        .subjects
                        .iter()
                        .flatten()
                        .map(|candidates| {
                            candidates.capacity() * size_of::<Candidate>()
                                + candidates.iter().map(|candidate| exp_heap_bytes(&candidate.value)).sum::<usize>()
                        })
                        .sum::<usize>()
            })
    }
}

pub(super) struct PathConditions<'a, B> {
    pub(super) index: &'a PrefixIndex,
    trace: &'a Trace<B>,
    buffered: &'a [Event<B>],
    guards: &'a [Exp<Sym>],
    published: OnceCell<Vec<&'a [Event<B>]>>,
}

impl<'a, B: BV> PathConditions<'a, B> {
    pub(super) fn new(solver: &'a Solver<'_, B>) -> Option<Self> {
        let index = solver.finite_prefix.as_ref()?;
        // 已发布断言保留发布时的绑定，不能用重绑后的符号表解释。
        (index.rebindings == 0).then(|| Self {
            index,
            trace: &solver.trace,
            buffered: &solver.transaction_events,
            guards: &solver.transaction_conditions,
            published: OnceCell::new(),
        })
    }

    fn event(&self, position: Position) -> &'a Event<B> {
        let Position(segment, offset) = position;
        let events: &[Event<B>] = if segment == BUFFERED {
            self.buffered
        } else if segment == self.trace.checkpoints {
            self.trace.head.as_slice()
        } else {
            self.published.get_or_init(|| {
                let mut segments: Vec<_> =
                    std::iter::successors(self.trace.tail.as_ref().as_ref(), |trace| trace.tail.as_ref().as_ref())
                        .map(|trace| trace.head.as_slice())
                        .collect();
                segments.reverse();
                segments
            })[segment]
        };
        &events[offset]
    }

    pub(super) fn definition(&self, sym: Sym) -> Option<&'a Exp<Sym>> {
        match self.event(*self.index.symbols.get(&sym)?) {
            Event::Smt(Def::DefineConst(_, exp), ..) => Some(exp),
            _ => None,
        }
    }

    pub(super) fn assertions(&self) -> impl Iterator<Item = &'a Exp<Sym>> + '_ {
        self.index
            .assertions
            .iter()
            .rev()
            .map(|position| match self.event(*position) {
                Event::Smt(Def::Assert(exp), ..) => exp,
                _ => unreachable!("断言索引必须指向断言"),
            })
            .chain(self.guards)
    }

    pub(super) fn bool_symbols(&self) -> impl Iterator<Item = Sym> + '_ {
        self.index.bool_symbols.iter().rev().map(|(_, sym)| *sym)
    }
}
