use super::*;

/// 要检查的联合值在槽内的位置。索引访问没有可直接证明的匹配语法。
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SlotProjection {
    Field(Name),
    Ctor(Name),
    Element(usize),
}

fn projection(exp: &Exp<Name>, name: Name) -> Option<Vec<SlotProjection>> {
    match exp {
        Exp::Id(id) if *id == name => Some(Vec::new()),
        Exp::Field(exp, field) => {
            let mut path = projection(exp, name)?;
            path.push(SlotProjection::Field(*field));
            Some(path)
        }
        Exp::Unwrap(ctor, exp) => {
            let mut path = projection(exp, name)?;
            path.push(SlotProjection::Ctor(*ctor));
            Some(path)
        }
        _ => None,
    }
}

fn reads_unguarded(
    exp: &Exp<Name>,
    name: Name,
    checked_payload: Option<(&[SlotProjection], Name)>,
    tag_matches: bool,
) -> bool {
    let (operand, tag_only) = match exp {
        Exp::Kind(_, operand) => (operand.as_ref(), true),
        _ => (exp, false),
    };
    if let Some(path) = projection(operand, name) {
        let Some((union_path, ctor)) = checked_payload else { return true };
        if let Some(suffix) = path.strip_prefix(union_path) {
            // 直接读取联合值可能让载荷逃逸。读取其标签或其它构造子的载荷是独立操作。
            return match suffix.first() {
                None => !tag_only,
                Some(SlotProjection::Ctor(read_ctor)) => *read_ctor == ctor && !tag_matches,
                Some(_) => true,
            };
        }
        return union_path.starts_with(&path) && !tag_only;
    }
    match exp {
        Exp::Kind(_, exp) | Exp::Unwrap(_, exp) | Exp::Field(exp, _) => {
            reads_unguarded(exp, name, checked_payload, tag_matches)
        }
        Exp::Call(_, args) => args.iter().any(|exp| reads_unguarded(exp, name, checked_payload, tag_matches)),
        Exp::Struct(_, fields) => {
            fields.iter().any(|(_, exp)| reads_unguarded(exp, name, checked_payload, tag_matches))
        }
        _ => false,
    }
}

impl<B: BV> FunctionRegions<B> {
    /// 沿完整 CFG 检查槽位的旧内容。只在肯定完整覆盖时停止，并保留异常边和回边。
    /// 有指定载荷时，只有对应 Kind 的匹配边可证明读该载荷安全。
    pub(crate) fn slot_reads_guarded(
        &self,
        join: RegionPoint,
        name: Name,
        checked_payload: Option<(&[SlotProjection], Name)>,
    ) -> bool {
        let analysis = self.analysis();
        // 返回值可逃逸到调用者，取地址的槽位也不能在函数内穷尽使用。
        if name == RETURN || analysis.address_taken.contains(&name) {
            return false;
        }
        let mut pending = vec![(join, false)];
        let mut visited = HashSet::new();
        while let Some((point, tag_matches)) = pending.pop() {
            let RegionPoint::Instruction(pc) = point else { continue };
            if !analysis.future_reads[analysis.full_cfg.pcs[pc].index()].contains(&name)
                || !visited.insert((pc, tag_matches))
            {
                continue;
            }
            let instr = &self.instrs[pc];
            let (expressions, destination, implicit_read) = instruction_operands(instr);
            if implicit_read == Some(name)
                || destination.is_some_and(|loc| !matches!(loc, Loc::Id(_)) && loc.id() == name)
                || expressions.into_iter().any(|exp| reads_unguarded(exp, name, checked_payload, tag_matches))
            {
                return false;
            }
            if matches!(instr, Instr::Decl(id, ..) | Instr::Init(id, ..) if *id == name)
                || matches!(instr, Instr::Copy(Loc::Id(id), ..) if *id == name)
            {
                continue;
            }
            // 其它写入可能伴随异常或调用，不用作覆盖证明。
            if destination.is_some_and(|loc| loc.id() == name) {
                return false;
            }
            let checks_tag = match (checked_payload, instr) {
                (Some((path, ctor)), Instr::Jump(Exp::Kind(tested, operand), ..)) => {
                    *tested == ctor && projection(operand, name).as_deref() == Some(path)
                }
                _ => false,
            };
            pending.extend(analysis.full_cfg.successors(pc).map(|(successor, edge)| {
                (successor, if checks_tag { edge == EdgeKind::Jump(false) } else { tag_matches })
            }));
        }
        true
    }
}
