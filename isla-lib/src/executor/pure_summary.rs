//! 显式启用的小型摘要原型；不接入普通执行器，也不自动发布正常域约束。
//! 调用者须报告两次调用间的写集。缓存还核对入口寄存器值，拒绝 relaxed 状态。
use super::*;
use crate::ir::pure::{analyze_from, AssertionCondition, PureFunction};
use std::collections::BTreeSet;

type Formula = smtlib::Exp<Sym>;

pub struct SummaryInstance<B> {
    /// 当前只支持类型／形状事实，故 A=true；不从第一次调用点借用前提。
    pub input_domain: Formula,
    pub domain: Formula,
    pub returns: Vec<(Formula, Val<B>)>,
    pub dead_arms: Vec<Formula>,
    pub reads: Vec<GuardedRegisterRead<B>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    Scalar(smtlib::Ty),
    Unit,
    Vector(Vec<Shape>),
    Struct(Vec<(Name, Shape)>),
    Ctor(Name, Box<Shape>),
}

fn shape<B: BV>(value: &Val<B>, ty: &Ty<Name>, shared: &SharedState<B>, solver: &Solver<B>) -> Result<Shape, String> {
    let scalar = match ty {
        Ty::Bool => Some(smtlib::Ty::Bool),
        Ty::I64 => Some(smtlib::Ty::BitVec(64)),
        Ty::I128 => Some(smtlib::Ty::BitVec(128)),
        Ty::Bits(n) => Some(smtlib::Ty::BitVec(*n)),
        Ty::AnyBits => match value {
            Val::Bits(b) => Some(smtlib::Ty::BitVec(b.len())),
            Val::Symbolic(s) => solver.scalar_sort(*s).filter(|t| matches!(t, smtlib::Ty::BitVec(_))),
            _ => None,
        },
        Ty::Enum(n) => Some(smtlib::Ty::Enum(EnumId::from_name(*n))),
        _ => None,
    };
    if let Some(expected) = scalar {
        value.plausible(ty, shared)?;
        let actual = match value {
            Val::Symbolic(s) => solver.scalar_sort(*s),
            Val::Bool(_) => Some(smtlib::Ty::Bool),
            Val::I64(_) => Some(smtlib::Ty::BitVec(64)),
            Val::I128(_) => Some(smtlib::Ty::BitVec(128)),
            Val::Bits(b) => Some(smtlib::Ty::BitVec(b.len())),
            Val::Enum(e) => Some(smtlib::Ty::Enum(e.enum_id)),
            _ => None,
        };
        if actual.as_ref() == Some(&expected) {
            return Ok(Shape::Scalar(expected));
        }
        return Err("摘要标量类型不一致".into());
    }
    match (value, ty) {
        (Val::Unit, Ty::Unit) => Ok(Shape::Unit),
        (Val::Vector(values), Ty::Vector(t) | Ty::FixedVector(_, t)) => {
            if matches!(ty, Ty::FixedVector(n, _) if *n as usize != values.len()) {
                return Err("固定向量长度不一致".into());
            }
            Ok(Shape::Vector(values.iter().map(|v| shape(v, t, shared, solver)).collect::<Result<_, _>>()?))
        }
        (Val::Struct(values), Ty::Struct(n)) => {
            let fields = &shared.type_info.structs[n];
            if fields.len() != values.len() {
                return Err("结构字段不一致".into());
            }
            Ok(Shape::Struct(
                fields
                    .iter()
                    .map(|(n, t)| Ok((*n, shape(values.get(n).ok_or("缺少结构字段")?, t, shared, solver)?)))
                    .collect::<Result<_, String>>()?,
            ))
        }
        (Val::Ctor(n, value), Ty::Union(union)) => {
            let (_, ty) =
                shared.type_info.unions[union].iter().find(|(ctor, _)| ctor == n).ok_or("构造子不属于参数类型")?;
            Ok(Shape::Ctor(*n, Box::new(shape(value, ty, shared, solver)?)))
        }
        _ => Err("原型未支持此值形状（含引用、动态构造子、列表或混合位向量）".into()),
    }
}

fn fresh<B: BV>(shape: &Shape, shared: &SharedState<B>, solver: &mut Solver<B>, formals: &mut Vec<Sym>) -> Val<B> {
    match shape {
        Shape::Scalar(ty) => {
            if let smtlib::Ty::Enum(e) = ty {
                solver.get_enum(e.to_name(), shared.type_info.enums[&e.to_name()].len());
            }
            let symbol = solver.declare_const(ty.clone(), SourceLoc::unknown());
            formals.push(symbol);
            Val::Symbolic(symbol)
        }
        Shape::Unit => Val::Unit,
        Shape::Vector(values) => Val::Vector(values.iter().map(|s| fresh(s, shared, solver, formals)).collect()),
        Shape::Struct(fields) => {
            Val::Struct(fields.iter().map(|(n, s)| (*n, fresh(s, shared, solver, formals))).collect())
        }
        Shape::Ctor(n, payload) => Val::Ctor(*n, Box::new(fresh(payload, shared, solver, formals))),
    }
}
fn leaves<B: BV>(shape: &Shape, value: &Val<B>, out: &mut Vec<Formula>) {
    match (shape, value) {
        (Shape::Scalar(_), value) => out.push(smt_value(value, SourceLoc::unknown()).expect("已核对标量类型")),
        (Shape::Unit, Val::Unit) => (),
        (Shape::Vector(shapes), Val::Vector(values)) => {
            for (s, v) in shapes.iter().zip(values) {
                leaves(s, v, out);
            }
        }
        (Shape::Struct(fields), Val::Struct(values)) => {
            for (n, s) in fields {
                leaves(s, &values[n], out);
            }
        }
        (Shape::Ctor(_, s), Val::Ctor(_, v)) => leaves(s, v, out),
        _ => panic!("已核对形状却不能绑定摘要形参"),
    }
}
fn substitute(exp: &Formula, names: &HashMap<Sym, Formula>) -> Formula {
    // 模板拒绝 DeclareFun，因而没有 map_var 不会重命名的 App 名字。
    exp.map_var(&mut |n| Ok::<_, ()>(names.get(n).expect("摘要使用了未定义符号").clone())).unwrap()
}
fn value_substitute<B: BV>(
    value: &Val<B>,
    names: &HashMap<Sym, Formula>,
    solver: &mut Solver<B>,
) -> Result<Val<B>, String> {
    Ok(match value {
        Val::Symbolic(n) => match names.get(n).expect("返回／读取符号必须已定义") {
            smtlib::Exp::Var(n) => Val::Symbolic(*n),
            exp => Val::Symbolic(solver.define_const(exp.clone(), SourceLoc::unknown())),
        },
        Val::Vector(v) => Val::Vector(v.iter().map(|v| value_substitute(v, names, solver)).collect::<Result<_, _>>()?),
        Val::Struct(fields) => Val::Struct(
            fields.iter().map(|(n, v)| Ok((*n, value_substitute(v, names, solver)?))).collect::<Result<_, String>>()?,
        ),
        Val::Ctor(n, v) => Val::Ctor(*n, Box::new(value_substitute(v, names, solver)?)),
        Val::Unit | Val::Bool(_) | Val::Bits(_) | Val::I64(_) | Val::I128(_) | Val::Enum(_) => value.clone(),
        _ => return Err("原型未支持此返回／读取形状".into()),
    })
}

struct TemplatePath<B> {
    events: Vec<Event<B>>,
    returned: Option<Val<B>>,
}
struct Template<B> {
    function: Name,
    shapes: Vec<Shape>,
    register_shapes: Vec<(Name, Shape)>,
    register_inputs: Vec<Val<B>>,
    formals: Vec<Sym>,
    paths: Vec<TemplatePath<B>>,
    analysis: PureFunction,
}

fn build<'ir, B: BV>(
    shared: &SharedState<'ir, B>,
    lets: &Bindings<'ir, B>,
    function: Name,
    shapes: Vec<Shape>,
    register_shapes: Vec<(Name, Shape)>,
    analysis: PureFunction,
) -> Result<Template<B>, String> {
    // 此接口刻意不接收父 Solver、实际数值或实际寄存器符号。
    for name in &analysis.lets {
        match &lets[name] {
            UVal::Init(v) if v.symbolic_variables().is_empty() => (),
            _ => return Err("原型要求不可变 let 为具体值".into()),
        }
    }
    let context = Context::new(Config::new());
    let mut solver = Solver::new(&context);
    let mut formals = Vec::new();
    let args: Vec<_> = shapes.iter().map(|s| fresh(s, shared, &mut solver, &mut formals)).collect();
    let mut registers = RegisterBindings::new();
    for (name, shape) in &register_shapes {
        registers.insert(*name, false, UVal::Init(fresh(shape, shared, &mut solver, &mut formals)));
    }
    let (params, ret, body) = &shared.functions[&function];
    let mut frame = LocalFrame::new(function, params, ret, Some(&args), body);
    frame.add_regs(&registers).add_lets(lets);
    let state = TaskState::new().with_execution_limits(ExecutionLimits::default().with_max_path_depth(4096));
    let output = Mutex::new(Ok(Vec::new()));
    super::start_single_with_timeout(
        frame.task_with_checkpoint(TaskId::fresh(), &state, checkpoint(&mut solver)),
        PathTimeout::from_seconds(Some(30)),
        shared,
        &output,
        &|_, _, result, _, mut solver, output| {
            let mut output = output.lock().unwrap();
            let Ok(paths) = output.as_mut() else { return };
            let returned = match result {
                Ok((Run::Finished(v), _)) => Some(v),
                Err((ExecError::AssertionFailure(_, location), _))
                    if analysis.assertions.iter().any(|((f, pc), c)| {
                        *c == AssertionCondition::Concrete(false)
                            && stats::instr_source_loc(&shared.functions[f].2[*pc]) == Some(location)
                    }) =>
                {
                    None
                }
                Ok((Run::Dead, _)) if matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat) => return,
                Err((error, _)) => {
                    *output = Err(format!("摘要构造拒绝: {:?}", error));
                    return;
                }
                _ => {
                    *output = Err("摘要构造出现未支持的终止".into());
                    return;
                }
            };
            match solver.check_sat(SourceLoc::unknown()) {
                SmtResult::Unsat => return,
                SmtResult::Sat => (),
                result => {
                    *output = Err(format!("摘要构造求解未知: {:?}", result));
                    return;
                }
            }
            let events: Vec<_> = solver.trace().to_vec().into_iter().rev().cloned().collect();
            if events.iter().any(|e| {
                matches!(
                    e,
                    Event::Smt(smtlib::Def::DeclareFun(..), _, _)
                        | Event::WriteReg(..)
                        | Event::ReadMem { .. }
                        | Event::WriteMem { .. }
                ) || matches!(e, Event::Smt(smtlib::Def::DeclareConst(n,_),_,_) if !formals.contains(n))
            }) {
                *output = Err("模板含不透明函数、外效或非形参自由符号".into());
                return;
            }
            paths.push(TemplatePath { events, returned });
        },
    );
    let paths = output.into_inner().unwrap()?;
    if paths.is_empty() {
        return Err("摘要没有已确认的终止路径".into());
    }
    Ok(Template { function, shapes, register_shapes, register_inputs: Vec::new(), formals, paths, analysis })
}

fn instantiate<B: BV>(
    template: &Template<B>,
    actuals: Vec<Formula>,
    solver: &mut Solver<B>,
) -> Result<SummaryInstance<B>, String> {
    assert_eq!(template.formals.len(), actuals.len());
    let bindings: HashMap<_, _> = template.formals.iter().copied().zip(actuals).collect();
    let mut result = SummaryInstance {
        input_domain: smtlib::Exp::Bool(true),
        domain: smtlib::Exp::Bool(false),
        returns: vec![],
        dead_arms: vec![],
        reads: vec![],
    };
    for path in &template.paths {
        let mut names = bindings.clone();
        let mut guard = smtlib::Exp::Bool(true);
        // 每条路径按原定义顺序导入；路径内辅助符号不会与另一次调用共用。
        for event in &path.events {
            match event {
                Event::Smt(smtlib::Def::DefineEnum(n, size), _, _) => {
                    solver.get_enum(*n, *size);
                }
                Event::Smt(smtlib::Def::DeclareConst(n, _), _, _) if bindings.contains_key(n) => (),
                Event::Smt(smtlib::Def::DefineConst(n, exp), attrs, loc) => {
                    let fresh =
                        solver.with_def_attrs(*attrs, |solver| solver.define_const(substitute(exp, &names), *loc));
                    names.insert(*n, smtlib::Exp::Var(fresh));
                }
                Event::Smt(smtlib::Def::Assert(exp), _, _) => {
                    guard = smtlib::Exp::And(Box::new(guard), Box::new(substitute(exp, &names)));
                }
                Event::Smt(..) => panic!("构造时应已拒绝不支持的 SMT 声明"),
                Event::ReadReg(register, accessor, value) => {
                    result.reads.push(GuardedRegisterRead {
                        register: *register,
                        accessor: accessor.clone(),
                        value: value_substitute(value, &names, solver)?,
                        guard: guard.clone(),
                    });
                }
                _ => (),
            }
        }
        if let Some(value) = &path.returned {
            let value = value_substitute(value, &names, solver)?;
            result.domain = smtlib::Exp::Or(Box::new(result.domain), Box::new(guard.clone()));
            result.returns.push((guard, value));
        } else {
            result.dead_arms.push(guard);
        }
    }
    Ok(result)
}

/// 局部单条目缓存。未连接正式执行帧的写入通知，不能用于生产调用跳过。
pub struct Prototype<'state, 'ir, B> {
    shared: &'state SharedState<'ir, B>,
    lets: &'state Bindings<'ir, B>,
    enabled: bool,
    template: Option<Template<B>>,
    pub builds: usize,
    pub hits: usize,
}
impl<'state, 'ir, B: BV> Prototype<'state, 'ir, B> {
    pub fn new(shared: &'state SharedState<'ir, B>, lets: &'state Bindings<'ir, B>) -> Self {
        Self { shared, lets, enabled: false, template: None, builds: 0, hits: 0 }
    }
    pub fn set_enabled(&mut self, enabled: bool) {
        self.enabled = enabled;
        if !enabled {
            self.template = None;
        }
    }
    /// writes 是上次调用以来全部写入的集合，包括写回原值；不得只比较当前值。
    pub fn call(
        &mut self,
        function: Name,
        args: &[Val<B>],
        registers: &RegisterBindings<'ir, B>,
        solver: &mut Solver<B>,
        writes: &BTreeSet<Name>,
    ) -> Result<Option<SummaryInstance<B>>, String> {
        if !self.enabled {
            return Ok(None);
        }
        if self.template.as_ref().map_or(false, |t| !t.analysis.registers.is_disjoint(writes)) {
            self.template = None;
        }
        let (params, _, _) = &self.shared.functions[&function];
        if args.len() != params.len() {
            return Err("摘要参数个数错误".into());
        }
        let shapes: Vec<_> =
            args.iter().zip(params).map(|(v, (_, t))| shape(v, t, self.shared, solver)).collect::<Result<_, _>>()?;
        let relaxed: HashSet<_> = self
            .shared
            .registers
            .keys()
            .copied()
            .filter(|n| registers.contains_key(*n) && registers.is_relaxed(*n))
            .collect();
        let analysis = match &self.template {
            Some(t) if t.function == function => t.analysis.clone(),
            _ => analyze_from(self.shared, self.lets, &relaxed, &BTreeSet::from([function])).remove(&function).unwrap(),
        };
        if !analysis.accepted() {
            return Err(format!("纯函数准入拒绝: {:?}", analysis.rejections));
        }
        if !analysis.registers.is_disjoint(&relaxed.iter().copied().collect()) {
            return Err("relaxed 寄存器不能缓存".into());
        }
        let mut register_shapes = Vec::new();
        let mut values = Vec::new();
        for n in &analysis.registers {
            let value = registers.get_last_if_initialized(*n).ok_or("原型要求入口寄存器已初始化")?.clone();
            register_shapes.push((*n, shape(&value, &self.shared.registers[n], self.shared, solver)?));
            values.push(value);
        }
        let hit = self.template.as_ref().map_or(false, |t| {
            t.function == function
                && t.shapes == shapes
                && t.register_shapes == register_shapes
                && t.register_inputs == values
        });
        if hit {
            self.hits += 1
        } else {
            self.template = None;
            let mut t = build(self.shared, self.lets, function, shapes, register_shapes, analysis)?;
            t.register_inputs = values.clone();
            self.template = Some(t);
            self.builds += 1;
        }
        let template = self.template.as_ref().unwrap();
        let mut actuals = Vec::new();
        for (s, v) in template.shapes.iter().zip(args) {
            leaves(s, v, &mut actuals)
        }
        for ((_, s), v) in template.register_shapes.iter().zip(&values) {
            leaves(s, v, &mut actuals)
        }
        instantiate(template, actuals, solver).map(Some)
    }
}
#[cfg(test)]
mod tests;
