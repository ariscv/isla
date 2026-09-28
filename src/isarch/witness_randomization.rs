//! solve witness 随机化的 isarch 侧胶水。
//!
//! 机制本体在 `isla_lib::smt::witness`（SMT 封装层：按 sort 采样、全部假设一次
//! `check-sat-assuming` 注入、UNSAT 二分丢弃重试、仍不 SAT 回退 plain 模型）。
//! 本层只做四件事：合并 CLI `--witness-randomization`（`<seed>` 固定 seed、无值
//! 自动 seed）与 TOML 顶层键 `witness_randomization`（整数/true），CLI 优先；从
//! wrapper 初始状态（pre-state 寄存器表）收集全部符号常量交给封装层；把记录里
//! 的符号显示名重映射为寄存器名。本层不感知任何维度名、取值域或分布——域知识
//! 全部留在路径自身的合法性约束（constrain_pre_state）里。
//!
//! 自动 seed 复用 `isla_lib::smt::fresh_random_seed`（与 Z3 相位 seed 同一时间源
//! 抽象），生成时在 stderr 打印一行，并随后写入输出元数据的 seed 字段。

use super::target::PreStateCtx;
use isla_lib::bitvector::BV;
use isla_lib::config::WitnessRandomizationSetting;
use isla_lib::error::ExecError;
use isla_lib::ir::{BitsSegment, Symtab, Val};
use isla_lib::smt::witness::WitnessRandomization;
use isla_lib::smt::{Solver, Sym};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;
use std::collections::{BTreeMap, HashMap};

/// CLI 的 `--witness-randomization <seed>` 配置：只有总开关 seed，无维度语法。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessRandomizationConfig {
    pub seed: u64,
}

/// 解析 `--witness-randomization` 参数：单个 u64 seed。
pub fn parse_witness_randomization(spec: &str) -> Result<WitnessRandomizationConfig, String> {
    let spec = spec.trim();
    if spec.is_empty() {
        return Err("--witness-randomization 不能为空，格式 <seed>".to_string());
    }
    let seed = spec.parse::<u64>().map_err(|_| format!("--witness-randomization 的 seed 不是 u64：{spec}"))?;
    Ok(WitnessRandomizationConfig { seed })
}

/// `--witness-randomization` 无值形态重写后的占位值：进入 getopts 前把裸 token 改写
/// 成 `--witness-randomization=auto`（getopts 原生支持 `=` 取值）。
pub const AUTO_SEED_SPEC: &str = "auto";

/// `--witness-randomization` 的 CLI 长名。
const WITNESS_RANDOMIZATION_FLAG: &str = "--witness-randomization";

/// 把无值的裸 `--witness-randomization` 重写为 `=auto` 形式。
///
/// getopts 的 optopt 要求选项后紧跟取值（空格形式 `--witness-randomization 42` 保持
/// 原语义不变），裸 token 会直接解析失败；这里在进入 getopts 前把"其后不是取值"
/// （末尾或下一个 token 以 `-` 开头）的裸 token 重写为 `=auto`。因此无值形态之后
/// 必须跟选项或位于参数末尾，紧跟的非 `-` 开头 token 仍按固定 seed 解析。
pub fn rewrite_bare_witness_randomization(args: Vec<String>) -> Vec<String> {
    let mut rewritten = args;
    for index in 0..rewritten.len() {
        if rewritten[index] == WITNESS_RANDOMIZATION_FLAG
            && rewritten.get(index + 1).is_none_or(|next| next.starts_with('-'))
        {
            rewritten[index] = format!("{WITNESS_RANDOMIZATION_FLAG}={AUTO_SEED_SPEC}");
        }
    }
    rewritten
}

/// 取自动 seed：复用 smt 层相位 seed 的同一时间源抽象，打印一行到 stderr 便于追溯。
fn auto_seed() -> u64 {
    let seed = u64::from(isla_lib::smt::fresh_random_seed());
    eprintln!("witness-randomization: 本次自动 seed = {seed}（已写入输出元数据的 seed 字段）");
    seed
}

/// CLI 与 TOML 配置合并为最终 seed：CLI（含 `=auto` 无值形态）> TOML > 关闭。
///
/// 返回 `Some(seed)` 表示启用；`None` 表示关闭（输出与默认行为逐键一致）。
pub fn resolve_witness_randomization_seed(
    cli: Option<&str>,
    config: Option<WitnessRandomizationSetting>,
) -> Result<Option<u64>, String> {
    if let Some(spec) = cli {
        if spec == AUTO_SEED_SPEC {
            return Ok(Some(auto_seed()));
        }
        return parse_witness_randomization(spec).map(|config| Some(config.seed));
    }
    match config {
        Some(WitnessRandomizationSetting::Seed(seed)) => Ok(Some(seed)),
        Some(WitnessRandomizationSetting::Enabled(true)) => Ok(Some(auto_seed())),
        // 显式 false 与不写键同义：关闭。
        Some(WitnessRandomizationSetting::Enabled(false)) | None => Ok(None),
    }
}

/// 首见符号登记进符号表与命名表；同一寄存器出现多个符号时追加 `.序号` 后缀。
fn record_symbol(
    display: &str,
    name_counts: &mut HashMap<String, usize>,
    symbols: &mut Vec<Sym>,
    names: &mut BTreeMap<String, String>,
    sym: Sym,
) {
    if symbols.contains(&sym) {
        return;
    }
    symbols.push(sym);
    let unique = match name_counts.get_mut(display) {
        Some(count) => {
            let suffixed = format!("{display}.{count}");
            *count += 1;
            suffixed
        }
        None => {
            name_counts.insert(display.to_string(), 1);
            display.to_string()
        }
    };
    names.insert(sym.to_string(), unique);
}

fn collect_symbolic<B: BV>(
    val: &Val<B>,
    display: &str,
    name_counts: &mut HashMap<String, usize>,
    symbols: &mut Vec<Sym>,
    names: &mut BTreeMap<String, String>,
) {
    match val {
        Val::Symbolic(sym) => record_symbol(display, name_counts, symbols, names, *sym),
        Val::Vector(values) | Val::List(values) => {
            for value in values {
                collect_symbolic(value, display, name_counts, symbols, names);
            }
        }
        // 结构字段按 Name 排序后递归：ahash 迭代序不确定，不排序会导致多符号
        // 寄存器的 `.序号` 后缀跨运行漂移，破坏同 seed 复跑的元数据一致性。
        Val::Struct(fields) => {
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_unstable_by_key(|(name, _)| name.as_u32());
            for (_, value) in fields {
                collect_symbolic(value, display, name_counts, symbols, names);
            }
        }
        Val::Ctor(_, inner) => collect_symbolic(inner, display, name_counts, symbols, names),
        Val::MixedBits(segments) => {
            for segment in segments {
                if let BitsSegment::Symbolic(sym) = segment {
                    record_symbol(display, name_counts, symbols, names, *sym);
                }
            }
        }
        Val::SymbolicCtor(sym, fields) => {
            record_symbol(display, name_counts, symbols, names, *sym);
            let mut fields: Vec<_> = fields.iter().collect();
            fields.sort_unstable_by_key(|(name, _)| name.as_u32());
            for (_, value) in fields {
                collect_symbolic(value, display, name_counts, symbols, names);
            }
        }
        _ => (),
    }
}

/// 从 pre-state 寄存器值中递归收集全部符号常量，并建立 sym 显示名 → 寄存器名映射。
///
/// 这些符号就是 wrapper 初始状态的 SMT 变量（setup_pre_state 声明），交给封装层
/// 按 sort 随机化；收集顺序不确定没有影响——封装层内部按 Sym id 排序去重。
pub(crate) fn collect_witness_symbols<B: BV>(
    pre_state: &PreStateCtx<B>,
    symtab: &Symtab,
) -> (Vec<Sym>, BTreeMap<String, String>) {
    let mut symbols = Vec::new();
    let mut names = BTreeMap::new();
    let mut name_counts: HashMap<String, usize> = HashMap::new();
    for (name, val) in pre_state.iter() {
        let display = zencode::decode(symtab.to_str(*name)).to_string();
        collect_symbolic(val, &display, &mut name_counts, &mut symbols, &mut names);
    }
    (symbols, names)
}

/// plain check SAT 后调用：收集 wrapper 初始状态符号交给封装层随机化，并把记录
/// 里的符号显示名重映射为寄存器名。
pub(crate) fn randomize_pre_state_witness<B: BV>(
    pre_state: &PreStateCtx<B>,
    symtab: &Symtab,
    solver: &mut Solver<'_, B>,
    seed: u64,
    path_signature: u64,
) -> Result<WitnessRandomization, ExecError> {
    let (symbols, names) = collect_witness_symbols(pre_state, symtab);
    let mut record = solver.randomize_witness(&symbols, seed, path_signature, SourceLoc::unknown())?;
    record.samples = record
        .samples
        .iter()
        .map(|(sym, value)| {
            let name = names.get(sym).unwrap_or_else(|| panic!("采样符号 {sym} 必须来自 pre-state 符号集")).clone();
            (name, value.clone())
        })
        .collect();
    Ok(record)
}

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::ir::Symtab;
    use isla_lib::smt::smtlib::Ty;
    use isla_lib::smt::{Config, Context, Model, ModelVal, SmtResult};
    use isla_lib::zencode;
    use std::collections::BTreeSet;

    #[test]
    fn parse_accepts_plain_seed_only() {
        assert_eq!(parse_witness_randomization("42").unwrap(), WitnessRandomizationConfig { seed: 42 });
        assert_eq!(parse_witness_randomization(" 7 ").unwrap(), WitnessRandomizationConfig { seed: 7 });
    }

    #[test]
    fn parse_rejects_dimension_syntax_and_malformed_specs() {
        // 旧的维度语法整体下线：上层不再感知维度。
        for spec in ["", "  ", "abc", "-1", "12:vl", "12:vl,vstart"] {
            assert!(parse_witness_randomization(spec).is_err(), "{spec:?} 必须被拒绝");
        }
    }

    #[test]
    fn rewrite_only_touches_bare_flag_without_value() {
        let rewrite = |args: &[&str]| {
            rewrite_bare_witness_randomization(args.iter().map(|arg| arg.to_string()).collect()).join(" ")
        };
        // 末尾裸 token 与其后跟选项的裸 token 都重写为 =auto。
        assert_eq!(rewrite(&["isarch", "--witness-randomization"]), "isarch --witness-randomization=auto");
        assert_eq!(
            rewrite(&["isarch", "--witness-randomization", "--tastic", "qfaufbv"]),
            "isarch --witness-randomization=auto --tastic qfaufbv"
        );
        // 空格取值与 = 取值形式原样保留：固定 seed 行为不变。
        assert_eq!(rewrite(&["isarch", "--witness-randomization", "42"]), "isarch --witness-randomization 42");
        assert_eq!(rewrite(&["isarch", "--witness-randomization=42"]), "isarch --witness-randomization=42");
        // 其它选项与自由参数不受影响。
        assert_eq!(rewrite(&["isarch", "-A", "rv64d.ir"]), "isarch -A rv64d.ir");
    }

    /// ① 无值 CLI（=auto 占位）→ 自动 seed；⑤ 无 CLI 无键 → 关闭；③ TOML 42 → 固定；
    /// ② TOML true → 自动；④ CLI 覆盖 TOML。
    #[test]
    fn resolve_merges_cli_and_toml_with_cli_priority() {
        // ⑤：双方都未给出 → 关闭。
        assert_eq!(resolve_witness_randomization_seed(None, None).unwrap(), None);
        assert_eq!(
            resolve_witness_randomization_seed(None, Some(WitnessRandomizationSetting::Enabled(false))).unwrap(),
            None,
            "TOML 显式 false 与缺省同义"
        );
        // ③：TOML 固定 seed。
        assert_eq!(
            resolve_witness_randomization_seed(None, Some(WitnessRandomizationSetting::Seed(42))).unwrap(),
            Some(42)
        );
        // ④：CLI 固定 seed 覆盖 TOML。
        assert_eq!(
            resolve_witness_randomization_seed(Some("7"), Some(WitnessRandomizationSetting::Seed(42))).unwrap(),
            Some(7)
        );
        // ④：CLI auto 覆盖 TOML 固定 seed（自动 seed 非零、写入元数据）。
        let cli_auto = resolve_witness_randomization_seed(Some("auto"), Some(WitnessRandomizationSetting::Seed(42)))
            .unwrap()
            .expect("CLI auto 必须启用");
        assert!(cli_auto > 0, "自动 seed 必须非零（fresh_random_seed 的 unwrap_or(1) 兜底）");
        // ②：TOML true → 自动 seed。
        let toml_auto = resolve_witness_randomization_seed(None, Some(WitnessRandomizationSetting::Enabled(true)))
            .unwrap()
            .expect("TOML true 必须启用");
        assert!(toml_auto > 0);
        // CLI 固定 seed 的非法值仍报错。
        assert!(resolve_witness_randomization_seed(Some("abc"), None).is_err());
    }

    /// ⑥：自动 seed 两次生成不同（同一进程内 retry 至值变化，纳秒时钟粒度）。
    #[test]
    fn auto_seed_changes_between_draws() {
        let first = isla_lib::smt::fresh_random_seed();
        let mut changed = false;
        for _ in 0..100_000 {
            if isla_lib::smt::fresh_random_seed() != first {
                changed = true;
                break;
            }
        }
        assert!(changed, "100_000 次内自动 seed 必然发生变化");
    }

    #[test]
    fn collect_witness_symbols_walks_register_values() {
        let mut symtab = Symtab::new();
        let names: Vec<String> = ["vl", "fcsr", "vr0"].iter().map(|name| zencode::encode(name)).collect();
        for name in &names {
            symtab.intern(name);
        }
        let mut pre_state = PreStateCtx::<B64>::new();
        pre_state.insert_from_str("vl", Val::Symbolic(Sym::from_u32(1)), &symtab);
        // Sail 可能用单字段结构包装寄存器值（与 constrain_pre_state 同法解包）。
        let mut wrapped = ahash::HashMap::with_capacity_and_hasher(1, ahash::RandomState::new());
        wrapped.insert(isla_lib::ir::Name::from_u32(9), Val::Symbolic(Sym::from_u32(2)));
        pre_state.insert_from_str("fcsr", Val::Struct(wrapped), &symtab);
        pre_state.insert_from_str(
            "vr0",
            Val::Vector(vec![Val::Symbolic(Sym::from_u32(3)), Val::Symbolic(Sym::from_u32(4))]),
            &symtab,
        );
        let (symbols, names) = collect_witness_symbols(&pre_state, &symtab);
        let mut sorted = symbols.clone();
        sorted.sort_by_key(|sym| sym.to_string());
        assert_eq!(sorted.len(), 4, "四个符号都必须收集到：{symbols:?}");
        assert_eq!(names[&Sym::from_u32(1).to_string()], "vl");
        assert_eq!(names[&Sym::from_u32(2).to_string()], "fcsr");
        assert_eq!(names[&Sym::from_u32(3).to_string()], "vr0", "同寄存器首个符号用寄存器名：{names:?}");
        assert_eq!(names[&Sym::from_u32(4).to_string()], "vr0.1", "同寄存器后续符号加序号后缀：{names:?}");
    }

    /// Context 与 Solver 存在借用关系，用闭包把二者限制在同一作用域内。
    fn with_pre_state_solver<R>(test: impl FnOnce(&mut Solver<'_, B64>, &PreStateCtx<B64>, &Symtab) -> R) -> R {
        isla_lib::smt::configure_tastic(isla_lib::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        let mut symtab = Symtab::new();
        let names: Vec<String> = ["vl", "vtype"].iter().map(|name| zencode::encode(name)).collect();
        for name in &names {
            symtab.intern(name);
        }
        let mut pre_state = PreStateCtx::<B64>::new();
        let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
        let vtype = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
        pre_state.insert_from_str("vl", Val::Symbolic(vl), &symtab);
        pre_state.insert_from_str("vtype", Val::Symbolic(vtype), &symtab);
        // 真实 IR 中 vl/vtype 受 constrain_pre_state 的合法域约束，但主用途是 UF
        // 参数——不直接出现在断言里的模型变量被 model completion 恒填 0，这是官方
        // solve witness 退化的根源（E4/E5 形态）。这里只声明不约束，忠实复现退化
        // 机制；注入的有效性（E6/E7）与 UNSAT 回退由 isla-lib 封装层单测覆盖。
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
        test(&mut solver, &pre_state, &symtab)
    }

    fn model_u64(solver: &mut Solver<'_, B64>, sym: Sym) -> u64 {
        let mut model = Model::new(&*solver);
        let value = match model.get_finite_domain_var(sym).unwrap().expect("模型必须有取值") {
            ModelVal::Arbitrary(_) => {
                model.set_complete_model(true);
                model.get_finite_domain_var(sym).unwrap().expect("completion 后必须有取值")
            }
            value => value,
        };
        match value {
            ModelVal::Exp(isla_lib::smt::smtlib::Exp::Bits64(bv)) => bv.lower_u64(),
            other => panic!("非位向量模型值 {other:?}"),
        }
    }

    /// G1（端口层）：开随机化后 vl 分布非退化，采样记录以寄存器名呈现。
    #[test]
    fn randomize_pre_state_witness_diversifies_vl_with_register_names() {
        with_pre_state_solver(|solver, pre_state, symtab| {
            let vl = match pre_state.get_from_str("vl", symtab) {
                Some(Val::Symbolic(sym)) => *sym,
                other => panic!("vl 必须是符号值：{other:?}"),
            };
            let mut seen = BTreeSet::new();
            for signature in 0..64u64 {
                let record = randomize_pre_state_witness(pre_state, symtab, solver, 0x5eed, signature).unwrap();
                assert!(record.accepted, "自由 vl/vtype 的联合注入不应回退：{record:?}");
                assert!(record.samples.contains_key("vl"), "采样记录必须用寄存器名：{record:?}");
                let value: u64 = record.samples["vl"].parse().expect("64 位内采样值记录为十进制");
                seen.insert(value);
                assert_eq!(model_u64(solver, vl), value, "模型必须携带注入值");
            }
            assert!(seen.len() >= 3, "vl 分布必须非退化，实际 {seen:?}");
        });
    }

    /// R1（端口层红场景）：不开随机化时 plain 模型对 vl 恒取退化值 0。
    #[test]
    fn plain_model_keeps_degenerate_zero_vl() {
        with_pre_state_solver(|solver, pre_state, symtab| {
            let vl = match pre_state.get_from_str("vl", symtab) {
                Some(Val::Symbolic(sym)) => *sym,
                other => panic!("vl 必须是符号值：{other:?}"),
            };
            for _ in 0..8 {
                assert_eq!(model_u64(solver, vl), 0, "不开随机化时 vl 必须恒为 0（退化模型）");
            }
        });
    }
}
