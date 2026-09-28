//! 求解 witness 的通用随机化机制（SMT 封装层）。
//!
//! 背景（见 agents/float_support_review/z3-random-model 的研究结论）：Z3 没有
//! 原生"随机满足赋值"；不出现在 case 身份约束里的符号（只进 UF 参数或完全自由）
//! 被 model completion 恒填 0，witness 系统性退化，而 assumption 注入实测完全
//! 可靠——随机性由调用方 seeded RNG 提供，Z3 负责"符合路径条件"的判定。
//!
//! [`Solver::randomize_witness`] 在 plain check SAT 之后调用：对调用方给出的
//! witness 输入符号按 sort 处理（位向量按位宽采样、浮点先采样随机位模式再按其
//! sort 以 `to_fp` 构造，其余 sort 跳过并计数），把全部 `(= sym value)` 组装成
//! 一次 `check_sat_with`（check-sat-assuming）注入；UNSAT 时按 RNG 序二分丢弃
//! 一半 assumptions 重试（总注入次数不超过 floor(log2 n)+1），仍不 SAT 则回退
//! plain 模型（重跑一次 plain check 恢复注入前的模型）。assumption 只作用于当次
//! check，不进入增量约束栈，不影响 case 的可满足性判定与后续物化。
//!
//! 随机性全部来自 `splitmix64(seed ^ path_signature)` 派生的计数器序列，无时间
//! 源；同 `(seed, path_signature)` 复跑逐位一致，多线程调度不影响结果。本层不
//! 感知任何符号的语义（维度名、取值域等），只按 sort 分派；上层负责挑选哪些符号
//! 属于 witness 初始状态。

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use z3_sys::*;

use crate::bitvector::b64::B64;
use crate::bitvector::BV;
use crate::error::ExecError;
use crate::source_loc::SourceLoc;

use super::smtlib::{self, Exp, FPUnary};
use super::{SmtResult, Solver, Sym};

/// SplitMix64 的单轮混合；同输入必得同输出，作为唯一随机源。
pub fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

/// 生成给定宽度位向量的一个确定性候选值。
///
/// 位宽超过 64 时仍是有限域，但不能只复用一个 64 位随机数；这里每 64 位独立混合一次，
/// 并保持 `Exp::Bits` 所要求的低位在前的位序。
pub fn bitvector_candidate(seed: u64, width: u32) -> Exp<Sym> {
    if width <= 64 {
        let value = if width == 64 { splitmix64(seed) } else { splitmix64(seed) & ((1u64 << width) - 1) };
        return Exp::Bits64(B64::new(value, width));
    }

    let mut bits = Vec::with_capacity(width as usize);
    for word_index in 0..((width + 63) / 64) {
        let word = splitmix64(seed.wrapping_add(word_index as u64));
        let word_width = (width - word_index * 64).min(64);
        for bit_index in 0..word_width {
            bits.push((word >> bit_index) & 1 == 1);
        }
    }
    Exp::Bits(bits)
}

/// 由 `(seed, path_signature)` 派生的确定性采样状态。
struct WitnessRng {
    base: u64,
    counter: u64,
}

impl WitnessRng {
    fn new(seed: u64, path_signature: u64) -> Self {
        WitnessRng { base: splitmix64(seed ^ path_signature), counter: 0 }
    }

    fn draw(&mut self) -> u64 {
        self.counter += 1;
        splitmix64(self.base ^ self.counter)
    }
}

/// 单个 witness 符号的一次采样：注入用取值表达式 + 元数据文本。
struct Sample {
    sym: Sym,
    exp: Exp<Sym>,
    text: String,
}

/// 一次 witness 随机化的结果记录，调用方可直接序列化进输出元数据。
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WitnessRandomization {
    pub seed: u64,
    pub accepted: bool,
    /// check-sat-assuming 返回 Unknown 时同样回退，单独计数以区分 UNSAT。
    pub unknown: bool,
    /// 因 UNSAT 而二分丢弃的轮数：0 表示首轮全量注入即 SAT。
    #[serde(rename = "bisection-rounds")]
    pub bisection_rounds: usize,
    /// 参与随机化（可按 sort 采样）的符号总数。
    pub attempted: usize,
    /// 最终随模型生效的 assumption 数；回退时为 0。
    pub injected: usize,
    /// 因 sort 不支持（枚举、数组、RoundingMode 等）而跳过的符号数。
    pub skipped: usize,
    /// 全部采样值（含被二分丢弃的；生效子集大小见 `injected`），键为符号显示名
    /// （`Sym` 的 Display，调用方可重映射为寄存器名）。
    pub samples: BTreeMap<String, String>,
}

/// 一次 solve run 的随机化汇总。
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SummaryWitnessRandomization {
    pub seed: u64,
    pub attempted: usize,
    pub accepted: usize,
    pub fallback: usize,
    pub unknown: usize,
}

impl SummaryWitnessRandomization {
    pub fn from_terminals(seed: u64, terminals: &[Option<WitnessRandomization>]) -> Option<Self> {
        let mut summary = SummaryWitnessRandomization { seed, attempted: 0, accepted: 0, fallback: 0, unknown: 0 };
        for record in terminals.into_iter().flatten() {
            summary.attempted += 1;
            if record.accepted {
                summary.accepted += 1;
            } else {
                summary.fallback += 1;
            }
            if record.unknown {
                summary.unknown += 1;
            }
        }
        (summary.attempted > 0).then_some(summary)
    }
}

/// 二分丢弃的调度：每轮保留的 assumption 数（含首轮全量），长度恰为
/// `floor(log2(total)) + 1`，即该机制的总注入次数上限。
fn bisection_schedule(total: usize) -> Vec<usize> {
    let mut schedule = vec![total];
    let mut live = total;
    while live > 1 {
        live /= 2;
        schedule.push(live);
    }
    schedule
}

fn width_mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1_u64 << width) - 1
    }
}

/// 64 位内位模式的 curated 混合分布：1/8 取 0、1/8 取 1、1/2 落在小值域
/// `[0, 64)`、1/4 全宽均匀。
///
/// witness 输入中的计数值/控制位集中在小值域；对受路径约束的符号做纯全宽均匀
/// 采样几乎必然 UNSAT（z3-random-model 实测），curated 类别 + 均匀混合是该研究
/// 给出的推荐形态。
fn sample_small_or_full(rng: &mut WitnessRng, width: u32) -> u64 {
    assert!(width > 0 && width <= 64, "sample_small_or_full 只处理 64 位内的位模式");
    let small_cap = if width >= 6 { 64 } else { 1_u64 << width };
    match rng.draw() % 8 {
        0 => 0,
        1 => 1,
        2..=5 => rng.draw() % small_cap,
        _ => rng.draw() & width_mask(width),
    }
}

/// 采样一个位向量符号；超过 64 位时元数据记录低 64 位十六进制。
fn sample_bitvector(rng: &mut WitnessRng, width: u32) -> (Exp<Sym>, String) {
    assert!(width > 0, "witness 符号的位宽为 0");
    if width <= 64 {
        let value = sample_small_or_full(rng, width);
        (smtlib::bits64(value, width), value.to_string())
    } else {
        let seed = rng.draw();
        if seed % 8 == 0 {
            (Exp::Bits(vec![false; width as usize]), "0x0".to_string())
        } else {
            (bitvector_candidate(seed, width), format!("{:#x}", splitmix64(seed)))
        }
    }
}

/// 采样一个浮点符号：先按 `ebits + sbits` 宽度采样随机位模式，再以 `to_fp`
/// 按其 sort 构造。位模式可能落入 NaN/Inf 等类别，均交给 Z3 判定可满足性。
fn sample_float(rng: &mut WitnessRng, ebits: u32, sbits: u32) -> (Exp<Sym>, String) {
    assert!(ebits > 1 && sbits > 2, "非法浮点 sort 宽度 e={ebits} s={sbits}");
    let width = ebits + sbits;
    if width <= 64 {
        let pattern = sample_small_or_full(rng, width);
        (smtlib::bits64(pattern, width), format!("{pattern:#x}"))
    } else {
        let seed = rng.draw();
        (bitvector_candidate(seed, width), format!("{:#x}", splitmix64(seed)))
    }
}

/// 一个符号在当前求解器中的可采样 sort；未声明的符号属于调用方违反契约。
enum WitnessSort {
    Bits(u32),
    Float(u32, u32),
    Other,
}

fn witness_sort<B>(solver: &Solver<'_, B>, sym: Sym) -> WitnessSort {
    let ast = solver.decls.get(&sym).unwrap_or_else(|| panic!("witness 随机化符号 {sym} 未在当前求解器声明"));
    unsafe {
        let ctx = solver.ctx.z3_ctx;
        let sort = Z3_get_sort(ctx, ast.z3_ast);
        match Z3_get_sort_kind(ctx, sort) {
            SortKind::BV => WitnessSort::Bits(Z3_get_bv_sort_size(ctx, sort)),
            SortKind::FloatingPoint => WitnessSort::Float(Z3_fpa_get_ebits(ctx, sort), Z3_fpa_get_sbits(ctx, sort)),
            _ => WitnessSort::Other,
        }
    }
}

impl<'ctx, B: BV> Solver<'ctx, B> {
    /// 对 witness 输入符号做通用随机化（见模块文档）。
    ///
    /// 必须在 plain check SAT 之后、读取模型之前调用；SAT 时当前模型携带采样值，
    /// UNSAT/Unknown 时内部已重跑 plain check 恢复注入前的模型。
    pub fn randomize_witness(
        &mut self,
        symbols: &[Sym],
        seed: u64,
        path_signature: u64,
        info: SourceLoc,
    ) -> Result<WitnessRandomization, ExecError> {
        // 规范序（按 Sym id 排序去重）：采样值的抽取顺序与调用方遍历序无关。
        let mut syms = symbols.to_vec();
        syms.sort_by_key(|sym| sym.id);
        syms.dedup_by_key(|sym| sym.id);

        let mut rng = WitnessRng::new(seed, path_signature);
        let mut samples: Vec<Sample> = Vec::new();
        let mut skipped = 0usize;
        for sym in syms {
            match witness_sort(self, sym) {
                WitnessSort::Bits(width) => {
                    let (exp, text) = sample_bitvector(&mut rng, width);
                    samples.push(Sample { sym, exp, text });
                }
                WitnessSort::Float(ebits, sbits) => {
                    let (pattern, text) = sample_float(&mut rng, ebits, sbits);
                    let exp = Exp::FPUnary(FPUnary::FromIEEE(ebits, sbits), Box::new(pattern));
                    samples.push(Sample { sym, exp, text });
                }
                WitnessSort::Other => skipped += 1,
            }
        }
        let attempted = samples.len();
        assert!(
            attempted > 0,
            "witness 随机化没有可按 sort 采样的符号（共 {} 个符号，跳过 {} 个）",
            symbols.len(),
            skipped
        );

        // RNG 序打乱后再按前缀截断：二分丢弃的是无偏随机子集。若按声明序截断，
        // 固定丢掉同一批符号（如晚声明的向量上下文寄存器），会系统性削弱随机化。
        for index in (1..samples.len()).rev() {
            let swap_with = (rng.draw() % (index as u64 + 1)) as usize;
            samples.swap(index, swap_with);
        }
        let all_samples: BTreeMap<String, String> =
            samples.iter().map(|sample| (sample.sym.to_string(), sample.text.clone())).collect();

        let mut accepted = false;
        let mut unknown = false;
        let mut bisection_rounds = 0usize;
        let mut injected = 0usize;
        for (round, keep) in bisection_schedule(attempted).into_iter().enumerate() {
            bisection_rounds = round;
            samples.truncate(keep);
            let assumption = samples
                .iter()
                .map(|sample| Exp::Eq(Box::new(Exp::Var(sample.sym)), Box::new(sample.exp.clone())))
                .reduce(|lhs, rhs| Exp::And(Box::new(lhs), Box::new(rhs)))
                .expect("采样符号集非空");
            match self.check_sat_with(&assumption, info) {
                SmtResult::Sat => {
                    accepted = true;
                    injected = keep;
                    break;
                }
                // 路径已把这些符号约束成别的值时诚实 UNSAT：丢弃一半重试。
                SmtResult::Unsat => continue,
                SmtResult::Unknown => {
                    unknown = true;
                    break;
                }
                SmtResult::Error(error) => return Err(ExecError::Smt(error)),
            }
        }
        if !accepted {
            // 全部轮次 UNSAT/Unknown：回退 plain 模型。进入本函数前 plain check 已
            // SAT，此处 UNSAT 属于不变量违反。
            match self.check_sat(info) {
                SmtResult::Sat => (),
                SmtResult::Unsat => panic!("witness 随机化回退后的 plain check 不可能 UNSAT"),
                SmtResult::Unknown => return Err(ExecError::Z3Unknown),
                SmtResult::Error(error) => return Err(ExecError::Smt(error)),
            }
        }
        Ok(WitnessRandomization {
            seed,
            accepted,
            unknown,
            bisection_rounds,
            attempted,
            injected,
            skipped,
            samples: all_samples,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::bitvector::b64::B64;
    use crate::smt::smtlib::Ty;
    use crate::smt::{Config, Context, Model, ModelVal};

    /// Context 与 Solver 存在借用关系，用闭包把二者限制在同一作用域内。
    fn with_solver<R>(test: impl FnOnce(&mut Solver<'_, B64>) -> R) -> R {
        crate::smt::configure_tastic(crate::smt::Tactic::Qfaufbv);
        let context = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&context);
        test(&mut solver)
    }

    /// 读模型里一个位向量符号的取值（低位在前的 u64）；Arbitrary 时走与
    /// solve_pre_state_complete 相同的 model completion 路径。
    fn model_bits(solver: &mut Solver<'_, B64>, sym: Sym) -> u64 {
        // 不做额外 check：模型必须与最近一次 check（注入或回退）关联。
        let mut model = Model::new(&*solver);
        let value = match model.get_finite_domain_var(sym).unwrap().expect("模型必须有该符号的取值") {
            ModelVal::Arbitrary(_) => {
                model.set_complete_model(true);
                model.get_finite_domain_var(sym).unwrap().expect("completion 后必须有该符号的取值")
            }
            value => value,
        };
        match value {
            ModelVal::Exp(Exp::Bits64(bv)) => bv.lower_u64(),
            ModelVal::Exp(Exp::Bits(bits)) => {
                let mut result = 0_u64;
                for (index, bit) in bits.iter().take(64).enumerate() {
                    if *bit {
                        result |= 1 << index;
                    }
                }
                result
            }
            other => panic!("非位向量模型值 {other:?}"),
        }
    }

    #[test]
    fn splitmix64_is_deterministic_and_bitvector_candidate_respects_width() {
        assert_eq!(splitmix64(42), splitmix64(42));
        assert_ne!(splitmix64(42), splitmix64(43));
        for width in [1u32, 4, 12, 31, 63, 64] {
            match bitvector_candidate(7, width) {
                Exp::Bits64(bv) => assert_eq!(bv.len(), width, "候选值位宽必须与请求一致"),
                other => panic!("64 位内候选必须是 Bits64：{other:?}"),
            }
        }
        match bitvector_candidate(7, 128) {
            Exp::Bits(bits) => assert_eq!(bits.len(), 128, "宽候选值位宽必须与请求一致"),
            other => panic!("64 位以上候选必须是 Bits：{other:?}"),
        }
    }

    #[test]
    fn rng_is_deterministic_and_seed_sensitive() {
        let mut first = WitnessRng::new(100, 0x1234_5678);
        let mut second = WitnessRng::new(100, 0x1234_5678);
        let mut third = WitnessRng::new(101, 0x1234_5678);
        for _ in 0..32 {
            let value = first.draw();
            assert_eq!(value, second.draw(), "同 (seed, signature) 必须逐位一致");
            assert_ne!(value, third.draw(), "不同 seed 的序列应当不同");
        }
        let mut other_signature = WitnessRng::new(100, 0xdead_beef);
        assert_ne!(first.draw(), other_signature.draw(), "不同 path_signature 的序列应当不同");
    }

    /// 二分调度长度恰为 floor(log2 n)+1：机制对总注入次数的上限。
    #[test]
    fn bisection_schedule_caps_attempts_at_log2_plus_one() {
        assert_eq!(bisection_schedule(1), vec![1]);
        assert_eq!(bisection_schedule(2), vec![2, 1]);
        assert_eq!(bisection_schedule(4), vec![4, 2, 1]);
        assert_eq!(bisection_schedule(100), vec![100, 50, 25, 12, 6, 3, 1]);
        for total in 1..200usize {
            let schedule = bisection_schedule(total);
            assert_eq!(schedule.len(), usize::ilog2(total) as usize + 1, "总 {total} 的调度长度");
            assert_eq!(schedule[0], total);
            assert_eq!(*schedule.last().unwrap(), 1, "调度必须收尾到单符号");
        }
    }

    /// 红场景：不开随机化时，plain check 的模型对自由位向量恒取退化值 0——复现
    /// 官方 solve 中不在身份约束里的模型变量被 model completion 填 0 的行为。
    #[test]
    fn plain_model_yields_degenerate_zero() {
        with_solver(|solver| {
            let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            for _ in 0..8 {
                assert_eq!(model_bits(solver, vl), 0, "不开随机化时自由符号必须恒为 0（退化模型）");
            }
        });
    }

    /// 注入后自由符号分布非退化（>=3 个不同值），且模型值与采样值一致。
    #[test]
    fn randomization_diversifies_free_symbols() {
        with_solver(|solver| {
            let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let mut seen = BTreeSet::new();
            for signature in 0..64u64 {
                let record = solver
                    .randomize_witness(std::slice::from_ref(&vl), 0x5eed, signature, SourceLoc::unknown())
                    .unwrap();
                assert!(record.accepted, "自由符号的注入不应回退：{record:?}");
                assert_eq!(record.bisection_rounds, 0, "单符号无冲突时不做二分");
                let value: u64 = record.samples[&vl.to_string()].parse().expect("64 位内采样值记录为十进制");
                seen.insert(value);
                assert_eq!(model_bits(solver, vl), value, "模型必须携带注入值");
            }
            assert!(seen.len() >= 3, "采样分布必须非退化，实际 {seen:?}");
        });
    }

    /// 路径已把符号钉在别的值时：冲突采样 UNSAT，回退后模型保留路径约束值；
    /// 与路径一致的采样 SAT。二分在多符号场景丢弃冲突假设（见下个测试）。
    #[test]
    fn randomization_falls_back_when_constrained() {
        with_solver(|solver| {
            let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
            // 模拟执行路径已经把 vl 钉在 2。
            solver.assert_eq(Exp::Var(vl), smtlib::bits64(2, 64));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let mut rejected = 0;
            for signature in 0..16u64 {
                let record = solver.randomize_witness(&[vl], 0x5eed, signature, SourceLoc::unknown()).unwrap();
                let sampled: u64 = record.samples[&vl.to_string()].parse().expect("64 位内采样值记录为十进制");
                if sampled == 2 {
                    assert!(record.accepted, "与路径约束一致的采样必须 SAT：{sampled}");
                } else {
                    assert!(!record.accepted, "与路径约束冲突的采样必须 UNSAT 回退：{sampled}");
                    rejected += 1;
                }
                assert_eq!(model_bits(solver, vl), 2, "回退后模型必须保留路径约束值");
            }
            assert!(rejected > 0, "16 条路径签名中必须出现 UNSAT 回退以覆盖回退路径");
        });
    }

    /// 多符号联合注入 UNSAT 时按二分丢弃，最终以子集 SAT，且不丢 case。
    #[test]
    fn bisection_drops_conflicting_assumptions_until_sat() {
        with_solver(|solver| {
            let symbols: Vec<Sym> =
                (0..4).map(|_| solver.declare_const(Ty::BitVec(64), SourceLoc::unknown())).collect();
            // 把后两个符号钉在 0：采样出非 0 值的假设与路径约束冲突。
            solver.assert_eq(Exp::Var(symbols[2]), smtlib::bits64(0, 64));
            solver.assert_eq(Exp::Var(symbols[3]), smtlib::bits64(0, 64));
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            // 找一个满足测试场景的 seed：两个冲突符号都采出非 0 值（全量注入必
            // UNSAT），且二分丢弃冲突假设后能以子集 SAT。前缀截断可能把冲突假设
            // 留到最后一轮，此时按机制诚实回退 plain 模型，不属于本测试场景。
            let seed = (0..64u64)
                .find(|seed| {
                    let record = solver.randomize_witness(&symbols, *seed, 1, SourceLoc::unknown()).unwrap();
                    let conflicts_nonzero = [2usize, 3]
                        .iter()
                        .all(|index| record.samples[&symbols[*index].to_string()].parse::<u64>().unwrap() != 0);
                    conflicts_nonzero && record.accepted && record.bisection_rounds >= 1
                })
                .expect("64 个 seed 中必有一个触发二分丢弃后 SAT 的场景");
            let record = solver.randomize_witness(&symbols, seed, 1, SourceLoc::unknown()).unwrap();
            assert!(record.accepted, "二分丢弃冲突假设后必须 SAT：{record:?}");
            assert!(record.bisection_rounds >= 1, "全量 UNSAT 后必须发生二分丢弃：{record:?}");
            assert!(record.injected < record.attempted, "冲突假设必须被丢弃：{record:?}");
            // 冲突符号的采样值非 0，不可能留在生效集合里；路径约束保持。
            assert_eq!(model_bits(solver, symbols[2]), 0, "路径约束必须保持");
            assert_eq!(model_bits(solver, symbols[3]), 0, "路径约束必须保持");
            // 生效集合里的每个假设都落到模型上（被丢弃的假设也可能恰好等于模型
            // 值，因此只验证下界）。
            let landed = symbols
                .iter()
                .filter(|sym| model_bits(solver, **sym) == record.samples[&sym.to_string()].parse::<u64>().unwrap())
                .count();
            assert!(landed >= record.injected, "生效假设必须全部落到模型：{record:?}");
        });
    }

    /// 同 (seed, path_signature) 两次独立求解的采样逐位一致；不同 seed 分布不同。
    #[test]
    fn same_seed_reproduces_and_different_seed_differs() {
        let draw = |seed: u64, signature: u64| {
            with_solver(|solver| {
                let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
                let fcsr = solver.declare_const(Ty::BitVec(12), SourceLoc::unknown());
                assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
                let record = solver.randomize_witness(&[vl, fcsr], seed, signature, SourceLoc::unknown()).unwrap();
                (record.samples.clone(), model_bits(solver, vl), model_bits(solver, fcsr))
            })
        };
        let mut differences = 0;
        for signature in 0..32u64 {
            let first = draw(0x5eed, signature);
            assert_eq!(first, draw(0x5eed, signature), "同 seed 复跑必须逐位一致");
            if first != draw(0x5eed + 1, signature) {
                differences += 1;
            }
        }
        assert!(differences > 0, "不同 seed 的分布必须不同");
    }

    /// assumption 只作用于当次 check：前一次注入不改变约束栈，后一次注入独立判定，
    /// 模型只携带当次注入值。
    #[test]
    fn assumptions_never_enter_assertion_stack() {
        with_solver(|solver| {
            let vl = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
            let vtype = solver.declare_const(Ty::BitVec(64), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let first = solver.randomize_witness(&[vl, vtype], 0x5eed, 1, SourceLoc::unknown()).unwrap();
            assert!(first.accepted);
            let second = solver.randomize_witness(&[vl, vtype], 0x5eed, 2, SourceLoc::unknown()).unwrap();
            assert!(second.accepted, "第二次注入必须独立判定，不受第一次 assumption 影响");
            let value: u64 = second.samples[&vl.to_string()].parse().unwrap();
            assert_eq!(model_bits(solver, vl), value, "模型必须携带当次注入值");
        });
    }

    /// 非 BV/Float 的 sort（Bool、数组、RoundingMode、枚举）不参与采样，只计数。
    #[test]
    fn unsupported_sorts_are_skipped_and_counted() {
        with_solver(|solver| {
            let bits = solver.declare_const(Ty::BitVec(8), SourceLoc::unknown());
            let boolean = solver.declare_const(Ty::Bool, SourceLoc::unknown());
            let array =
                solver.declare_const(Ty::Array(Box::new(Ty::BitVec(8)), Box::new(Ty::BitVec(8))), SourceLoc::unknown());
            let rounding = solver.declare_const(Ty::RoundingMode, SourceLoc::unknown());
            let enum_id = solver.get_enum(crate::ir::Name::from_u32(501), 3);
            let enumeration = solver.declare_const(Ty::Enum(enum_id), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let record = solver
                .randomize_witness(&[bits, boolean, array, rounding, enumeration], 9, 1, SourceLoc::unknown())
                .unwrap();
            assert_eq!(record.attempted, 1, "只有位向量参与采样：{record:?}");
            assert_eq!(record.skipped, 4, "Bool/数组/RoundingMode/枚举都必须跳过：{record:?}");
            assert!(record.samples.contains_key(&bits.to_string()));
        });
    }

    /// Float 符号按位模式采样并以 to_fp 构造：自由浮点符号注入后 SAT，且模型中的
    /// 浮点值位模式与采样一致（经 to_ieee_bv 反查验证）。
    #[test]
    fn float_symbols_are_sampled_by_sort() {
        with_solver(|solver| {
            let f = solver.declare_const(Ty::Float(11, 52), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let mut seen = BTreeSet::new();
            for signature in 0..32u64 {
                let record = solver
                    .randomize_witness(std::slice::from_ref(&f), 0x5eed, signature, SourceLoc::unknown())
                    .unwrap();
                assert!(record.accepted, "自由浮点符号的注入不应回退：{record:?}");
                let pattern = u64::from_str_radix(record.samples[&f.to_string()].trim_start_matches("0x"), 16)
                    .expect("浮点采样值记录为十六进制位模式");
                assert!(pattern < (1_u64 << 63), "位模式必须落在 63 位（11+52）内");
                seen.insert(pattern);
                // 模型中的浮点值必须携带采样位模式：用 to_ieee_bv 在模型内求值反查。
                let mut model = Model::new(&*solver);
                match model.get_exp(&Exp::FPUnary(FPUnary::ToIEEE(11, 52), Box::new(Exp::Var(f)))).unwrap() {
                    ModelVal::Exp(Exp::Bits64(bv)) => {
                        assert_eq!(bv.lower_u64(), pattern, "模型浮点值的 IEEE 位模式必须与采样一致")
                    }
                    other => panic!("to_ieee_bv 求值必须得到位向量：{other:?}"),
                }
            }
            assert!(seen.len() >= 3, "浮点位模式采样必须非退化，实际 {seen:?}");
        });
    }

    /// 宽位向量（>64 位，如 vr 载荷）也参与采样；元数据记录低 64 位十六进制。
    #[test]
    fn wide_bitvectors_are_sampled() {
        with_solver(|solver| {
            let payload = solver.declare_const(Ty::BitVec(128), SourceLoc::unknown());
            assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat);
            let mut seen = BTreeSet::new();
            for signature in 0..16u64 {
                let record = solver
                    .randomize_witness(std::slice::from_ref(&payload), 0x5eed, signature, SourceLoc::unknown())
                    .unwrap();
                assert!(record.accepted, "自由宽位向量的注入不应回退：{record:?}");
                let low = u64::from_str_radix(record.samples[&payload.to_string()].trim_start_matches("0x"), 16)
                    .expect("宽符号采样值记录为低 64 位十六进制");
                seen.insert(low);
                assert_eq!(model_bits(solver, payload), low, "模型必须携带注入值（低 64 位）");
            }
            assert!(seen.len() >= 3, "宽位向量采样必须非退化，实际 {seen:?}");
        });
    }

    /// 汇总：从 terminal 记录聚合 attempted/accepted/fallback/unknown。
    #[test]
    fn summary_aggregates_terminal_records() {
        let record = |accepted: bool, unknown: bool| WitnessRandomization {
            seed: 7,
            accepted,
            unknown,
            bisection_rounds: 0,
            attempted: 4,
            injected: if accepted { 4 } else { 0 },
            skipped: 0,
            samples: BTreeMap::new(),
        };
        let summary = SummaryWitnessRandomization::from_terminals(
            7,
            &[Some(record(true, false)), None, Some(record(false, true))],
        )
        .expect("有记录时必须汇总");
        assert_eq!(
            (summary.seed, summary.attempted, summary.accepted, summary.fallback, summary.unknown),
            (7, 2, 1, 1, 1)
        );
        assert!(SummaryWitnessRandomization::from_terminals(7, &[None]).is_none());
    }
}
