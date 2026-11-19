//! 为已知可满足的路径选择代表。随机偏好只作为单次求解的假设。
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WitnessRandomization {
    pub seed: u64,
    pub attempted: usize,
    pub injected: usize,
}

fn draw(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn candidate(state: &mut u64, width: u32) -> Exp<Sym> {
    assert!(width > 0);
    if width <= 64 {
        let word = draw(state);
        let value = match word & 7 {
            0 => 0,
            1 => 1,
            2..=5 => (word >> 3) & 63,
            _ => draw(state),
        };
        return smtlib::bits64(value & (u64::MAX >> (64 - width)), width);
    }
    let mut bits = Vec::with_capacity(width as usize);
    for low in (0..width).step_by(64) {
        let word = draw(state);
        bits.extend((0..(width - low).min(64)).map(|bit| word >> bit & 1 != 0));
    }
    Exp::Bits(bits)
}

impl<B: BV> Solver<'_, B> {
    /// 尝试用满足偏好的完整模型替换已缓存见证。偏好不满足或未证实时保留已认证模型。
    pub fn randomize_witness(&mut self, symbols: &[Sym], seed: u64, path: u64) -> WitnessRandomization {
        assert!(self.has_stashed_model(), "随机化前必须持有已认证的模型");
        let mut symbols = symbols.to_vec();
        symbols.sort_unstable_by_key(|sym| sym.as_u32());
        symbols.dedup();
        let mut state = seed ^ path.rotate_left(17);
        let mut preferences: Vec<_> = symbols
            .into_iter()
            .filter_map(|symbol| {
                assert!(self.decls.contains_key(&symbol), "随机化符号 {symbol} 未在求解器中登记");
                let value = match self.scalar_sort(symbol)? {
                    Ty::Bool => Exp::Bool(draw(&mut state) & 1 != 0),
                    Ty::BitVec(width) => candidate(&mut state, width),
                    Ty::Float(exponent, significand) => Exp::FPUnary(
                        smtlib::FPUnary::FromIEEE(exponent, significand),
                        Box::new(candidate(&mut state, exponent + significand)),
                    ),
                    _ => return None,
                };
                Some(Exp::Eq(Box::new(Exp::Var(symbol)), Box::new(value)))
            })
            .collect();
        for index in (1..preferences.len()).rev() {
            let swap = (draw(&mut state) % (index as u64 + 1)) as usize;
            preferences.swap(index, swap);
        }
        let attempted = preferences.len();
        let mut keep = attempted;
        let mut injected = 0;
        while keep != 0 {
            let assumption = preferences[..keep]
                .iter()
                .cloned()
                .reduce(|left, right| Exp::And(Box::new(left), Box::new(right)))
                .unwrap();
            match self.check_sat_with(&assumption, SourceLoc::unknown()) {
                SmtResult::Sat => {
                    injected = keep;
                    break;
                }
                SmtResult::Unsat => keep /= 2,
                // 这是对代表值的可选偏好。当前求解器始终持有满足原路径的模型。
                SmtResult::Unknown | SmtResult::Error(_) => break,
            }
        }
        assert!(self.has_stashed_model(), "随机偏好不应丢弃已认证的模型");
        WitnessRandomization { seed, attempted, injected }
    }
}

#[cfg(test)]
mod tests;
