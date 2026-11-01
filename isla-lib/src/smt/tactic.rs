use std::ffi::CStr;
use std::str::FromStr;

/// Isla 支持的 Z3 求解策略。
/// 默认使用 Z3 自身的 Default 策略，仍须通过运行时随机种子能力校验。
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Tactic {
    #[default]
    Default,
    Qfaufbv,
    Qffp,
    Smt,
}

impl FromStr for Tactic {
    type Err = String;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        match name {
            "default" => Ok(Self::Default),
            "qfaufbv" => Ok(Self::Qfaufbv),
            "qffp" => Ok(Self::Qffp),
            "smt" => Ok(Self::Smt),
            _ => Err(format!("不支持的 tactic {name:?}，可选值：default、qfaufbv、qffp、smt")),
        }
    }
}

impl Tactic {
    pub(super) fn as_c_str(self) -> &'static CStr {
        CStr::from_bytes_with_nul(match self {
            Self::Default => b"default\0",
            Self::Qfaufbv => b"qfaufbv\0",
            Self::Qffp => b"qffp\0",
            Self::Smt => b"smt\0",
        })
        .unwrap()
    }
}
