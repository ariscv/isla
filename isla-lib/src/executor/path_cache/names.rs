//! 名字编号保持原样；不做编号重定位或 IR 函数语义复核。
use crate::ir::{IRTypeInfo, Name, Symtab};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NameEnvironment {
    pub symbols: Vec<String>,
    pub mangled_names: Vec<(Name, String)>,
    pub enums: Vec<(Name, Vec<(Name, String)>)>,
    pub files: Vec<String>,
}

impl NameEnvironment {
    pub fn capture(symtab: &Symtab, types: &IRTypeInfo) -> Self {
        let (symbols, files) = symtab.to_raw_table();
        let mut mangled_names = symtab.mangled_names.iter().map(|(n, s)| (*n, s.to_string())).collect::<Vec<_>>();
        mangled_names.sort_by_key(|(n, _)| *n);
        let mut enums = types
            .enums
            .iter()
            .map(|(n, members)| (*n, members.iter().map(|m| (*m, symbols[m.as_u32() as usize].clone())).collect()))
            .collect::<Vec<_>>();
        enums.sort_by_key(|(n, _)| *n);
        let environment = Self { symbols, mangled_names, enums, files };
        environment.validate(symtab, types);
        environment
    }

    pub fn validate(&self, symtab: &Symtab, types: &IRTypeInfo) {
        let (symbols, files) = symtab.to_raw_table();
        for (i, symbol) in self.symbols.iter().enumerate() {
            assert_eq!(symbols.get(i), Some(symbol), "缓存符号表编号 {i} 不一致");
        }
        let current = symtab
            .mangled_names
            .iter()
            .filter(|(n, _)| (n.as_u32() as usize) < self.symbols.len())
            .map(|(n, s)| (*n, s.to_string()))
            .collect::<std::collections::BTreeMap<_, _>>();
        let expected = self.mangled_names.iter().cloned().collect::<std::collections::BTreeMap<_, _>>();
        assert_eq!(expected.len(), self.mangled_names.len(), "缓存反混淆编号重复");
        let names = current.keys().chain(expected.keys()).copied().collect::<std::collections::BTreeSet<_>>();
        for name in names {
            assert_eq!(expected.get(&name), current.get(&name), "缓存反混淆映射编号 {name} 不一致");
        }
        let expected_enums = self.enums.iter().map(|(name, _)| *name).collect::<std::collections::BTreeSet<_>>();
        assert_eq!(expected_enums.len(), self.enums.len(), "缓存枚举编号重复");
        let current_enums = types
            .enums
            .keys()
            .filter(|name| (name.as_u32() as usize) < self.symbols.len())
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        for name in current_enums.symmetric_difference(&expected_enums) {
            panic!("缓存枚举表编号 {name} 缺失或多出");
        }
        for (name, members) in &self.enums {
            let actual = types.enums.get(name).expect("缓存枚举类型缺失");
            assert_eq!(members.len(), actual.len(), "缓存枚举大小不一致：{name}");
            for (i, ((member, text), actual)) in members.iter().zip(actual).enumerate() {
                assert_eq!(member, actual, "缓存枚举成员顺序不一致：{name} 位置 {i}");
                assert_eq!(symbols.get(member.as_u32() as usize), Some(text), "缓存枚举名字不一致");
                assert_eq!(
                    types.enum_members.get(member),
                    Some(&(i, members.len(), *name)),
                    "缓存枚举反向表不一致：{member}"
                );
            }
        }
        for (i, file) in self.files.iter().enumerate() {
            assert_eq!(files.get(i), Some(file), "缓存源文件索引 {i} 不一致");
        }
    }
}
