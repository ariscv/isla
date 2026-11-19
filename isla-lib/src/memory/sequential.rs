//! W2 数组内存模型：用 SMT 字节数组 `(Array (_ BitVec addr_size) (_ BitVec 8))`
//! 建模符号内存，使同一条执行路径内同地址读写保持一致：
//!
//! - 读：读值 == 逐字节 `Select` 后按小端 `Concat` 拼接（低地址在低位，与
//!   sail-riscv RV64 小端一致）；
//! - 写：对写数据逐字节 `Extract` 构造 `Store` 链；普通写发出事件即提交，
//!   独占写按返回 Bool 条件提交，之后同一路径的读写都基于新数组；
//! - Concrete／Constrained 区域：按需将具体内容或生成器约束接入初始数组；
//!   普通具体读与符号读共享当前数组，后续写入可以覆盖初值；
//! - Custom 由 Memory 保留设备分派；Constrained 保留整区域读取合同，读值查询当前数组；
//! - **默认（W9 语义）：全符号化**。符号读写地址全域自由、读值/写效来自
//!   字节数组，`[[memory_regions]]` 的 symbolic 声明只是"这一段是 RAM、
//!   内容未知"的**纯声明**，不产生任何约束；可访问性/trap 完全交给模型
//!   自身的 PMA/PMP：可访问则正常访存，不可访问则由模型分叉出访存 trap/
//!   access fault，**fault 路径是合法输出、不许被内存层抹掉**；
//! - **判死区域（W9 新语义，`region_type = "excluded"`）**：声明"这一段
//!   不关心，遇到了是 unsat"。符号读写地址追加 NOT(与判死区域并集重叠)
//!   约束（`smt_excluded_constraint`），并沿用 W7 的"回调追加约束后立即
//!   check_sat"机制——与路径既有断言（如模型侧 PMA 分支）联立 Unsat 时
//!   立即以 BadRead/BadWrite 判死、不发出访存事件；具体地址与判死区域
//!   重叠时由 `Memory` 的具体地址分派直接 BadRead/BadWrite。判死对读和
//!   写一视同仁；零判死区域 = 零约束零开销，与默认一致。
//!
//! 范式来源：上游 isla-testgen 的 `SeqMemory`（esop22 谱系，与本仓 f06371f
//! 的 API 有差异，按本仓源码改写）。
//!
use crate::bitvector::BV;
use crate::ir::Val;
use crate::log;
use crate::memory::{smt_excluded_constraint, Memory, MemoryCallbacks, Region};
use crate::primop_util::{length_bits, smt_value};
use crate::smt::smtlib::{bits64, Def, Exp, Ty};
use crate::smt::{ReadOpts, Solver, Sym, WriteOpts};
use crate::source_loc::SourceLoc;

/// 顺序内存回调：持有当前数组常量。每次符号写把数组重定义为新常量并更新此记录；
/// 读路径只读，依赖 `Clone` 快照与执行路径的 fork 语义保持各路径独立。
#[derive(Debug, Clone)]
pub struct SeqMemory {
    initial_memory_var: Sym,
    memory_var: Sym,
    addr_size: u32,
    exclusive_writes_succeed: bool,
}

/// 在 solver 中声明初始数组常量 `(Array (_ BitVec addr_size) (_ BitVec 8))`
/// 并把回调装入 `memory`。必须在生成后续 checkpoint 之前调用，使所有执行
/// 路径共享初始数组定义。
pub fn install_seq_memory<B: BV>(
    memory: &mut Memory<B>,
    addr_size: u32,
    solver: &mut Solver<B>,
    exclusive_writes_succeed: bool,
) {
    assert!(addr_size > 0, "数组索引位宽必须为正");
    let memory_var = solver.fresh();
    solver.add(Def::DeclareConst(memory_var, Ty::Array(Box::new(Ty::BitVec(addr_size)), Box::new(Ty::BitVec(8)))));
    memory.set_client_info(Box::new(SeqMemory {
        initial_memory_var: memory_var,
        memory_var,
        addr_size,
        exclusive_writes_succeed,
    }));
    log!(log::MEMORY, &format!("数组内存模型已启用: memory_var={} addr_size={}", memory_var, addr_size));
}

/// 读值逐字节拼接表达式（小端：addr+i 的字节位于第 i 字节）。
fn smt_read_exp(memory: Sym, addr_exp: &Exp<Sym>, addr_size: u32, bytes: u64) -> Exp<Sym> {
    let mut mem_exp = Exp::Select(Box::new(Exp::Var(memory)), Box::new(addr_exp.clone()));
    for i in 1..bytes {
        mem_exp = Exp::Concat(
            Box::new(Exp::Select(
                Box::new(Exp::Var(memory)),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(bits64(i, addr_size)))),
            )),
            Box::new(mem_exp),
        )
    }
    mem_exp
}

impl SeqMemory {
    /// 数组运算统一使用索引位宽；访存事件仍由 Memory 保存原始地址。
    fn array_address<B: BV>(&self, address: &Val<B>, solver: &mut Solver<B>) -> Exp<Sym> {
        let width = length_bits(address, solver, SourceLoc::unknown()).expect("数组地址必须是位向量");
        let address = smt_value(address, SourceLoc::unknown()).expect("数组地址必须具有 SMT 表示");
        if width > self.addr_size {
            Exp::Extract(self.addr_size - 1, 0, Box::new(address))
        } else if width < self.addr_size {
            Exp::ZeroExtend(self.addr_size - width, Box::new(address))
        } else {
            address
        }
    }
}

impl<B: BV> MemoryCallbacks<B> for SeqMemory {
    // 读取只向调用方的 solver 添加约束，区域／回调自身的路径状态不变。
    fn is_pure_reader(&self) -> bool {
        true
    }

    fn ram_version(&self) -> Option<Sym> {
        Some(self.memory_var)
    }

    fn set_ram_version(&mut self, version: Sym) {
        self.memory_var = version;
    }

    fn constrains_symbolic_writes(&self) -> bool {
        true
    }

    fn constrains_symbolic_reads(&self) -> bool {
        true
    }

    fn handles_concrete_reads(&self) -> bool {
        true
    }

    fn symbolic_read(
        &self,
        regions: &[Region<B>],
        solver: &mut Solver<B>,
        value: &Val<B>,
        _read_kind: &Val<B>,
        address: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        _opts: &ReadOpts,
    ) -> bool {
        // 此顺序内存只存放数据字节，不存放 capability tag
        if let Some(tag_value) = tag {
            panic!("顺序数组内存不支持带 capability tag 的符号读: {:?}", tag_value);
        }

        let read_exp = smt_value(value, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号读值不是位向量 {:?}: {}", value, err));
        let array_addr = self.array_address(address, solver);

        // 只约束本次查询涉及的初始字节；Store 链仍可覆盖初值，不能钉死当前数组。
        // 沿用 Memory 的区域优先级，前序区域遮蔽后续区域的初值。
        if regions.iter().any(|region| matches!(region, Region::Concrete(..) | Region::Constrained(..))) {
            // 同次多字节读取只调用每个生成器一次，保留区域内各字节的关联。
            let mut generated = vec![None; regions.len()];
            for i in 0..bytes {
                let byte_addr = solver.define_const(
                    Exp::Bvadd(Box::new(array_addr.clone()), Box::new(bits64(u64::from(i), self.addr_size))),
                    SourceLoc::unknown(),
                );
                let region_addr = if self.addr_size > 64 {
                    Exp::Extract(63, 0, Box::new(Exp::Var(byte_addr)))
                } else if self.addr_size < 64 {
                    Exp::ZeroExtend(64 - self.addr_size, Box::new(Exp::Var(byte_addr)))
                } else {
                    Exp::Var(byte_addr)
                };
                let mut unmatched = Exp::Bool(true);
                for (region_index, region) in regions.iter().enumerate() {
                    if matches!(region, Region::Excluded(_)) {
                        continue;
                    }
                    let range = region.region_range();
                    let in_region = Exp::And(
                        Box::new(Exp::Bvule(Box::new(bits64(range.start, 64)), Box::new(region_addr.clone()))),
                        Box::new(Exp::Bvult(Box::new(region_addr.clone()), Box::new(bits64(range.end, 64)))),
                    );
                    let selected = Exp::And(Box::new(unmatched.clone()), Box::new(in_region.clone()));
                    let initial_byte = if let Region::Concrete(_, contents) = region {
                        let mut initial_byte = bits64(0, 8);
                        let mut entries: Vec<_> = contents.iter().collect();
                        entries.sort_unstable_by_key(|(address, _)| **address);
                        for (&address, &value) in entries {
                            initial_byte = Exp::Ite(
                                Box::new(Exp::Eq(Box::new(region_addr.clone()), Box::new(bits64(address, 64)))),
                                Box::new(bits64(u64::from(value), 8)),
                                Box::new(initial_byte),
                            );
                        }
                        Some(initial_byte)
                    } else if let Region::Constrained(range, generator) = region {
                        if solver
                            .check_candidate_sat_with(&selected, SourceLoc::unknown())
                            .map(|result| result.is_unsat())
                            .transpose()
                            .expect("生成器初值的区域可达性检查必须成功")
                            .unwrap_or(false)
                        {
                            None
                        } else {
                            let width = u32::try_from(range.end - range.start)
                                .unwrap()
                                .checked_mul(8)
                                .expect("生成器区域位宽必须能用 u32 表示");
                            assert!(width >= 8, "生成器区域不能为空");
                            let generated = *generated[region_index].get_or_insert_with(|| {
                                let value = generator(solver);
                                assert_eq!(solver.length(value), Some(width), "生成器位宽必须匹配整个区域");
                                solver.mark_bitvector(value);
                                value
                            });
                            // 生成器低字节对应区域起点，与读值的小端拼接一致。
                            let offset = Exp::Bvmul(
                                Box::new(Exp::Bvsub(Box::new(region_addr.clone()), Box::new(bits64(range.start, 64)))),
                                Box::new(bits64(8, 64)),
                            );
                            let shift = if width > 64 {
                                Exp::ZeroExtend(width - 64, Box::new(offset))
                            } else if width < 64 {
                                Exp::Extract(width - 1, 0, Box::new(offset))
                            } else {
                                offset
                            };
                            Some(Exp::Extract(
                                7,
                                0,
                                Box::new(Exp::Bvlshr(Box::new(Exp::Var(generated)), Box::new(shift))),
                            ))
                        }
                    } else {
                        None
                    };
                    if let Some(initial_byte) = initial_byte {
                        let initial =
                            Exp::Select(Box::new(Exp::Var(self.initial_memory_var)), Box::new(Exp::Var(byte_addr)));
                        solver.assert(Exp::Or(
                            Box::new(Exp::Not(Box::new(selected))),
                            Box::new(Exp::Eq(Box::new(initial), Box::new(initial_byte))),
                        ));
                    }
                    unmatched = Exp::And(Box::new(unmatched), Box::new(Exp::Not(Box::new(in_region))));
                }
            }
        }

        // 读值逐字节等于数组内容（小端拼接）
        let read_prop = Exp::Eq(
            Box::new(read_exp),
            Box::new(smt_read_exp(self.memory_var, &array_addr, self.addr_size, u64::from(bytes))),
        );

        // 判死区域（W9）：追加以读地址为自由变量的 NOT(与判死区域并集重叠)
        // 约束；零判死区域返回 None，不加任何约束（默认全符号化语义不变）。
        // 返回 true 触发 read_symbolic 的 W7 立即判死检查。
        let (full_constraint, constrained) = match smt_excluded_constraint(regions, &array_addr, bytes, solver) {
            Some(not_overlap) => (Exp::And(Box::new(not_overlap), Box::new(read_prop)), true),
            None => (read_prop, false),
        };
        solver.add(Def::Assert(full_constraint));
        constrained
    }

    fn symbolic_write(
        &mut self,
        regions: &[Region<B>],
        solver: &mut Solver<B>,
        value: Sym,
        _write_kind: &Val<B>,
        address: &Val<B>,
        data: &Val<B>,
        bytes: u32,
        tag: &Option<Val<B>>,
        opts: &WriteOpts,
    ) -> bool {
        // 此顺序内存只存放数据字节，不存放 capability tag
        if let Some(tag_value) = tag {
            panic!("顺序数组内存不支持带 capability tag 的符号写: {:?}", tag_value);
        }
        if bytes == 0 {
            panic!("数组内存模型不支持 0 字节符号写");
        }

        let data_exp = smt_value(data, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号写数据不是位向量 {:?}: {}", data, err));
        let array_addr = self.array_address(address, solver);

        // 小端逐字节 Store 链：第 i 字节写到 addr+i
        let mut mem_exp = Exp::Store(
            Box::new(Exp::Var(self.memory_var)),
            Box::new(array_addr.clone()),
            Box::new(Exp::Extract(7, 0, Box::new(data_exp.clone()))),
        );
        for i in 1..bytes {
            mem_exp = Exp::Store(
                Box::new(mem_exp),
                Box::new(Exp::Bvadd(Box::new(array_addr.clone()), Box::new(bits64(u64::from(i), self.addr_size)))),
                Box::new(Exp::Extract(i * 8 + 7, i * 8, Box::new(data_exp.clone()))),
            );
        }
        // 独占写的返回布尔值表示是否提交。已由调用者确认成功的请求可直接更新数组。
        let next_exp = if opts.is_exclusive() && !self.exclusive_writes_succeed {
            Exp::Ite(Box::new(Exp::Var(value)), Box::new(mem_exp), Box::new(Exp::Var(self.memory_var)))
        } else {
            if opts.is_exclusive() {
                solver.add(Def::Assert(Exp::Var(value)));
            }
            mem_exp
        };
        self.memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.memory_var, next_exp));

        // 判死区域（W9）：与读侧对称，追加 NOT(与判死区域并集重叠) 约束，
        // 返回 true 触发 write_symbolic 的 W7 立即判死检查；零判死区域不加
        // 任何约束。
        match smt_excluded_constraint(regions, &array_addr, bytes, solver) {
            Some(not_overlap) => {
                solver.add(Def::Assert(not_overlap));
                true
            }
            None => false,
        }
    }

    fn symbolic_write_tag(
        &mut self,
        _regions: &[Region<B>],
        _solver: &mut Solver<B>,
        _value: Sym,
        _write_kind: &Val<B>,
        _address: &Val<B>,
        _tag: &Val<B>,
    ) {
        // RV64 无 capability tag，按 W2 约定空实现；默认路径的事件语义保持不变
    }
}
