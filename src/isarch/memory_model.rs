//! W2 数组内存模型：用 SMT 字节数组 `(Array (_ BitVec addr_size) (_ BitVec 8))`
//! 建模符号内存，使同一条执行路径内同地址读写保持一致：
//!
//! - 读：读值 == 逐字节 `Select` 后按小端 `Concat` 拼接（低地址在低位，与
//!   sail-riscv RV64 小端一致）；
//! - 写：对写数据逐字节 `Extract` 构造 `Store` 链；普通写发出事件即提交，
//!   独占写按返回 Bool 条件提交，之后同一路径的读写都基于新数组；
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
//! 行为开关：环境变量 `ISLA_RISCV_MEMORY_MODEL`
//! - `array`（默认）：启用本模型的同址读写一致性；
//! - `fresh`：退回 `Memory` 默认行为，每次符号读新建独立位向量变量。

use isla_lib::bitvector::BV;
use isla_lib::ir::Val;
use isla_lib::log;
use isla_lib::memory::{smt_excluded_constraint, Memory, MemoryCallbacks, Region};
use isla_lib::primop_util::smt_value;
use isla_lib::smt::smtlib::{bits64, Def, Exp, Ty};
use isla_lib::smt::{ReadOpts, Solver, Sym, WriteOpts};
use isla_lib::source_loc::SourceLoc;

/// 顺序内存回调：持有当前数组常量。每次符号写把数组重定义为新常量并更新此记录；
/// 读路径只读，依赖 `Clone` 快照与执行路径的 fork 语义保持各路径独立。
#[derive(Debug, Clone)]
pub struct SeqMemory {
    memory_var: Sym,
    addr_size: u32,
}

/// 环境变量 `ISLA_RISCV_MEMORY_MODEL` 是否启用数组模型（默认启用）。
pub fn array_model_enabled() -> bool {
    let value = match std::env::var("ISLA_RISCV_MEMORY_MODEL") {
        Ok(value) => value,
        Err(std::env::VarError::NotPresent) => return true,
        Err(err) => panic!("读取环境变量 ISLA_RISCV_MEMORY_MODEL 失败: {}", err),
    };
    match value.as_str() {
        "array" => true,
        "fresh" => false,
        other => panic!("ISLA_RISCV_MEMORY_MODEL 仅支持 array 或 fresh，实际为 '{}'", other),
    }
}

/// 在 solver 中声明初始数组常量 `(Array (_ BitVec addr_size) (_ BitVec 8))`
/// 并把回调装入 `memory`。必须在生成后续 checkpoint 之前调用，使所有执行
/// 路径共享初始数组定义。
pub fn install_seq_memory<B: BV>(memory: &mut Memory<B>, addr_size: u32, solver: &mut Solver<B>) {
    let memory_var = solver.fresh();
    solver.add(Def::DeclareConst(memory_var, Ty::Array(Box::new(Ty::BitVec(addr_size)), Box::new(Ty::BitVec(8)))));
    memory.set_client_info(Box::new(SeqMemory { memory_var, addr_size }));
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

impl<B: BV> MemoryCallbacks<B> for SeqMemory {
    fn constrains_symbolic_writes(&self) -> bool {
        true
    }

    fn constrains_symbolic_reads(&self) -> bool {
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
        // RV64 模型不使用 capability tag（primop/memory.rs 读路径恒为 tag=false）
        if let Some(tag_value) = tag {
            panic!("RV64 数组内存模型不支持带 capability tag 的符号读: {:?}", tag_value);
        }

        let read_exp = smt_value(value, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号读值不是位向量 {:?}: {}", value, err));
        let addr_exp = smt_value(address, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号读地址不是位向量 {:?}: {}", address, err));

        // 读值逐字节等于数组内容（小端拼接）
        let read_prop = Exp::Eq(
            Box::new(read_exp),
            Box::new(smt_read_exp(self.memory_var, &addr_exp, self.addr_size, u64::from(bytes))),
        );

        // 判死区域（W9）：追加以读地址为自由变量的 NOT(与判死区域并集重叠)
        // 约束；零判死区域返回 None，不加任何约束（默认全符号化语义不变）。
        // 返回 true 触发 read_symbolic 的 W7 立即判死检查。
        let (full_constraint, constrained) = match smt_excluded_constraint(regions, &addr_exp, bytes, solver) {
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
        // RV64 模型不使用 capability tag（primop/memory.rs 写路径恒为 tag=None）
        if let Some(tag_value) = tag {
            panic!("RV64 数组内存模型不支持带 capability tag 的符号写: {:?}", tag_value);
        }
        if bytes == 0 {
            panic!("数组内存模型不支持 0 字节符号写");
        }

        let data_exp = smt_value(data, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号写数据不是位向量 {:?}: {}", data, err));
        let addr_exp = smt_value(address, SourceLoc::unknown())
            .unwrap_or_else(|err| panic!("符号写地址不是位向量 {:?}: {}", address, err));

        // 小端逐字节 Store 链：第 i 字节写到 addr+i
        let mut mem_exp = Exp::Store(
            Box::new(Exp::Var(self.memory_var)),
            Box::new(addr_exp.clone()),
            Box::new(Exp::Extract(7, 0, Box::new(data_exp.clone()))),
        );
        for i in 1..bytes {
            mem_exp = Exp::Store(
                Box::new(mem_exp),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(bits64(u64::from(i), self.addr_size)))),
                Box::new(Exp::Extract(i * 8 + 7, i * 8, Box::new(data_exp.clone()))),
            );
        }
        // Sail 并发接口的 Bool 仅表示 exclusive/CAS 的成败；普通写的 Bool
        // 可以被调用方忽略，事件一旦发出就提交 Store 链。
        // 独占写同理必已提交（F3，campaign24 七例 AMO 非 aqrl post==pre 的根因）：
        // 模型的 write_ram 把并发接口的返回值丢弃（`Ok(_) => true`，
        // phys_mem_interface.sail:109-115），AMO/SC 拿到的提交判定恒为具体 true，
        // "未提交"分支在模型控制流里不可达——独占写事件一旦发出即已提交。
        // 此前 Bool 保持自由，Z3 可任取 false：数组 Ite 选旧值、exec.rs 终值重放
        // 按 write_success=Some(false) 跳过物化。SC 失败在模型里发生于写之前
        // （vmem_write_addr 的 match_reservation 检查不满足时直接跳过写），
        // 不经过本回调，故此处钉死 Bool=true 不吞掉任何合法路径。
        if opts.is_exclusive() {
            solver.add(Def::Assert(Exp::Var(value)));
        }
        let next_exp = mem_exp;
        self.memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.memory_var, next_exp));

        // 判死区域（W9）：与读侧对称，追加 NOT(与判死区域并集重叠) 约束，
        // 返回 true 触发 write_symbolic 的 W7 立即判死检查；零判死区域不加
        // 任何约束。
        match smt_excluded_constraint(regions, &addr_exp, bytes, solver) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::smt::{Config, Context, Event, SmtResult};

    /// 测试用符号地址 id 从 9000 起，避免与 install/fresh 生成的 Sym id 冲突。
    fn test_sym(id: u32) -> Sym {
        Sym::from_u32(9000 + id)
    }

    fn declare_symbol(solver: &mut Solver<B64>, sym: Sym, bits: u32) {
        solver.add(Def::DeclareConst(sym, Ty::BitVec(bits)));
    }

    fn read_bytes(memory: &Memory<B64>, solver: &mut Solver<B64>, addr: Val<B64>, bytes: i128) -> Val<B64> {
        memory.read(Val::Unit, addr, Val::I128(bytes), solver, false, ReadOpts::default()).unwrap()
    }

    fn write_bytes(memory: &mut Memory<B64>, solver: &mut Solver<B64>, addr: Val<B64>, data: B64) -> Val<B64> {
        memory.write(Val::Unit, addr, Val::Bits(data), solver, None, WriteOpts::default()).unwrap()
    }

    fn write_bytes_exclusive(
        memory: &mut Memory<B64>,
        solver: &mut Solver<B64>,
        addr: Val<B64>,
        data: B64,
    ) -> Val<B64> {
        memory.write(Val::Unit, addr, Val::Bits(data), solver, None, WriteOpts::exclusive()).unwrap()
    }

    fn read_sym(val: &Val<B64>) -> Sym {
        match val {
            Val::Symbolic(sym) => *sym,
            _ => panic!("符号读应返回 Val::Symbolic，实际 {:?}", val),
        }
    }

    fn write_sym(val: &Val<B64>) -> Sym {
        match val {
            Val::Symbolic(sym) => *sym,
            _ => panic!("符号写应返回 Val::Symbolic Bool，实际 {:?}", val),
        }
    }

    fn assert_write_success(solver: &mut Solver<B64>, result: &Val<B64>) {
        solver.add(Def::Assert(Exp::Var(write_sym(result))));
    }

    fn expect_unsat(solver: &mut Solver<B64>, prop: Exp<Sym>, what: &str) {
        match solver.check_sat_with(&prop, SourceLoc::unknown()) {
            SmtResult::Unsat => (),
            SmtResult::Sat => panic!("期望 {} 时 Unsat，实际 Sat", what),
            SmtResult::Unknown => panic!("期望 {} 时 Unsat，实际 Unknown", what),
            SmtResult::Error(_) => panic!("期望 {} 时 Unsat，实际 Error", what),
        }
    }

    fn expect_sat_with(solver: &mut Solver<B64>, prop: Exp<Sym>, what: &str) {
        match solver.check_sat_with(&prop, SourceLoc::unknown()) {
            SmtResult::Sat => (),
            SmtResult::Unsat => panic!("期望 {} 时 Sat，实际 Unsat", what),
            SmtResult::Unknown => panic!("期望 {} 时 Sat，实际 Unknown", what),
            SmtResult::Error(_) => panic!("期望 {} 时 Sat，实际 Error", what),
        }
    }

    #[test]
    fn 同地址两次读模型值一致() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);

        let first = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);
        let second = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "两次读后整体应保持 Sat");
        let neq = Exp::Neq(Box::new(Exp::Var(read_sym(&first))), Box::new(Exp::Var(read_sym(&second))));
        expect_unsat(&mut solver, neq, "同地址两次读值不相等");
    }

    #[test]
    fn 写八字节后读同地址等于写数据() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);

        let data = B64::new(0x1122_3344_5566_7788, 64);
        let write_result = write_bytes(&mut memory, &mut solver, Val::Symbolic(addr), data);
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "写后读整体应保持 Sat");
        let neq = Exp::Neq(Box::new(Exp::Var(read_sym(&read_back))), Box::new(Exp::Bits64(data)));
        expect_unsat(&mut solver, neq, "写 8 字节后同地址读值不等于写数据");
    }

    #[test]
    fn 写四字节后读中间一字节等于对应字节() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        let base = test_sym(0);
        let mid = test_sym(1);
        declare_symbol(&mut solver, base, 64);
        declare_symbol(&mut solver, mid, 64);
        // mid = base + 2：指向 4 字节写数据的第 2 字节
        solver.add(Def::Assert(Exp::Eq(
            Box::new(Exp::Var(mid)),
            Box::new(Exp::Bvadd(Box::new(Exp::Var(base)), Box::new(bits64(2, 64)))),
        )));

        // 0xAABBCCDD 小端布局：base+0=DD, base+1=CC, base+2=BB, base+3=AA
        let write_result = write_bytes(&mut memory, &mut solver, Val::Symbolic(base), B64::new(0xAABBCCDD, 32));
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(mid), 1);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "部分读整体应保持 Sat");
        let neq = Exp::Neq(Box::new(Exp::Var(read_sym(&read_back))), Box::new(bits64(0xBB, 8)));
        expect_unsat(&mut solver, neq, "写 4 字节后中间 1 字节读值不等于写数据第 2 字节 0xBB");
    }

    #[test]
    fn 独占写事件按模型语义必已提交_bool钉为真() {
        // F3（campaign24，7 例 AMO 非 aqrl post==pre）：Sail 模型的 write_ram 对
        // 并发接口返回值 `Ok(_) => true`（phys_mem_interface.sail:109-115，IR
        // zwrite_ram 中 zz410 = true），独占写 Bool 被调用方丢弃、永不约束——
        // Z3 可任取 false，使数组 Ite 选旧值、终值重放按 write_success=Some(false)
        // 跳过物化。模型语义上独占写事件一旦发出即已提交（SC 失败发生在写之前，
        // 不经过本回调），注入期必须把 Bool 钉为真。
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = Val::Bits(B64::new(0x1000, 64));
        let write_result = write_bytes_exclusive(&mut memory, &mut solver, address.clone(), B64::new(0xA5, 8));
        // 调用方不追加任何方向断言：Bool 本身必须已被钉为真
        expect_unsat(
            &mut solver,
            Exp::Not(Box::new(Exp::Var(write_sym(&write_result)))),
            "独占写 Bool 必须为真（模型语义必已提交）",
        );
        let after = read_bytes(&memory, &mut solver, address, 1);
        expect_unsat(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&after))), Box::new(bits64(0xA5, 8))),
            "独占写后读值必须等于写数据",
        );
    }

    #[test]
    fn 独占写失败分支在注入后不可表达() {
        // 原"独占失败写"场景（调用方事后断言 Bool=false）在钉真后必须整体 Unsat：
        // 这不是合法路径，而是模型不变量违反，防御式地让断言方直接看到矛盾。
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = Val::Bits(B64::new(0x1000, 64));
        let write_result = write_bytes_exclusive(&mut memory, &mut solver, address, B64::new(0xA5, 8));
        solver.add(Def::Assert(Exp::Not(Box::new(Exp::Var(write_sym(&write_result))))));
        assert_eq!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat, "独占写 Bool=false 分支必须不可满足");
    }

    #[test]
    fn 普通写返回布尔假仍提交数据() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = Val::Bits(B64::new(0x1000, 64));
        let write_result = write_bytes(&mut memory, &mut solver, address.clone(), B64::new(0xA5, 8));
        solver.add(Def::Assert(Exp::Not(Box::new(Exp::Var(write_sym(&write_result))))));
        let after = read_bytes(&memory, &mut solver, address, 1);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat));
        expect_unsat(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&after))), Box::new(bits64(0xA5, 8))),
            "普通写返回Bool=false不表示写入失败",
        );
    }

    #[test]
    fn 独占符号写提交后读值与先前读取解耦() {
        // 钉真后不存在"真假两臂"：独占写无条件提交，写后读值恒等于写数据，
        // 与写前读值是否一致无关（写数据可以覆盖任意先前内容）。
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);
        let address = Val::Bits(B64::new(0x1000, 64));
        let _before = read_bytes(&memory, &mut solver, address.clone(), 1);
        let write_result = write_bytes_exclusive(&mut memory, &mut solver, address.clone(), B64::new(0xA5, 8));
        let after = read_bytes(&memory, &mut solver, address, 1);

        expect_sat_with(&mut solver, Exp::Var(write_sym(&write_result)), "独占写 Bool 恒真");
        expect_unsat(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&after))), Box::new(bits64(0xA5, 8))),
            "独占写后读值必须等于写数据",
        );
    }

    /// W9 判死区域（RED A 读侧）：符号读地址解进判死区域 → 回调追加
    /// NOT(与判死区域重叠) 约束后与钉死断言联立 Unsat，`read_symbolic` 的
    /// W7 立即检查直接 BadRead 判死，不发出 ReadMem 事件。
    #[test]
    fn 判死区域内符号读立即BadRead无事件且Unsat() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        // 模拟路径既有断言把地址钉进判死区域（如模型侧 PMA 分支的 range_subset）
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1500, 64)))));

        let result = memory.read(Val::Unit, Val::Symbolic(addr), Val::I128(8), &mut solver, false, ReadOpts::default());
        assert!(
            matches!(result, Err(isla_lib::error::ExecError::BadRead(_))),
            "判死区域内的符号读应立即 BadRead，实际 {:?}",
            result.map(|_| ())
        );
        assert!(
            !solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { .. })),
            "被判死的符号读不应发出 ReadMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat), "判死约束联立应 Unsat");
    }

    /// W9 判死区域（RED A 写侧）：与读侧一视同仁——符号写地址解进判死区域
    /// → BadWrite 判死、无事件、断言集 Unsat。
    #[test]
    fn 判死区域内符号写立即BadWrite无事件且Unsat() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1500, 64)))));

        let result = memory.write(
            Val::Unit,
            Val::Symbolic(addr),
            Val::Bits(B64::new(0xA5A5_5A5A, 32)),
            &mut solver,
            None,
            WriteOpts::default(),
        );
        assert!(
            matches!(result, Err(isla_lib::error::ExecError::BadWrite(_))),
            "判死区域内的符号写应立即 BadWrite，实际 {:?}",
            result.map(|_| ())
        );
        assert!(
            !solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { .. })),
            "被判死的符号写不应发出 WriteMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Unsat), "判死约束联立应 Unsat");
    }

    /// W9 判死区域（RED A 自由地址）：地址未被钉死时读路径保持 Sat、事件
    /// 可见；模型地址只被排除出判死区域（NOT 链），其余全域自由——包括
    /// 边界精确性：恰好在判死区域外完成的八字节读可满足，跨入一字节即死。
    #[test]
    fn 判死区域外符号读Sat事件可见且边界精确() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        let _ = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
            "判死区域外的符号读应发出 ReadMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "判死区域外读路径应保持 Sat");
        // 区域内地址不可解
        expect_unsat(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1500, 64))),
            "判死区域内的读地址",
        );
        // 边界（区域末端为半开端点）：区域 [0x1000,0x2000) 的最后一字节是
        // 0x1fff——八字节读 [0x1ff8,0x2000) 整段落入区域 → Unsat
        expect_unsat(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1ff8, 64))),
            "末八字节全部落入判死区域的读",
        );
        // 恰好从区域末端之外开始：[0x2000,0x2008) 与区域无重叠 → Sat
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x2000, 64))),
            "从判死区域末端之外开始的八字节读",
        );
        // 远离区域的位置自由可取
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x5000, 64))),
            "远离判死区域的读地址",
        );
    }

    /// W9 判死区域对取指（ifetch 读）同样生效：判死语义对一切读一视同仁，
    /// 不因 ReadOpts::ifetch 而豁免。
    #[test]
    fn 判死区域对ifetch读同样生效() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1800, 64)))));

        let result = memory.read(Val::Unit, Val::Symbolic(addr), Val::I128(4), &mut solver, false, ReadOpts::ifetch());
        assert!(
            matches!(result, Err(isla_lib::error::ExecError::BadRead(_))),
            "判死区域内的 ifetch 读应立即 BadRead，实际 {:?}",
            result.map(|_| ())
        );
        assert!(
            !solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { .. })),
            "被判死的 ifetch 读不应发出 ReadMem 事件"
        );
    }

    /// W9 判死区域（多区域并集）：两个判死区域的并集共同生效——落在任一
    /// 区域内即死，区域外可解。
    #[test]
    fn 多判死区域并集生效() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        memory.add_excluded_region(0x8000_0000..0x9000_0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        let _ = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 4);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "并集约束下应保持 Sat");
        expect_unsat(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1000, 64))),
            "第一个判死区域首地址",
        );
        expect_unsat(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x8fff_fffc, 64))),
            "第二个判死区域末地址",
        );
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x5000, 64))),
            "两个判死区域之间的地址",
        );
    }

    #[test]
    fn 未配置区域时符号地址不受限() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);

        let _ = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "未配置区域时应保持 Sat");
        let anywhere = Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x5000, 64)));
        expect_sat_with(&mut solver, anywhere, "未配置区域时任意地址 0x5000 的符号读");
    }

    /// W9 判死区域（RED B 具体地址）：具体地址读/写落在判死区域内 → 具体
    /// 地址分派直接 BadRead/BadWrite，不经 solver；跨界访问（起始在区域外、
    /// 末字节伸入区域）同样判死。
    #[test]
    fn 具体地址落在判死区域直接拒绝() {
        // 读侧：区域内具体地址
        {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::<B64>::new();
            memory.add_excluded_region(0x1000..0x2000);
            install_seq_memory(&mut memory, 64, &mut solver);

            let result = memory.read(
                Val::Unit,
                Val::Bits(B64::new(0x1500, 64)),
                Val::I128(4),
                &mut solver,
                false,
                ReadOpts::default(),
            );
            assert!(
                matches!(result, Err(isla_lib::error::ExecError::BadRead(_))),
                "判死区域内的具体地址读应直接 BadRead，实际 {:?}",
                result.map(|_| ())
            );
            assert!(
                !solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { .. })),
                "被判死的具体读不应发出 ReadMem 事件"
            );
            // 跨界：起始 0x1ffd 的 4 字节读覆盖 [0x1ffd,0x2001)，触到区域内
            // 末字节 0x1fff
            let straddle = memory.read(
                Val::Unit,
                Val::Bits(B64::new(0x1ffd, 64)),
                Val::I128(4),
                &mut solver,
                false,
                ReadOpts::default(),
            );
            assert!(
                matches!(straddle, Err(isla_lib::error::ExecError::BadRead(_))),
                "跨入判死区域的具体读应 BadRead，实际 {:?}",
                straddle.map(|_| ())
            );
            // 恰好从区域末端之外开始：[0x2000,0x2004) 与区域无重叠
            let edge = memory.read(
                Val::Unit,
                Val::Bits(B64::new(0x2000, 64)),
                Val::I128(4),
                &mut solver,
                false,
                ReadOpts::default(),
            );
            assert!(edge.is_ok(), "从判死区域末端之外开始的具体读不应被拒绝：{:?}", edge.err());
        }
        // 写侧对称
        {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::<B64>::new();
            memory.add_excluded_region(0x1000..0x2000);
            install_seq_memory(&mut memory, 64, &mut solver);

            let result = memory.write(
                Val::Unit,
                Val::Bits(B64::new(0x1500, 64)),
                Val::Bits(B64::new(0xA5A5_A5A5, 32)),
                &mut solver,
                None,
                WriteOpts::default(),
            );
            assert!(
                matches!(result, Err(isla_lib::error::ExecError::BadWrite(_))),
                "判死区域内的具体地址写应直接 BadWrite，实际 {:?}",
                result.map(|_| ())
            );
            assert!(
                !solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { .. })),
                "被判死的具体写不应发出 WriteMem 事件"
            );
        }
    }

    /// W9 判死区域与 concrete 区域并存（RED B 回归）：判死不改变 concrete
    /// 区域的具体地址命中语义——快照内容照常可读、事件照常发出。
    #[test]
    fn 判死区域不改变concrete区域具体读取() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_zero_region(0x8000_0000..0x8000_1000);
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let value = memory
            .read(
                Val::Unit,
                Val::Bits(B64::new(0x8000_0100, 64)),
                Val::I128(4),
                &mut solver,
                false,
                ReadOpts::default(),
            )
            .expect("concrete 区域内的具体读不受判死区域影响");
        assert_eq!(value, Val::Bits(B64::new(0, 32)), "零快照 concrete 区域读回应为 0");
        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 4)),
            "concrete 具体读应发出 ReadMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "concrete 具体读路径应保持 Sat");
    }

    #[test]
    fn 克隆内存保留数组模型回调() {
        let cfg = Config::new();
        let ctx = Context::new(cfg);
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        // Clone 快照（对应 exec.rs 每个 clause 克隆内存）必须保留 client_info，
        // 否则写后读的相等约束不会生成，下面的 Unsat 断言会失败。
        let mut memory_clone = memory.clone();

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);

        let data = B64::new(0xCAFEBABE, 32);
        let write_result = write_bytes(&mut memory_clone, &mut solver, Val::Symbolic(addr), data);
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory_clone, &mut solver, Val::Symbolic(addr), 4);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "克隆内存写后读应保持 Sat");
        let neq = Exp::Neq(Box::new(Exp::Var(read_sym(&read_back))), Box::new(Exp::Bits64(data)));
        expect_unsat(&mut solver, neq, "克隆内存写后读值不等于写数据");
    }

    #[test]
    fn 克隆路径的写入不污染另一条路径() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut initial = Memory::<B64>::new();
        install_seq_memory(&mut initial, 64, &mut solver);
        let mut writer = initial.clone();
        let reader = initial.clone();
        let address = Val::Bits(B64::new(0x1000, 64));

        let write_result = write_bytes(&mut writer, &mut solver, address.clone(), B64::new(0xA5, 8));
        assert_write_success(&mut solver, &write_result);
        let written = read_bytes(&writer, &mut solver, address.clone(), 1);
        let untouched = read_bytes(&reader, &mut solver, address, 1);

        expect_unsat(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&written))), Box::new(bits64(0xA5, 8))),
            "写入路径的读值",
        );
        expect_sat_with(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&untouched))), Box::new(bits64(0xA5, 8))),
            "未写入路径保留初始数组",
        );
    }

    #[test]
    fn 六十四位地址高位不与低位别名() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        install_seq_memory(&mut memory, 64, &mut solver);

        let write_result =
            write_bytes(&mut memory, &mut solver, Val::Bits(B64::new(0x1_0000_0000, 64)), B64::new(0xA5, 8));
        assert_write_success(&mut solver, &write_result);
        let low = read_bytes(&memory, &mut solver, Val::Bits(B64::new(0, 64)), 1);
        let high = read_bytes(&memory, &mut solver, Val::Bits(B64::new(0x1_0000_0000, 64)), 1);

        expect_unsat(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&high))), Box::new(bits64(0xA5, 8))),
            "高位地址写后读",
        );
        expect_sat_with(
            &mut solver,
            Exp::Neq(Box::new(Exp::Var(read_sym(&low))), Box::new(bits64(0xA5, 8))),
            "低位地址不与高位地址别名",
        );
    }

    /// W9 语义回归：symbolic 区域降级为纯声明后，concrete 区域的具体地址
    /// 写不再被"圈进 Symbolic 并集"的白名单机制拒绝（W8 定向重放档行为，
    /// 已删除）——默认全符号化下具体地址写走 write_symbolic，正常提交。
    #[test]
    fn 具体地址写concrete区域不再被白名单拒绝() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_zero_region(0..0x1000);
        memory.add_symbolic_region(0x8000..0x9000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let result = memory.write(
            Val::Unit,
            Val::Bits(B64::new(0x100, 64)),
            Val::Bits(B64::new(0xA5, 8)),
            &mut solver,
            None,
            WriteOpts::default(),
        );
        assert!(result.is_ok(), "W9 默认语义下具体地址写不应被区域白名单拒绝：{:?}", result.err());
        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 1)),
            "具体地址写应发出 WriteMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "具体地址写路径应保持 Sat");
    }

    #[test]
    fn 默认内存保留具体区域重叠写入错误() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_zero_region(0..0x1000);
        memory.add_symbolic_region(0x8000..0x9000);
        let address = test_sym(0);
        declare_symbol(&mut solver, address, 64);

        let error = memory.write(
            Val::Unit,
            Val::Symbolic(address),
            Val::Bits(B64::new(0xA5, 8)),
            &mut solver,
            None,
            WriteOpts::default(),
        );
        assert!(matches!(error, Err(isla_lib::error::ExecError::BadWrite("possible symbolic address overlap"))));
    }

    /// 数组内存模型下读地址的合法性由回调的区域 OR 链约束（`symbolic_read`），
    /// 与写侧 `constrains_symbolic_writes` 对称，未约束的符号读地址不应被
    /// `check_concrete_overlap` 以 BadRead 提前拒绝（默认配置内存只有 CLINT
    /// concrete 区域时，真实 load 路径会整体死在该预检查上）。W6 起只有
    /// concrete 区域（无 Symbolic）时区域约束整体不生成，读地址全域自由。
    #[test]
    fn 数组模型下未约束符号读地址不被具体区域预检查拒绝() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_zero_region(0x2000000..0x20c0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let address = test_sym(0);
        declare_symbol(&mut solver, address, 64);

        let value = memory
            .read(Val::Unit, Val::Symbolic(address), Val::I128(8), &mut solver, false, ReadOpts::default())
            .expect("数组模型读不应被具体区域重叠预检查拒绝");
        assert!(matches!(value, Val::Symbolic(_)), "符号读应返回符号值");

        // ReadMem 事件必须已进入 solver trace（solve-state 物化 memory-events 的来源）
        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
            "符号读后 trace 应包含 ReadMem 事件"
        );

        // 无 Symbolic 区域时不生成区域约束，地址全域自由、整体可满足
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "零配置读路径应保持 Sat");
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x5000, 64))),
            "零配置读地址可取 CLINT 外任意值",
        );
    }

    /// W6 修复（写侧空 OR 链折叠 bug）：只有 concrete 区域（默认 difftest 配置，
    /// CLINT concrete + 未声明 [[memory_regions]]）时，`ranges_for_access_checks`
    /// 的 `SmtKind::WriteData` 收集不到任何 Symbolic 区域，旧实现的 OR 链折叠成
    /// `Bool(false)` 直接 Assert，零配置写路径被整体判死。空集的正确语义是
    /// **不加约束**（地址全域自由），不是"禁止一切写"。
    #[test]
    fn 零符号区域时符号写不被空or链判死() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        // 默认 difftest 配置构建出的内存：只有 CLINT concrete 区域
        memory.add_zero_region(0x2000000..0x20c0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let address = test_sym(0);
        declare_symbol(&mut solver, address, 64);

        let write_result =
            write_bytes(&mut memory, &mut solver, Val::Symbolic(address), B64::new(0x1122_3344_5566_7788, 64));
        assert_write_success(&mut solver, &write_result);

        assert!(
            matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat),
            "只有 concrete 区域时符号写不应被空 OR 链折叠成 false 判死"
        );
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0x5000, 64))),
            "零配置写地址可取任意值",
        );
        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 8)),
            "符号写后 trace 应包含 WriteMem 事件"
        );
    }

    /// W6 零配置 = 彻底全符号化（追加组合测试，CLINT 保持默认开启）：不配任何
    /// `[[memory_regions]]` 时，数组模型下符号读和符号写都 SAT、事件可见、地址
    /// 模型值不被圈进任何区域（CLINT 内外、0 与接近 2^64 的位置都可满足）。
    /// 内置默认 CLINT 只参与具体地址分派，不参与约束生成。
    #[test]
    fn 零配置全符号化读写不受区域约束且事件可见() {
        use crate::isarch::memory_builder::MemoryBuilder;
        use crate::isarch::target::RV64;

        let rv64: RV64<B64> = RV64::default();
        let mut memory = MemoryBuilder::<B64>::new(&rv64).build().unwrap();
        // 零配置默认内存：只有内置 CLINT concrete 区域，没有任何 Symbolic 区域
        assert!(
            !memory.regions().iter().any(|r| matches!(r, Region::Symbolic(_) | Region::SymbolicCode(_))),
            "零配置不应有任何符号区域"
        );
        assert_eq!(memory.regions().len(), 1, "默认构建只装内置 CLINT concrete 区域");

        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        install_seq_memory(&mut memory, 64, &mut solver);

        let address = test_sym(0);
        declare_symbol(&mut solver, address, 64);

        let write_result =
            write_bytes(&mut memory, &mut solver, Val::Symbolic(address), B64::new(0xA5A5_5A5A_5A5A_A5A5, 64));
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(address), 8);

        let events = solver.trace().to_vec();
        assert!(
            events.iter().any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 8)),
            "符号写后 trace 应包含 WriteMem 事件"
        );
        assert!(
            events.iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
            "符号读后 trace 应包含 ReadMem 事件"
        );

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "零配置下符号读写路径应保持 Sat");
        // 写后同址读值仍等于写数据（数组一致性语义与区域无关）
        expect_unsat(
            &mut solver,
            Exp::Neq(
                Box::new(Exp::Var(read_sym(&read_back))),
                Box::new(Exp::Bits64(B64::new(0xA5A5_5A5A_5A5A_A5A5, 64))),
            ),
            "零配置写后同址读值",
        );
        // 地址不被圈进任何区域：0、高位都应可满足
        expect_sat_with(&mut solver, Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0, 64))), "地址取 0");
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(address)), Box::new(bits64(0xffff_ffff_ffff_fff8, 64))),
            "地址取接近 2^64 的高位",
        );
    }

    /// W7 机制回归（W9 判死语义）：真实访存路径先经模型侧 `matching_pma`/PMP
    /// 检查，range_subset 的析取分支会把读地址断言进对应 PMA 区域。判死区域
    /// 与 PMA 钉死区间重叠时，回调追加的 NOT(判死并集) 约束与路径既有断言
    /// 联立 Unsat——必须在读入口立即 BadRead 判死（W7 修复），不能静默 Ok
    /// 后把 Unsat 留到路径终值查询（那时已烧掉一次模型查询）。构造方式与
    /// W6/W7 证据一致：ROM 边界断言 addr ∈ [0x1000,0x2000) + 判死同区间。
    #[test]
    fn 判死约束与既有路径断言矛盾时符号读立即判死() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        // 模拟模型侧 matching_pma 选中 ROM 分支的 range_subset 首析取断言：
        // addr - 0x1000 <=u 0xfff，即 addr ∈ [0x1000, 0x1fff]，整体落入判死区域
        solver.add(Def::Assert(Exp::Bvule(
            Box::new(Exp::Bvadd(Box::new(Exp::Var(addr)), Box::new(bits64(0u64.wrapping_sub(0x1000), 64)))),
            Box::new(bits64(0xfff, 64)),
        )));

        let result = memory.read(Val::Unit, Val::Symbolic(addr), Val::I128(8), &mut solver, false, ReadOpts::default());
        match result {
            Err(isla_lib::error::ExecError::BadRead(_)) => (),
            other => panic!("判死约束与 ROM 断言矛盾时符号读应立即 BadRead 判死，实际 {:?}", other),
        }
        // 事件不应进入 trace：死路径不产出访存事件
        assert!(
            !solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { .. })),
            "被判死的符号读不应发出 ReadMem 事件"
        );
    }

    /// 写侧与读侧对称：判死 NOT 约束与既有路径断言矛盾时立即 BadWrite 判死，
    /// 不把 Unsat 留到路径终值查询。
    #[test]
    fn 判死约束与既有路径断言矛盾时符号写立即判死() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_excluded_region(0x1000..0x2000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        solver.add(Def::Assert(Exp::Bvule(
            Box::new(Exp::Bvadd(Box::new(Exp::Var(addr)), Box::new(bits64(0u64.wrapping_sub(0x1000), 64)))),
            Box::new(bits64(0xfff, 64)),
        )));

        let result = memory.write(
            Val::Unit,
            Val::Symbolic(addr),
            Val::Bits(B64::new(0xA5A5_5A5A_5A5A_A5A5, 64)),
            &mut solver,
            None,
            WriteOpts::default(),
        );
        match result {
            Err(isla_lib::error::ExecError::BadWrite(_)) => (),
            other => panic!("判死约束与 ROM 断言矛盾时符号写应立即 BadWrite 判死，实际 {:?}", other),
        }
        assert!(
            !solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { .. })),
            "被判死的符号写不应发出 WriteMem 事件"
        );
    }

    /// W9 默认全符号化：`[[memory_regions]]` 的 symbolic 声明只是"这一段
    /// 明确是 RAM（内容未知）"的**纯声明**，**不是**"地址必须圈进这一段"
    /// （W9 已删除圈地址的白名单机制）。Isla 内存层只管内容：符号读地址全域
    /// 自由，读值来自字节数组，访存可访问性与 trap 完全交给模型自身的
    /// PMA/PMP。锁定：配置 sym_ram 后，地址仍可解在 sym_ram 之外、但属于
    /// 模型 PMA RAM（IR 固化 [0x80000000,0x100000000)）的区间（如
    /// 0x91000000），整体 SAT 且 ReadMem 事件可见；对称地，落在模型 PMA
    /// 其他区域（如 ROM）的地址也不被内存层预先抹掉——fault 路径是否存在
    /// 由模型 PMA 分叉决定（端到端验证）。
    #[test]
    fn 默认分层下配置sym_ram符号读不被区域圈定() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_symbolic_region(0x8000_0000..0x9000_0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        let _ = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
            "默认分层下符号读应发出 ReadMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "默认分层下读路径应保持 Sat");
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x9100_0000, 64))),
            "sym_ram 外、模型 PMA RAM 内的符号读地址",
        );
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x1800, 64))),
            "ROM 区间的符号读地址（可访问性由模型 PMA 决定，不由内存层抹掉）",
        );
    }

    /// W9 默认全符号化（写侧）：配置 sym_ram（纯声明）后符号写地址同样不被
    /// 区域圈定——数组内容层对全域地址提供写后读一致性，可访问性/trap 由
    /// 模型 PMA/PMP 决定。锁定：sym_ram 之外、模型 PMA RAM 之内的写地址
    /// 可解且 WriteMem 事件可见，写后同址读值等于写数据（内容层语义与区域
    /// 无关）。
    #[test]
    fn 默认分层下配置sym_ram符号写不被区域圈定() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_symbolic_region(0x8000_0000..0x9000_0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        let write_result =
            write_bytes(&mut memory, &mut solver, Val::Symbolic(addr), B64::new(0x1122_3344_5566_7788, 64));
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(
            solver.trace().to_vec().iter().any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 8)),
            "默认分层下符号写应发出 WriteMem 事件"
        );
        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "默认分层下写路径应保持 Sat");
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x9100_0000, 64))),
            "sym_ram 外、模型 PMA RAM 内的符号写地址",
        );
        // 内容层一致性在 sym_ram 外的地址上同样成立
        expect_unsat(
            &mut solver,
            Exp::Neq(
                Box::new(Exp::Var(read_sym(&read_back))),
                Box::new(Exp::Bits64(B64::new(0x1122_3344_5566_7788, 64))),
            ),
            "默认分层下写后同址读值",
        );
    }

    /// 默认全符号化与 W7 立即判死机制的分界（RED C 核心守卫）：只有配置了
    /// 判死区域（excluded）才生成 NOT 约束并触发"约束矛盾立即判死"；零判死
    /// 区域下即使路径断言已把地址钉在与 sym_ram 不相交的模型 PMA 区域（如
    /// ROM [0x1000,0x2000)，见上方 W7 测试的构造），读写也只是正常从数组取
    /// 内容，**不被 BadRead/BadWrite 判死**、事件照常发出——成功/fault 两侧
    /// 路径的取舍交给模型 PMA 分叉，内存层不抹掉任何一侧。symbolic 声明
    /// 不产生任何约束（W9 纯声明语义）。
    #[test]
    fn 默认分层下与PMA断言矛盾的读写不被判死() {
        // 读侧：ROM 钉死断言 + sym_ram 纯声明区域，零判死区域应正常返回符号值
        {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::<B64>::new();
            memory.add_symbolic_region(0x8000_0000..0x9000_0000);
            install_seq_memory(&mut memory, 64, &mut solver);
            let addr = test_sym(0);
            declare_symbol(&mut solver, addr, 64);
            solver.add(Def::Assert(Exp::Bvule(
                Box::new(Exp::Bvadd(Box::new(Exp::Var(addr)), Box::new(bits64(0u64.wrapping_sub(0x1000), 64)))),
                Box::new(bits64(0x1000, 64)),
            )));

            let value = memory
                .read(Val::Unit, Val::Symbolic(addr), Val::I128(8), &mut solver, false, ReadOpts::default())
                .expect("默认分层下与 PMA 断言'矛盾'的符号读不应被判死");
            assert!(matches!(value, Val::Symbolic(_)), "符号读应返回符号值");
            assert!(
                solver
                    .trace()
                    .to_vec()
                    .iter()
                    .any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
                "默认分层下符号读应发出 ReadMem 事件"
            );
            assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "ROM 钉死地址的读应保持 Sat");
        }
        // 写侧对称
        {
            let ctx = Context::new(Config::new());
            let mut solver = Solver::<B64>::new(&ctx);
            let mut memory = Memory::<B64>::new();
            memory.add_symbolic_region(0x8000_0000..0x9000_0000);
            install_seq_memory(&mut memory, 64, &mut solver);
            let addr = test_sym(0);
            declare_symbol(&mut solver, addr, 64);
            solver.add(Def::Assert(Exp::Bvule(
                Box::new(Exp::Bvadd(Box::new(Exp::Var(addr)), Box::new(bits64(0u64.wrapping_sub(0x1000), 64)))),
                Box::new(bits64(0x1000, 64)),
            )));

            let result = memory.write(
                Val::Unit,
                Val::Symbolic(addr),
                Val::Bits(B64::new(0xA5A5_5A5A_5A5A_A5A5, 64)),
                &mut solver,
                None,
                WriteOpts::default(),
            );
            assert!(result.is_ok(), "默认分层下与 PMA 断言'矛盾'的符号写不应被判死：{:?}", result.err());
            assert!(
                solver
                    .trace()
                    .to_vec()
                    .iter()
                    .any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 8)),
                "默认分层下符号写应发出 WriteMem 事件"
            );
            assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "ROM 钉死地址的写应保持 Sat");
        }
    }

    /// W9 判死与 symbolic 声明并存：sym_ram（纯声明，无约束）+ 判死 MMIO 段
    /// 同时配置时，只有判死区域生效——地址可解在 sym_ram 内、也可解在
    /// sym_ram 外的任意非判死位置（symbolic 声明不圈地址），落进判死段才死。
    #[test]
    fn 判死与symbolic声明并存时仅判死生效() {
        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_symbolic_region(0x8000_0000..0x9000_0000);
        memory.add_excluded_region(0x0200_0000..0x0400_0000);
        install_seq_memory(&mut memory, 64, &mut solver);

        let addr = test_sym(0);
        declare_symbol(&mut solver, addr, 64);
        let write_result =
            write_bytes(&mut memory, &mut solver, Val::Symbolic(addr), B64::new(0x1122_3344_5566_7788, 64));
        assert_write_success(&mut solver, &write_result);
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(addr), 8);

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "判死外的读写路径应保持 Sat");
        // sym_ram 内可解（symbolic 声明仍然合法目标）
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x8500_0000, 64))),
            "sym_ram 内的读写地址",
        );
        // sym_ram 外、判死段外也可解（symbolic 声明不圈地址）
        expect_sat_with(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x9100_0000, 64))),
            "sym_ram 外、判死段外的读写地址",
        );
        // 判死段内不可解
        expect_unsat(
            &mut solver,
            Exp::Eq(Box::new(Exp::Var(addr)), Box::new(bits64(0x0300_0000, 64))),
            "判死 MMIO 段内的读写地址",
        );
        // 内容层一致性在判死语义之外照常成立
        expect_unsat(
            &mut solver,
            Exp::Neq(
                Box::new(Exp::Var(read_sym(&read_back))),
                Box::new(Exp::Bits64(B64::new(0x1122_3344_5566_7788, 64))),
            ),
            "写后同址读值",
        );
    }

    /// solve-state 装配（`ensure_solve_state_memory` 开关打开，即 W5 语义）+ 数组
    /// 内存的组合行为：默认配置内存（仅 CLINT concrete 区域）补默认符号 RAM 后，
    /// 符号读写被约束进 sym_ram、访存事件可物化且路径可满足。W6 起该兜底由
    /// `ISLA_RISCV_DEFAULT_SYM_RAM=1` 显式开启，零配置不再隐式补区域。
    #[test]
    fn 默认配置内存经装配后符号读写可满足且事件可见() {
        use crate::isarch::memory_builder::ensure_solve_state_memory;

        let ctx = Context::new(Config::new());
        let mut solver = Solver::<B64>::new(&ctx);
        let mut memory = Memory::<B64>::new();
        memory.add_zero_region(0x2000000..0x20c0000);
        let mut memory = ensure_solve_state_memory(memory, true);
        install_seq_memory(&mut memory, 64, &mut solver);

        let address = test_sym(0);
        declare_symbol(&mut solver, address, 64);

        write_bytes(&mut memory, &mut solver, Val::Symbolic(address), B64::new(0x1122_3344_5566_7788, 64));
        let read_back = read_bytes(&memory, &mut solver, Val::Symbolic(address), 8);

        let events = solver.trace().to_vec();
        assert!(
            events.iter().any(|event| matches!(event, Event::WriteMem { bytes, .. } if *bytes == 8)),
            "符号写后 trace 应包含 WriteMem 事件"
        );
        assert!(
            events.iter().any(|event| matches!(event, Event::ReadMem { bytes, .. } if *bytes == 8)),
            "符号读后 trace 应包含 ReadMem 事件"
        );

        assert!(matches!(solver.check_sat(SourceLoc::unknown()), SmtResult::Sat), "装配后读写路径应保持 Sat");
        // 写后同址读值应等于写数据（数组模型的一致性语义）
        let neq = Exp::Neq(
            Box::new(Exp::Var(read_sym(&read_back))),
            Box::new(Exp::Bits64(B64::new(0x1122_3344_5566_7788, 64))),
        );
        expect_unsat(&mut solver, neq, "写后同址读值");
    }
}
