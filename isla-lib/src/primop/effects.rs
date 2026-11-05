//! 原语副作用的唯一分类表。名字须逐项列出，禁止按前缀或默认类别放行。
//! 注册表保持现有 API，完整性由测试遍历检查（包括浮点、内存扩展和加载期重写）。

use super::{binary_primops, unary_primops, variadic_primops, Binary, Reset, Unary, Variadic};
use crate::bitvector::BV;

/// 原语的可观察副作用；同一原语有多种作用时选择更保守的类别。
///
/// `Pure` 只依赖输入。符号值的类型/宽度、路径条件查询，以及为返回值生成 SMT
/// 定义或仅约束新鲜辅助变量的等式，属于输入的符号求值，不算外部状态访问。
/// 对既有输入追加限制、生成独立的不确定选择、写事件和 IO 则不能归纯。
///
/// `zeros`、`ones`、`vector_subrange` 归 `Pure`：符号长度返回 `SymbolicLength`，
/// 由执行器重试路径分叉，C1 推演模式的统一“分支决策口”负责拦截。
/// 同样的操作数重试（含 `RetryCondition`、`IntegerConversion`）不另归 `MayFork`。
/// 当前原语没有内部直接分叉或建检查点的实现，`MayFork` 的条目数为 0。
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Effect {
    /// 只读输入，不访问寄存器、内存、配置等外部状态，也不写外部状态。
    Pure,
    /// 没有可执行实现；静态保留未知等级，推演到达时报错并回滚。
    Unknown,
    /// 读取寄存器、内存、配置、周期数等外部状态。
    ReadsState,
    /// 读取内存并发布 ReadMem；与普通状态读分开，推演还需检查设备区域。
    /// 注意（ATTENTION）：合并路径的内存读取为并集语义；需要精确内存读序列时不可信。
    /// 仅适用于本项目可审计的 RAM / 顺序数组内存回调；约束必须经 solver 带条件提交。
    ReadsMemory,
    /// 写寄存器、内存、约束、事件、IO，或无法证明安全的不透明实现。
    WritesState,
    /// 仅用于原语内部直接分叉/建检查点，且不经过执行器操作数重试路径的实现。
    MayFork,
}

/// 按注册名查询；未知名字返回 `None`，调用方必须拒绝执行或明确处理缺失分类。
/// 配置条目须按解析值使用 [`const_primop_effect`]；任意动态闭包使用 [`reset_effect`]。
pub fn effect(name: &str) -> Option<Effect> {
    match name {
        // 整数、位向量、字符串、列表和向量：只计算实参；isla_read_vreg 也从实参取寄存器值。
        "%i64->%i"
        | "%i->%i64"
        | "%string->%i"
        | "bit_to_bool"
        | "isla_bool_to_bit"
        | "not"
        | "neg_int"
        | "abs_int"
        | "pow2"
        | "not_bits"
        | "length"
        | "zeros"
        | "ones"
        | "sail_unsigned"
        | "sail_signed"
        | "count_leading_zeros"
        | "count_trailing_zeros"
        | "isla_count_ones"
        | "isla_cpop"
        | "isla_cpopw"
        | "isla_brev8"
        | "isla_rev8"
        | "isla_vector_rev8"
        | "undefined_unit"
        | "undefined_string"
        | "one_if"
        | "zero_if"
        | "hex_str"
        | "dec_str"
        | "string_length"
        | "string_of_bits"
        | "decimal_string_of_bits"
        | "string_of_int"
        | "monomorphize"
        | "and_bool"
        | "strict_and_bool"
        | "or_bool"
        | "strict_or_bool"
        | "eq_int"
        | "eq_bool"
        | "lteq"
        | "gteq"
        | "lt"
        | "gt"
        | "add_int"
        | "sub_int"
        | "sub_nat"
        | "mult_int"
        | "tdiv_int"
        | "tmod_int"
        | "ediv_int"
        | "emod_int"
        | "pow_int"
        | "shl_int"
        | "shr_int"
        | "shl_mach_int"
        | "shr_mach_int"
        | "max_int"
        | "min_int"
        | "eq_bit"
        | "eq_bits"
        | "neq_bits"
        | "xor_bits"
        | "or_bits"
        | "and_bits"
        | "add_bits"
        | "sub_bits"
        | "add_bits_int"
        | "sub_bits_int"
        | "align_bits"
        | "zero_extend"
        | "sign_extend"
        | "sail_truncate"
        | "sail_truncateLSB"
        | "replicate_bits"
        | "shiftr"
        | "shiftl"
        | "arith_shiftr"
        | "shift_bits_right"
        | "shift_bits_left"
        | "append"
        | "append_64"
        | "vector_access"
        | "eq_anything"
        | "eq_string"
        | "concat_str"
        | "string_startswith"
        | "string_drop"
        | "string_take"
        | "cons"
        | "undefined_vector"
        | "vector_init"
        | "carryless_mul"
        | "isla_carryless_mul"
        | "isla_carryless_mulr"
        | "isla_clmul"
        | "isla_clmulh"
        | "isla_clmulr"
        | "isla_xperm4"
        | "isla_xperm8"
        | "lt_bits_u"
        | "lteq_bits_u"
        | "gt_bits_u"
        | "gteq_bits_u"
        | "lt_bits_s"
        | "lteq_bits_s"
        | "gt_bits_s"
        | "gteq_bits_s"
        | "slice"
        | "vector_subrange"
        | "vector_update_subrange"
        | "bitvector_update"
        | "set_slice"
        | "get_slice_int"
        | "set_slice_int"
        | "ite"
        | "isla_read_vreg"
        | "isla_init_mask"
        | "isla_select_int"
        | "isla_vector_access_or_default"
        | "isla_vector_select"
        | "isla_mux2"
        | "isla_masktypei_result"
        | "isla_masktypev_result"
        | "isla_pack_vreg" => Some(Effect::Pure),
        // 浮点运算、舍入模式和常量：只生成返回值的 SMT 定义，不读硬件浮点状态。
        "round_nearest_ties_to_even"
        | "round_nearest_ties_to_away"
        | "round_toward_positive"
        | "round_toward_negative"
        | "round_toward_zero"
        | "fp16_nan"
        | "fp32_nan"
        | "fp64_nan"
        | "fp128_nan"
        | "fp16_inf"
        | "fp32_inf"
        | "fp64_inf"
        | "fp128_inf"
        | "fp16_negative_inf"
        | "fp32_negative_inf"
        | "fp64_negative_inf"
        | "fp128_negative_inf"
        | "fp16_zero"
        | "fp32_zero"
        | "fp64_zero"
        | "fp128_zero"
        | "fp16_negative_zero"
        | "fp32_negative_zero"
        | "fp64_negative_zero"
        | "fp128_negative_zero"
        | "fp_abs"
        | "fp_neg"
        | "fp_is_normal"
        | "fp_is_subnormal"
        | "fp_is_zero"
        | "fp_is_infinite"
        | "fp_is_nan"
        | "fp_is_negative"
        | "fp_is_positive"
        | "fp16_from_ieee"
        | "fp32_from_ieee"
        | "fp64_from_ieee"
        | "fp128_from_ieee"
        | "fp_sqrt"
        | "fp_round_to_integral"
        | "fp16_convert"
        | "fp32_convert"
        | "fp64_convert"
        | "fp128_convert"
        | "fp16_from_signed"
        | "fp32_from_signed"
        | "fp64_from_signed"
        | "fp128_from_signed"
        | "fp16_from_unsigned"
        | "fp32_from_unsigned"
        | "fp64_from_unsigned"
        | "fp128_from_unsigned"
        | "fp_to_signed16"
        | "fp_to_signed32"
        | "fp_to_signed64"
        | "fp_to_signed128"
        | "fp_rem"
        | "fp_min"
        | "fp_max"
        | "fp_lteq"
        | "fp_lt"
        | "fp_gteq"
        | "fp_gt"
        | "fp_eq"
        | "fp_add"
        | "fp_sub"
        | "fp_mul"
        | "fp_div"
        | "fp_fma" => Some(Effect::Pure),
        // 直接读取求解器周期数或 frame 的 ELF 配置。
        "get_cycle_count" | "elf_entry" => Some(Effect::ReadsState),
        // 当前是常量/错误桩；保守保留配置、睡眠、标签和读失败的状态访问契约。
        "sail_get_verbosity" | "sleeping" | "read_tag_bool" | "bad_read" => Some(Effect::ReadsState),
        // assume/乐观断言修改路径条件；推演按条件提交。悲观断言仅放行具体布尔参数。
        "assume" | "optimistic_assert" | "pessimistic_assert" => Some(Effect::WritesState),
        // 递增周期数或发布迹事件。
        "cycle_count"
        | "mark_register"
        | "mark_register_pair"
        | "platform_branch_announce"
        | "branch_announce"
        | "address_announce" => Some(Effect::WritesState),
        // 新鲜的未定义值/选择不由输入决定；nat/range 还追加范围约束，保守拒绝。
        "undefined_bitvector"
        | "undefined_bit"
        | "undefined_bool"
        | "undefined_int"
        | "undefined_nat"
        | "undefined_range"
        | "internal_pick"
        | "fp128_undefined"
        | "fp16_undefined"
        | "fp32_undefined"
        | "fp64_undefined" => Some(Effect::WritesState),
        // 这两个向量辅助原语会直接对既有实参加范围断言，可能删除路径。
        "isla_fixed_rounding_incr" | "isla_mask_from_low_bits" => Some(Effect::WritesState),
        // 非法索引类型分支会 eprintln 输出；有效分支仅更新返回的向量，仍按 IO 保守分类。
        "vector_update" => Some(Effect::WritesState),
        // RAM 读取在推演中按并集发布；设备区域在运行时预检拒绝，写和 IO 仍拒绝。
        "platform_read_mem"
        | "platform_read_mem_ifetch"
        | "platform_read_mem_exclusive"
        | "platform_read_memt"
        | "read_mem"
        | "read_mem_ifetch"
        | "read_mem_exclusive" => Some(Effect::ReadsMemory),
        // 写内存/标签或同步寄存器。
        "platform_write_mem"
        | "platform_write_mem_exclusive"
        | "platform_write_memt"
        | "platform_write_tag"
        | "write_mem"
        | "write_mem_exclusive"
        | "platform_synchronize_registers"
        | "synchronize_registers" => Some(Effect::WritesState),
        // 当前部分 IO、睡眠、屏障和标签写是空桩；保守保留副作用契约，避免推演将其吞掉。
        "sail_putchar" | "print" | "prerr" | "print_endline" | "prerr_endline" | "print_string" | "prerr_string"
        | "print_int" | "prerr_int" | "print_bits" | "prerr_bits" | "sleep_request" | "wakeup_request"
        | "platform_barrier" | "write_tag_bool" | "bad_write" => Some(Effect::WritesState),
        // 实数原语全部返回 Unimplemented；没有可审计的成功实现，保守拒绝（包含 print_real）。
        "%string->%real" | "neg_real" | "mult_real" | "sub_real" | "add_real" | "div_real" | "sqrt_real"
        | "abs_real" | "round_down" | "round_up" | "to_real" | "eq_real" | "lt_real" | "gt_real" | "lteq_real"
        | "gteq_real" | "real_power" | "print_real" | "prerr_real" | "undefined_real" => Some(Effect::WritesState),
        _ => None,
    }
}

// 三种函数指针接口复用同一分类表。优化器可能合并契约不同的相同函数体，
// 故同地址取 Pure < Unknown < ReadsState < ReadsMemory < WritesState < MayFork 的最大值，与遍历顺序无关。
macro_rules! pointer_effect {
    ($query:ident, $kind:ident, $registry:ident) => {
        /// 按实现指针查询副作用；未注册的指针返回 `None`。
        pub fn $query<B: BV>(f: $kind<B>) -> Option<Effect> {
            $registry::<B>()
                .into_iter()
                .filter_map(|(name, implementation)| {
                    std::ptr::fn_addr_eq(implementation, f)
                        .then(|| effect(&name).expect("已注册的原语必须有副作用分类"))
                })
                .max()
        }
    };
}

pointer_effect!(unary_effect, Unary, unary_primops);
fn binary_effect_registry<B: BV>() -> impl Iterator<Item = (String, Binary<B>)> {
    binary_primops::<B>().into_iter().chain(crate::ir::load_time_binary_primops::<B>().into_iter().map(
        |(_, name, implementation)| {
            effect(name).expect("加载期直接重写必须有副作用分类");
            (name.into(), implementation)
        },
    ))
}

pointer_effect!(binary_effect, Binary, binary_effect_registry);
pointer_effect!(variadic_effect, Variadic, variadic_primops);

/// 配置值已经初始化时，调用只复制固定值；Uninit 每次生成独立符号，必须保守拒绝。
pub fn const_primop_effect<B>(value: &crate::ir::URVal<B>) -> Effect {
    match value {
        crate::ir::URVal::Init(_) => Effect::Pure,
        crate::ir::URVal::Uninit(_) => Effect::WritesState,
    }
}

/// Reset 是配置注入的任意闭包，可读内存并通过 solver 写事件/约束，甚至捕获
/// 可变外部状态。当前类型未提供更细的契约，统一保守归 WritesState，不能只按
/// 名字或只读的 Memory 参数推断为纯。固定配置值另由 [`const_primop_effect`] 分类。
pub fn reset_effect<B>(reset: &Reset<B>) -> Effect {
    let _ = reset;
    Effect::WritesState
}

#[cfg(test)]
mod collision_tests {
    use super::*;
    use crate::bitvector::b64::B64;

    fn collision_registry<B: BV>() -> std::collections::HashMap<String, Unary<B>> {
        let implementation = unary_primops::<B>()["undefined_unit"];
        ["undefined_unit", "get_cycle_count", "print"].into_iter().map(|name| (name.into(), implementation)).collect()
    }
    pointer_effect!(collision_effect, Unary, collision_registry);

    #[test]
    fn primop_effect_address_collision_is_conservative() {
        let implementation = unary_primops::<B64>()["undefined_unit"];
        // 每次重建 HashMap 的随机遍历顺序不得影响同地址冲突的结果。
        for iteration in 0..64 {
            assert_eq!(collision_effect(implementation), Some(Effect::WritesState), "第 {iteration} 次地址冲突分类");
        }
    }
}
