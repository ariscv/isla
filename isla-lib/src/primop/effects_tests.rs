//! 副作用分类的契约测试；预期名单独立于分类表。
use super::*;
use crate::bitvector::b129::B129;

#[test]
fn effect_classification_covers_all_registries() {
    let primops = Primops::<B129>::default();
    for name in primops.unary.keys().chain(primops.binary.keys()).chain(primops.variadic.keys()) {
        assert!(effect(name).is_some(), "原语缺少副作用分类：{name}");
    }
    // Reset 名字由配置任意注入，必须按闭包类型分类，不能靠默认空表通过。
    let mut primops = primops;
    primops.consts.insert(
        "配置注入的复位闭包".into(),
        (
            std::sync::Arc::new(|memory, types, solver| {
                let _ = (memory, types, solver);
                Ok(Val::Unit)
            }),
            Effect::WritesState,
        ),
    );
    for (reset, declared) in primops.consts.values() {
        assert_eq!(reset_effect(reset), Effect::WritesState);
        assert_eq!(*declared, Effect::WritesState);
    }
    assert_eq!(effect("不存在的原语"), None);
}

#[test]
fn effect_representatives_and_conservative_cases() {
    for (name, expected) in [
        ("zeros", Effect::Pure),
        ("ones", Effect::Pure),
        ("vector_subrange", Effect::Pure),
        ("isla_read_vreg", Effect::Pure), // 寄存器值来自实参，不访问 frame。
        ("get_cycle_count", Effect::ReadsState),
        ("elf_entry", Effect::ReadsState),
        ("assume", Effect::WritesState),
        ("mark_register", Effect::WritesState),
        ("platform_write_mem", Effect::WritesState),
        ("read_mem", Effect::ReadsMemory),
        ("undefined_nat", Effect::WritesState),
        ("internal_pick", Effect::WritesState),
        ("isla_fixed_rounding_incr", Effect::WritesState),
        ("isla_mask_from_low_bits", Effect::WritesState),
        ("print_real", Effect::WritesState),
    ] {
        assert_eq!(effect(name), Some(expected), "分类错误：{name}");
    }
    let names = unary_primops::<B129>()
        .into_keys()
        .chain(binary_primops::<B129>().into_keys())
        .chain(variadic_primops::<B129>().into_keys());
    assert_eq!(names.filter(|name| effect(name) == Some(Effect::MayFork)).count(), 0);
}

#[test]
fn effect_pointer_queries_and_purity_agree() {
    for (name, f) in unary_primops::<B129>() {
        let by_pointer = unary_effect(f).expect("已注册地址必须有分类");
        assert!(by_pointer >= effect(&name).unwrap(), "一元地址分类必须保守：{name}");
        assert_eq!(is_pure_unary(f), by_pointer == Effect::Pure, "一元纯度不一致：{name}");
    }
    for (name, f) in binary_primops::<B129>() {
        let by_pointer = binary_effect(f).expect("已注册地址必须有分类");
        assert!(by_pointer >= effect(&name).unwrap(), "二元地址分类必须保守：{name}");
        assert_eq!(is_pure_binary(f), by_pointer == Effect::Pure, "二元纯度不一致：{name}");
    }
    for (name, f) in variadic_primops::<B129>() {
        assert!(variadic_effect(f).unwrap() >= effect(&name).unwrap(), "多元地址分类必须保守：{name}");
    }
}

#[test]
fn effect_newly_pure_primops_have_positive_cases() {
    let primops = unary_primops::<B129>();
    for name in [
        "%string->%i",
        "zeros",
        "ones",
        "sail_unsigned",
        "sail_signed",
        "isla_count_ones",
        "isla_cpop",
        "isla_cpopw",
        "isla_brev8",
        "isla_rev8",
        "isla_vector_rev8",
        "undefined_unit",
        "undefined_string",
        "one_if",
        "zero_if",
        "hex_str",
        "dec_str",
        "string_length",
        "string_of_bits",
        "decimal_string_of_bits",
        "string_of_int",
        "monomorphize",
        "round_nearest_ties_to_even",
        "round_nearest_ties_to_away",
        "round_toward_positive",
        "round_toward_negative",
        "round_toward_zero",
        "fp16_nan",
        "fp32_nan",
        "fp64_nan",
        "fp128_nan",
        "fp16_inf",
        "fp32_inf",
        "fp64_inf",
        "fp128_inf",
        "fp16_negative_inf",
        "fp32_negative_inf",
        "fp64_negative_inf",
        "fp128_negative_inf",
        "fp16_zero",
        "fp32_zero",
        "fp64_zero",
        "fp128_zero",
        "fp16_negative_zero",
        "fp32_negative_zero",
        "fp64_negative_zero",
        "fp128_negative_zero",
        "fp_abs",
        "fp_neg",
        "fp_is_normal",
        "fp_is_subnormal",
        "fp_is_zero",
        "fp_is_infinite",
        "fp_is_nan",
        "fp_is_negative",
        "fp_is_positive",
        "fp16_from_ieee",
        "fp32_from_ieee",
        "fp64_from_ieee",
        "fp128_from_ieee",
    ] {
        assert_eq!(effect(name), Some(Effect::Pure), "新增纯原语：{name}");
        // 优化构建允许相同函数体被合并；按名字仍为纯，地址查询必须保守。
        assert_eq!(is_pure_unary(primops[name]), unary_effect(primops[name]) == Some(Effect::Pure));
    }
    let primops = binary_primops::<B129>();
    for name in [
        "strict_and_bool",
        "strict_or_bool",
        "shl_mach_int",
        "shr_mach_int",
        "max_int",
        "min_int",
        "align_bits",
        "sail_truncateLSB",
        "shift_bits_right",
        "shift_bits_left",
        "append_64",
        "vector_access",
        "eq_string",
        "concat_str",
        "string_startswith",
        "string_drop",
        "string_take",
        "cons",
        "undefined_vector",
        "vector_init",
        "carryless_mul",
        "isla_carryless_mul",
        "isla_carryless_mulr",
        "isla_clmul",
        "isla_clmulh",
        "isla_clmulr",
        "isla_xperm4",
        "isla_xperm8",
        "fp_sqrt",
        "fp_round_to_integral",
        "fp16_convert",
        "fp32_convert",
        "fp64_convert",
        "fp128_convert",
        "fp16_from_signed",
        "fp32_from_signed",
        "fp64_from_signed",
        "fp128_from_signed",
        "fp16_from_unsigned",
        "fp32_from_unsigned",
        "fp64_from_unsigned",
        "fp128_from_unsigned",
        "fp_to_signed16",
        "fp_to_signed32",
        "fp_to_signed64",
        "fp_to_signed128",
        "fp_rem",
        "fp_min",
        "fp_max",
        "fp_lteq",
        "fp_lt",
        "fp_gteq",
        "fp_gt",
        "fp_eq",
        "lt_bits_u",
        "lteq_bits_u",
        "gt_bits_u",
        "gteq_bits_u",
        "lt_bits_s",
        "lteq_bits_s",
        "gt_bits_s",
        "gteq_bits_s",
    ] {
        assert_eq!(effect(name), Some(Effect::Pure), "新增纯原语：{name}");
        assert_eq!(is_pure_binary(primops[name]), binary_effect(primops[name]) == Some(Effect::Pure));
    }
    let primops = variadic_primops::<B129>();
    for name in [
        "slice",
        "vector_subrange",
        "vector_update_subrange",
        "bitvector_update",
        "set_slice",
        "get_slice_int",
        "set_slice_int",
        "ite",
        "isla_read_vreg",
        "isla_init_mask",
        "isla_select_int",
        "isla_vector_access_or_default",
        "isla_vector_select",
        "isla_mux2",
        "isla_masktypei_result",
        "isla_masktypev_result",
        "isla_pack_vreg",
        "fp_add",
        "fp_sub",
        "fp_mul",
        "fp_div",
        "fp_fma",
    ] {
        assert_eq!(effect(name), Some(Effect::Pure), "新增纯原语：{name}");
        assert!(variadic_effect(primops[name]).is_some(), "新增纯原语指针必须可分类：{name}");
    }
}

#[test]
fn effect_writes_state_is_not_pure() {
    let f = unary_primops::<B129>()["assume"];
    assert_eq!(unary_effect(f), Some(Effect::WritesState));
    assert!(!is_pure_unary(f));
    let ctx = Context::new(Config::new());
    let mut solver = Solver::<B129>::new(&ctx);
    f(Val::Bool(false), &mut solver, SourceLoc::unknown()).unwrap();
    assert!(solver.check_sat(SourceLoc::unknown()).is_unsat().unwrap());
    assert!(!is_pure_binary(binary_primops::<B129>()["optimistic_assert"]));
}

#[test]
fn effect_classification_covers_load_time_pointer_rewrites() {
    // 直接遍历加载器消费的声明；新增重写项遗漏分类必须在这里失败。
    let rewrites = crate::ir::load_time_binary_primops::<B129>();
    assert!(!rewrites.is_empty());
    for (sail_name, primop_name, implementation) in rewrites {
        let declared = effect(primop_name).expect("加载期直接重写缺少副作用分类");
        assert!(binary_effect(implementation).unwrap() >= declared, "加载期重写地址分类必须保守：{sail_name}");
    }
}

#[test]
fn effect_const_primops_follow_initialized_values() {
    use crate::ir::URVal;
    for value in [URVal::Init(Val::<B129>::Bool(false)), URVal::Init(Val::Unit), URVal::Init(Val::I64(0))] {
        assert_eq!(effects::const_primop_effect(&value), Effect::Pure);
    }
    for ty in [crate::ir::Ty::Bool, crate::ir::Ty::Bits(16)] {
        assert_eq!(effects::const_primop_effect(&URVal::<B129>::Uninit(ty)), Effect::WritesState);
    }
    assert_eq!(effect("配置中未声明的调用"), None);
}
