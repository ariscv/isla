use super::*;

pub(super) fn call<'ir, B: BV>(
    buildin: Buildin,
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    match buildin {
        Buildin::RiscvRangeSubset => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("range_subset expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_RANGE_SUBSET") {
                return Ok(None);
            }
            range_subset_builtin(args, solver, info)
        }
        Buildin::RiscvSplitMisaligned => {
            if args.len() != 2 {
                return Err(ExecError::Type(
                    format!("split_misaligned expected 2 arguments, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_SPLIT_MISALIGNED") {
                return Ok(None);
            }
            split_misaligned_builtin(args, shared_state, solver, info)
        }
        Buildin::RiscvPmpAddrMatchTypeBackwards => {
            if args.len() != 1 {
                return Err(ExecError::Type(
                    format!("pmpAddrMatchType_encdec_backwards expected 1 argument, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_ADDR_MATCH_TYPE") {
                return Ok(None);
            }
            pmp_addr_match_type_backwards_builtin(args, shared_state, solver, info)
        }
        Buildin::RiscvPmpCheckRwx => {
            if args.len() != 2 {
                return Err(ExecError::Type(format!("pmpCheckRWX expected 2 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_CHECK_RWX") {
                return Ok(None);
            }
            pmp_check_rwx_builtin(args, shared_state, solver, info)
        }
        Buildin::RiscvPmpLocked => {
            if args.len() != 1 {
                return Err(ExecError::Type(format!("pmpLocked expected 1 argument, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_LOCKED") {
                return Ok(None);
            }
            pmp_locked_builtin(args, shared_state, solver, info)
        }
        Buildin::RiscvPmpMatchAddr => {
            if args.len() != 5 {
                return Err(ExecError::Type(format!("pmpMatchAddr expected 5 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PMP_MATCH_ADDR") {
                return Ok(None);
            }
            pmp_match_addr_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvPmpRangeMatch => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmpRangeMatch expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag_default_true("ISLA_RISCV_BUILTIN_PMP_RANGE_MATCH") {
                return Ok(None);
            }
            pmp_range_match_builtin(args, shared_state, solver, info)
        }
        Buildin::RiscvPmpCheck => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmpCheck expected 4 arguments, got {}", args.len()), info));
            }
            if env_flag("ISLA_RISCV_ASSUME_PMP_OFF") {
                return pmp_check_off_builtin(args, shared_state, info);
            }
            if env_flag("ISLA_RISCV_BUILTIN_PMP_CHECK") {
                return pmp_check_builtin(args, frame, shared_state, solver, info);
            }
            Ok(None)
        }
        Buildin::RiscvPmaCheck => {
            if args.len() != 4 {
                return Err(ExecError::Type(format!("pmaCheck expected 4 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PMA_CHECK") {
                return Ok(None);
            }
            pma_check_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvPhysAccessCheck => {
            if args.len() != 5 {
                return Err(ExecError::Type(
                    format!("phys_access_check expected 5 arguments, got {}", args.len()),
                    info,
                ));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK") {
                return Ok(None);
            }
            phys_access_check_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvWithinClint => {
            if args.len() != 2 {
                return Err(ExecError::Type(format!("within_clint expected 2 arguments, got {}", args.len()), info));
            }
            within_clint_builtin(info)
        }
        Buildin::RiscvClintLoad => {
            if args.len() != 3 {
                return Err(ExecError::Type(format!("clint_load expected 3 arguments, got {}", args.len()), info));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_CLINT_LOAD") {
                return Ok(None);
            }
            clint_load_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvWithinMmio => {
            if args.len() != 2 {
                return Err(ExecError::Type(
                    format!("{} expected 2 arguments, got {}", buildin.function_name(), args.len()),
                    info,
                ));
            }
            if !env_flag("ISLA_RISCV_BUILTIN_WITHIN_MMIO") {
                return Ok(None);
            }
            within_mmio_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvVmemWriteAddr => {
            if args.len() != 7 {
                return Err(ExecError::Type(format!("vmem_write_addr expected 7 arguments, got {}", args.len()), info));
            }

            if !riscv_vmem_builtin_enabled("vmem_write_addr") {
                return Ok(None);
            }

            vmem_write_addr_builtin(args, frame, shared_state, solver, info)
        }
        Buildin::RiscvVmemReadAddr => {
            if args.len() != 7 {
                return Err(ExecError::Type(format!("vmem_read_addr expected 7 arguments, got {}", args.len()), info));
            }

            if !riscv_vmem_builtin_enabled("vmem_read_addr") {
                return Ok(None);
            }

            vmem_read_addr_builtin(args, frame, shared_state, solver, info)
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum RiscvVmemBuiltinMode {
    Off,
    Legacy,
    PlainRam,
}

fn riscv_vmem_builtin_mode() -> RiscvVmemBuiltinMode {
    match std::env::var("ISLA_RISCV_VMEM_BUILTIN_MODE") {
        Ok(mode) if mode.eq_ignore_ascii_case("off") => RiscvVmemBuiltinMode::Off,
        Ok(mode) if mode.eq_ignore_ascii_case("plain-ram") => RiscvVmemBuiltinMode::PlainRam,
        Ok(mode) if mode.eq_ignore_ascii_case("plain_ram") => RiscvVmemBuiltinMode::PlainRam,
        Ok(mode) if mode.eq_ignore_ascii_case("legacy") => RiscvVmemBuiltinMode::Legacy,
        Ok(mode) => {
            log!(log::VERBOSE, &format!("unknown ISLA_RISCV_VMEM_BUILTIN_MODE={}; using plain-ram", mode));
            RiscvVmemBuiltinMode::PlainRam
        }
        Err(_) => RiscvVmemBuiltinMode::PlainRam,
    }
}

fn riscv_vmem_builtin_enabled(function_name: &str) -> bool {
    let key = match function_name {
        "vmem_write_addr" => "ISLA_RISCV_BUILTIN_VMEM_WRITE_ADDR",
        "vmem_read_addr" => "ISLA_RISCV_BUILTIN_VMEM_READ_ADDR",
        _ => return false,
    };

    match std::env::var(key) {
        Ok(value) => !matches!(value.as_str(), "0" | "false" | "False" | "FALSE" | "off" | "Off" | "OFF"),
        Err(_) => true,
    }
}

fn env_flag(name: &str) -> bool {
    matches!(std::env::var(name), Ok(value) if matches!(value.as_str(), "1" | "true" | "True" | "TRUE" | "on" | "On" | "ON"))
}

fn env_flag_default_true(name: &str) -> bool {
    match std::env::var(name) {
        Ok(value) => !matches!(value.as_str(), "0" | "false" | "False" | "FALSE" | "off" | "Off" | "OFF"),
        Err(_) => true,
    }
}

fn clint_disabled_predicate_result<B: BV>() -> Option<Val<B>> {
    Some(Val::Bool(false))
}

fn clint_off_requires_within_mmio_builtin(assume_clint_off: bool, within_mmio_builtin_enabled: bool) -> bool {
    assume_clint_off && !within_mmio_builtin_enabled
}

fn within_clint_builtin<B: BV>(info: SourceLoc) -> Result<Option<Val<B>>, ExecError> {
    if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
        if clint_off_requires_within_mmio_builtin(true, env_flag("ISLA_RISCV_BUILTIN_WITHIN_MMIO")) {
            return Err(ExecError::Type(
                "ISLA_RISCV_ASSUME_CLINT_OFF=1 requires ISLA_RISCV_BUILTIN_WITHIN_MMIO=1 to avoid treating CLINT range as RAM".to_string(),
                info,
            ));
        }
        return Ok(clint_disabled_predicate_result());
    }
    Ok(None)
}

fn vmem_write_addr_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    match riscv_vmem_builtin_mode() {
        RiscvVmemBuiltinMode::Off => Ok(None),
        RiscvVmemBuiltinMode::Legacy => vmem_write_addr_legacy_builtin(args, frame, shared_state, solver, info),
        RiscvVmemBuiltinMode::PlainRam => vmem_write_addr_plain_ram_builtin(args, frame, shared_state, solver, info),
    }
}

fn vmem_write_addr_legacy_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let opts = match args[6] {
        Val::Bool(true) => WriteOpts::exclusive(),
        _ => WriteOpts::default(),
    };
    let write_success =
        frame.memory_mut().write(args[3].clone(), args[0].clone(), args[2].clone(), solver, None, opts)?;
    let ok_ctor = lookup_required_vmem_symbol("zOkzIozCUExecutionResultzK", shared_state, info)?;
    Ok(Some(Val::Ctor(ok_ctor, Box::new(write_success))))
}

fn vmem_write_addr_plain_ram_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if let Some(reason) = validate_plain_vmem_write(args, shared_state, solver, info)? {
        if reason == PLAIN_VMEM_MISALIGNED && env_flag("ISLA_RISCV_VMEM_ASSUME_MISALIGNED_FAULTS") {
            log!(log::VERBOSE, "vmem_write_addr builtin returning concrete alignment exception");
            return Ok(Some(vmem_alignment_exception(
                args[0].clone(),
                "zE_SAMO_Addr_Align",
                "zErrzIozCUExecutionResultzK",
                shared_state,
                info,
            )?));
        }
        log!(log::VERBOSE, &format!("vmem_write_addr builtin fallback: {}", reason));
        return Ok(None);
    }

    let write_success = frame.memory_mut().write(
        args[3].clone(),
        args[0].clone(),
        args[2].clone(),
        solver,
        None,
        WriteOpts::default(),
    )?;
    if let Val::Symbolic(success) = write_success {
        solver.add(Def::Assert(SmtExp::Var(success)));
    }
    let ok_ctor = lookup_required_vmem_symbol("zOkzIozCUExecutionResultzK", shared_state, info)?;
    Ok(Some(Val::Ctor(ok_ctor, Box::new(Val::Bool(true)))))
}

fn vmem_read_addr_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    match riscv_vmem_builtin_mode() {
        RiscvVmemBuiltinMode::Off => Ok(None),
        RiscvVmemBuiltinMode::Legacy => vmem_read_addr_legacy_builtin(args, frame, shared_state, solver, info),
        RiscvVmemBuiltinMode::PlainRam => vmem_read_addr_plain_ram_builtin(args, frame, shared_state, solver, info),
    }
}

fn vmem_read_addr_legacy_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let opts = match args[6] {
        Val::Bool(true) => ReadOpts::exclusive(),
        _ => ReadOpts::default(),
    };
    let value = frame.memory().read(args[3].clone(), args[0].clone(), args[2].clone(), solver, false, opts)?;
    let ok_ctor = lookup_required_vmem_symbol("zOkzIbzCUExecutionResultzK", shared_state, info)?;
    Ok(Some(Val::Ctor(ok_ctor, Box::new(value))))
}

fn vmem_read_addr_plain_ram_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if let Some(reason) = validate_plain_vmem_read(args, shared_state, solver, info)? {
        if reason == PLAIN_VMEM_MISALIGNED && env_flag("ISLA_RISCV_VMEM_ASSUME_MISALIGNED_FAULTS") {
            log!(log::VERBOSE, "vmem_read_addr builtin returning concrete alignment exception");
            return Ok(Some(vmem_alignment_exception(
                args[0].clone(),
                "zE_Load_Addr_Align",
                "zErrzIbzCUExecutionResultzK",
                shared_state,
                info,
            )?));
        }
        log!(log::VERBOSE, &format!("vmem_read_addr builtin fallback: {}", reason));
        return Ok(None);
    }

    let value =
        frame.memory().read(args[3].clone(), args[0].clone(), args[2].clone(), solver, false, ReadOpts::default())?;
    let ok_ctor = lookup_required_vmem_symbol("zOkzIbzCUExecutionResultzK", shared_state, info)?;
    Ok(Some(Val::Ctor(ok_ctor, Box::new(value))))
}

fn clint_off_within_mmio_error(reason: &str, info: SourceLoc) -> ExecError {
    ExecError::Type(
        format!(
            "ISLA_RISCV_ASSUME_CLINT_OFF=1 requires within_mmio summary to avoid treating CLINT range as RAM: {}",
            reason
        ),
        info,
    )
}

fn clint_off_within_mmio_fallback<B: BV>(reason: &str, info: SourceLoc) -> Result<Option<Val<B>>, ExecError> {
    log!(log::VERBOSE, &format!("within_mmio builtin fallback: {}", reason));
    if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
        return Err(clint_off_within_mmio_error(reason, info));
    }
    Ok(None)
}

fn clint_disabled_within_mmio_result<B: BV>(
    htif_tohost_base_none: bool,
    clint_range: Val<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if htif_tohost_base_none {
        Ok(Some(clint_range))
    } else {
        Err(clint_off_within_mmio_error("HTIF tohost base is not concrete None", info))
    }
}

fn within_mmio_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_rvfi", shared_state) {
        return clint_off_within_mmio_fallback("get_config_rvfi is not literal false", info);
    }
    let htif_tohost_base_none = htif_tohost_base_is_none(frame, shared_state);
    if !htif_tohost_base_none {
        return clint_off_within_mmio_fallback("HTIF tohost base is not concrete None", info);
    }

    let Some(width) = concrete_width_bytes(&args[1]) else {
        return clint_off_within_mmio_fallback("symbolic width", info);
    };
    if width == 0 {
        return clint_off_within_mmio_fallback("zero width", info);
    }

    let Some((addr, addr_width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        return clint_off_within_mmio_fallback("unsupported address", info);
    };
    let Some((clint_base, clint_base_width)) = let_bitvector_exp_and_width("zplat_clint_base", frame, shared_state)
    else {
        return clint_off_within_mmio_fallback("missing CLINT base", info);
    };
    let Some((clint_size, clint_size_width)) = let_bitvector_exp_and_width("zplat_clint_sizze", frame, shared_state)
    else {
        return clint_off_within_mmio_fallback("missing CLINT size", info);
    };
    if addr_width != clint_base_width || addr_width != clint_size_width || addr_width > 64 {
        return clint_off_within_mmio_fallback("unsupported CLINT/address width", info);
    }

    let addr = unsigned_bv_exp_to_i128(addr, addr_width)?;
    let clint_base = unsigned_bv_exp_to_i128(clint_base, clint_base_width)?;
    let clint_size = unsigned_bv_exp_to_i128(clint_size, clint_size_width)?;
    let clint_range = smt_exp_to_value(unbounded_range_contains_exp(addr, clint_base, clint_size, width), solver)?;
    if env_flag("ISLA_RISCV_ASSUME_CLINT_OFF") {
        clint_disabled_within_mmio_result(htif_tohost_base_none, clint_range, info)
    } else {
        Ok(Some(clint_range))
    }
}

fn unbounded_range_contains_exp(
    addr: SmtExp<Sym>,
    base: SmtExp<Sym>,
    size: SmtExp<Sym>,
    width_bytes: u32,
) -> SmtExp<Sym> {
    let width = smt_i128(i128::from(width_bytes));
    let addr_end = SmtExp::Bvadd(Box::new(addr.clone()), Box::new(width));
    let base_end = SmtExp::Bvadd(Box::new(base.clone()), Box::new(size));
    SmtExp::And(
        Box::new(SmtExp::Bvule(Box::new(base), Box::new(addr))),
        Box::new(SmtExp::Bvule(Box::new(addr_end), Box::new(base_end))),
    )
}

fn range_subset_builtin<B: BV>(
    args: &[Val<B>],
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(width) = range_subset_width(args, solver) else {
        log!(log::VERBOSE, "range_subset builtin fallback: unsupported argument width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "range_subset builtin fallback: zero-width bitvector");
        return Ok(None);
    }

    let a_begin = smt_value(&args[0], info)?;
    let a_size = smt_value(&args[1], info)?;
    let b_begin = smt_value(&args[2], info)?;
    let b_size = smt_value(&args[3], info)?;

    Ok(Some(smt_exp_to_value(range_subset_exp(a_begin, a_size, b_begin, b_size), solver)?))
}

fn range_subset_exp(
    a_begin: SmtExp<Sym>,
    a_size: SmtExp<Sym>,
    b_begin: SmtExp<Sym>,
    b_size: SmtExp<Sym>,
) -> SmtExp<Sym> {
    let a_end =
        SmtExp::Bvsub(Box::new(SmtExp::Bvadd(Box::new(a_begin.clone()), Box::new(a_size))), Box::new(b_begin.clone()));
    let b_end =
        SmtExp::Bvsub(Box::new(SmtExp::Bvadd(Box::new(b_begin.clone()), Box::new(b_size))), Box::new(b_begin.clone()));
    let a_begin = SmtExp::Bvsub(Box::new(a_begin), Box::new(b_begin));

    SmtExp::And(
        Box::new(SmtExp::Bvule(Box::new(a_begin.clone()), Box::new(b_end.clone()))),
        Box::new(SmtExp::And(
            Box::new(SmtExp::Bvule(Box::new(a_end.clone()), Box::new(b_end))),
            Box::new(SmtExp::Bvule(Box::new(a_begin), Box::new(a_end))),
        )),
    )
}

fn range_subset_width<B: BV>(args: &[Val<B>], solver: &mut Solver<B>) -> Option<u32> {
    let mut width = None;
    for arg in args {
        let arg_width = bitvector_width(arg, solver)?;
        match width {
            Some(width) if width != arg_width => return None,
            Some(_) => {}
            None => width = Some(arg_width),
        }
    }
    width
}

fn bitvector_width<B: BV>(value: &Val<B>, solver: &mut Solver<B>) -> Option<u32> {
    match value {
        Val::Bits(bits) => Some(bits.len()),
        Val::Symbolic(sym) => solver.length(*sym),
        _ => None,
    }
}

fn split_misaligned_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(width) = concrete_width_bytes(&args[1]) else {
        log!(log::VERBOSE, "split_misaligned builtin fallback: symbolic width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "split_misaligned builtin fallback: zero width");
        return Ok(None);
    }

    match is_concretely_aligned(&args[0], width) {
        Some(true) => split_misaligned_single_access(width, shared_state, info).map(Some),
        Some(false) => {
            log!(log::VERBOSE, "split_misaligned builtin fallback: concrete misaligned address");
            Ok(None)
        }
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assert_plain_vmem_alignment(&args[0], width, solver, info)?;
            split_misaligned_single_access(width, shared_state, info).map(Some)
        }
        None => {
            log!(log::VERBOSE, "split_misaligned builtin fallback: symbolic alignment");
            Ok(None)
        }
    }
}

fn split_misaligned_single_access<B: BV>(
    width: u32,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let n_field = lookup_required_vmem_symbol("ztuplez3z5i_z5i0", shared_state, info)?;
    let bytes_field = lookup_required_vmem_symbol("ztuplez3z5i_z5i1", shared_state, info)?;
    let mut fields = HashMap::default();
    fields.insert(n_field, Val::I128(1));
    fields.insert(bytes_field, Val::I128(i128::from(width)));
    Ok(Val::Struct(fields))
}

fn pmp_addr_match_type_backwards_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some((bits, width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        log!(log::VERBOSE, "pmpAddrMatchType builtin fallback: unsupported argument");
        return Ok(None);
    };
    if width != 2 {
        log!(log::VERBOSE, "pmpAddrMatchType builtin fallback: non-2-bit argument");
        return Ok(None);
    }

    let off = enum_symbol_exp("zOFF", shared_state, solver, info)?;
    let tor = enum_symbol_exp("zTOR", shared_state, solver, info)?;
    let na4 = enum_symbol_exp("zNA4", shared_state, solver, info)?;
    let napot = enum_symbol_exp("zNAPOT", shared_state, solver, info)?;

    let result = SmtExp::Ite(
        Box::new(SmtExp::Eq(Box::new(bits.clone()), Box::new(smt_sbits(B::new(0, 2))))),
        Box::new(off),
        Box::new(SmtExp::Ite(
            Box::new(SmtExp::Eq(Box::new(bits.clone()), Box::new(smt_sbits(B::new(1, 2))))),
            Box::new(tor),
            Box::new(SmtExp::Ite(
                Box::new(SmtExp::Eq(Box::new(bits), Box::new(smt_sbits(B::new(2, 2))))),
                Box::new(na4),
                Box::new(napot),
            )),
        )),
    );

    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_check_rwx_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(result) = pmp_check_rwx_exp(&args[0], &args[1], shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheckRWX builtin fallback: unsupported access");
        return Ok(None);
    };
    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_locked_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(result) = pmpcfg_bit_is_set(&args[0], 7, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpLocked builtin fallback: unsupported pmpcfg entry");
        return Ok(None);
    };
    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_match_addr_builtin<B: BV>(
    args: &[Val<B>],
    frame: &LocalFrame<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    match concrete_i64_let("zsys_pmp_grain", frame, shared_state) {
        Some(0) => {}
        Some(_) => {
            log!(log::VERBOSE, "pmpMatchAddr builtin fallback: non-zero PMP grain");
            return Ok(None);
        }
        None => {
            log!(log::VERBOSE, "pmpMatchAddr builtin fallback: unknown PMP grain");
            return Ok(None);
        }
    }

    let Some(result) =
        pmp_match_addr_exp(&args[0], &args[1], &args[2], &args[3], &args[4], shared_state, solver, info)?
    else {
        log!(log::VERBOSE, "pmpMatchAddr builtin fallback: unsupported argument");
        return Ok(None);
    };

    Ok(Some(smt_exp_to_value(result, solver)?))
}

fn pmp_match_addr_exp<B: BV>(
    addr_value: &Val<B>,
    width_value: &Val<B>,
    ent: &Val<B>,
    pmpaddr_value: &Val<B>,
    prev_pmpaddr_value: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some((addr_bv, addr_width)) = bitvector_exp_and_width(addr_value, solver, info)? else {
        return Ok(None);
    };
    let Some((width_bv, width_width)) = bitvector_exp_and_width(width_value, solver, info)? else {
        return Ok(None);
    };
    let Some((pmpaddr_bv, pmpaddr_width)) = bitvector_exp_and_width(pmpaddr_value, solver, info)? else {
        return Ok(None);
    };
    let Some((prev_pmpaddr_bv, prev_pmpaddr_width)) = bitvector_exp_and_width(prev_pmpaddr_value, solver, info)? else {
        return Ok(None);
    };
    if addr_width != width_width || addr_width != pmpaddr_width || addr_width != prev_pmpaddr_width || addr_width > 128
    {
        return Ok(None);
    }

    let Some(a_bits) = pmpcfg_a_bits(ent, shared_state, solver, info)? else {
        return Ok(None);
    };

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    let addr = unsigned_bv_exp_to_i128(addr_bv, addr_width)?;
    let width = unsigned_bv_exp_to_i128(width_bv, width_width)?;
    let pmpaddr = unsigned_bv_exp_to_i128(pmpaddr_bv.clone(), pmpaddr_width)?;
    let prev_pmpaddr = unsigned_bv_exp_to_i128(prev_pmpaddr_bv.clone(), prev_pmpaddr_width)?;

    let four = smt_i128(4);
    let tor_begin = SmtExp::Bvmul(Box::new(prev_pmpaddr), Box::new(four.clone()));
    let tor_end = SmtExp::Bvmul(Box::new(pmpaddr.clone()), Box::new(four.clone()));
    let tor_result = SmtExp::Ite(
        Box::new(SmtExp::Bvuge(Box::new(prev_pmpaddr_bv.clone()), Box::new(pmpaddr_bv.clone()))),
        Box::new(no_match.clone()),
        Box::new(pmp_range_match_exp(
            tor_begin,
            tor_end,
            addr.clone(),
            width.clone(),
            &no_match,
            &partial_match,
            &full_match,
        )),
    );

    let na4_begin = SmtExp::Bvmul(Box::new(pmpaddr.clone()), Box::new(four.clone()));
    let na4_end = SmtExp::Bvadd(Box::new(na4_begin.clone()), Box::new(four.clone()));
    let na4_result =
        pmp_range_match_exp(na4_begin, na4_end, addr.clone(), width.clone(), &no_match, &partial_match, &full_match);

    let one_bv = smt_sbits(B::new(1, addr_width));
    let pmpaddr_plus_one = SmtExp::Bvadd(Box::new(pmpaddr_bv.clone()), Box::new(one_bv));
    let mask_bv = SmtExp::Bvxor(Box::new(pmpaddr_bv.clone()), Box::new(pmpaddr_plus_one));
    let begin_words_bv = SmtExp::Bvand(Box::new(pmpaddr_bv), Box::new(SmtExp::Bvnot(Box::new(mask_bv.clone()))));
    let begin_words = unsigned_bv_exp_to_i128(begin_words_bv, addr_width)?;
    let mask = unsigned_bv_exp_to_i128(mask_bv, addr_width)?;
    let end_words =
        SmtExp::Bvadd(Box::new(SmtExp::Bvadd(Box::new(begin_words.clone()), Box::new(mask))), Box::new(smt_i128(1)));
    let napot_begin = SmtExp::Bvmul(Box::new(begin_words), Box::new(four.clone()));
    let napot_end = SmtExp::Bvmul(Box::new(end_words), Box::new(four));
    let napot_result = pmp_range_match_exp(napot_begin, napot_end, addr, width, &no_match, &partial_match, &full_match);

    Ok(Some(SmtExp::Ite(
        Box::new(SmtExp::Eq(Box::new(a_bits.clone()), Box::new(smt_sbits(B::new(0, 2))))),
        Box::new(no_match),
        Box::new(SmtExp::Ite(
            Box::new(SmtExp::Eq(Box::new(a_bits.clone()), Box::new(smt_sbits(B::new(1, 2))))),
            Box::new(tor_result),
            Box::new(SmtExp::Ite(
                Box::new(SmtExp::Eq(Box::new(a_bits), Box::new(smt_sbits(B::new(2, 2))))),
                Box::new(na4_result),
                Box::new(napot_result),
            )),
        )),
    )))
}

fn pmp_range_match_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let begin = int_value_exp(&args[0], info)?;
    let end = int_value_exp(&args[1], info)?;
    let addr = int_value_exp(&args[2], info)?;
    let width = int_value_exp(&args[3], info)?;

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    Ok(Some(smt_exp_to_value(
        pmp_range_match_exp(begin, end, addr, width, &no_match, &partial_match, &full_match),
        solver,
    )?))
}

fn pma_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(computation) = pma_check_compute(args, frame, shared_state, solver, info)? else {
        return Ok(None);
    };
    let PmaCheckComputation { access_fault_cond, access_fault, alignment_fault_cond, alignment_fault, effects } =
        computation;
    commit_pending_builtin_effects(effects, solver);
    option_exception_from_fault_conds(
        access_fault_cond,
        access_fault,
        alignment_fault_cond,
        alignment_fault,
        shared_state,
        solver,
        info,
    )
    .map(Some)
}

fn pma_check_compute<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<PmaCheckComputation<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_print_pma", shared_state) {
        log!(log::VERBOSE, "pmaCheck builtin fallback: get_config_print_pma is not literal false");
        return Ok(None);
    }

    let Some(width) = concrete_width_bytes(&args[1]) else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: symbolic width");
        return Ok(None);
    };
    if width == 0 {
        log!(log::VERBOSE, "pmaCheck builtin fallback: zero width");
        return Ok(None);
    }

    let Some((addr, addr_width)) = bitvector_exp_and_width(&args[0], solver, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported paddr");
        return Ok(None);
    };
    if addr_width == 0 || addr_width > 64 {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported paddr width");
        return Ok(None);
    }
    let addr = if addr_width == 64 { addr } else { SmtExp::ZeroExtend(64 - addr_width, Box::new(addr)) };
    let width_bits = smt_sbits(B::new(u64::from(width), 64));
    let zero64 = smt_sbits(B::new(0, 64));
    let mut assume_aligned = false;
    let misaligned = match is_concretely_aligned(&args[0], width) {
        Some(true) => SmtExp::Bool(false),
        Some(false) => SmtExp::Bool(true),
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assume_aligned = true;
            SmtExp::Bool(false)
        }
        None => SmtExp::Not(Box::new(SmtExp::Eq(
            Box::new(SmtExp::Bvurem(Box::new(addr.clone()), Box::new(width_bits.clone()))),
            Box::new(zero64),
        ))),
    };

    let Some(access_fault) = access_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported access fault");
        return Ok(None);
    };
    let Some(alignment_fault) = alignment_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported alignment fault");
        return Ok(None);
    };

    let pma_regions_name = lookup_required_symbol("zpma_regions", shared_state, info)?;
    let Some(pma_regions) = read_register_value_cloned(frame, pma_regions_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: missing pma_regions register");
        return Ok(None);
    };
    let Val::List(regions) = &pma_regions else {
        log!(log::VERBOSE, "pmaCheck builtin fallback: pma_regions is not a list");
        return Ok(None);
    };

    let mut no_match_so_far = SmtExp::Bool(true);
    let mut access_fault_cond = SmtExp::Bool(false);
    let mut alignment_fault_cond = SmtExp::Bool(false);

    for region in regions.iter().rev() {
        let Some((match_cond, attributes)) =
            pma_region_match_exp(region, &addr, &width_bits, shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA region");
            return Ok(None);
        };
        let Some(can_access) = pma_access_permitted_exp(attributes, &args[2], &args[3], shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA access expression");
            return Ok(None);
        };
        let Some(misaligned_access_fault_mode) =
            pma_enum_field_eq_exp(attributes, "zmisaligned_fault", "zAccessFault", shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA misaligned access-fault mode");
            return Ok(None);
        };
        let Some(misaligned_alignment_fault_mode) =
            pma_enum_field_eq_exp(attributes, "zmisaligned_fault", "zAlignmentFault", shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmaCheck builtin fallback: unsupported PMA misaligned alignment-fault mode");
            return Ok(None);
        };

        let selected = SmtExp::And(Box::new(no_match_so_far.clone()), Box::new(match_cond.clone()));
        let misaligned_access_fault = SmtExp::And(
            Box::new(selected.clone()),
            Box::new(SmtExp::And(Box::new(misaligned.clone()), Box::new(misaligned_access_fault_mode.clone()))),
        );
        let misaligned_alignment_fault = SmtExp::And(
            Box::new(selected.clone()),
            Box::new(SmtExp::And(Box::new(misaligned.clone()), Box::new(misaligned_alignment_fault_mode.clone()))),
        );
        let misaligned_exception = SmtExp::And(
            Box::new(misaligned.clone()),
            Box::new(SmtExp::Or(Box::new(misaligned_access_fault_mode), Box::new(misaligned_alignment_fault_mode))),
        );
        let permission_fault = SmtExp::And(
            Box::new(selected),
            Box::new(SmtExp::And(
                Box::new(SmtExp::Not(Box::new(misaligned_exception))),
                Box::new(SmtExp::Not(Box::new(can_access))),
            )),
        );

        access_fault_cond = SmtExp::Or(
            Box::new(access_fault_cond),
            Box::new(SmtExp::Or(Box::new(misaligned_access_fault), Box::new(permission_fault))),
        );
        alignment_fault_cond = SmtExp::Or(Box::new(alignment_fault_cond), Box::new(misaligned_alignment_fault));
        no_match_so_far = SmtExp::And(Box::new(no_match_so_far), Box::new(SmtExp::Not(Box::new(match_cond))));
    }

    if smt_bool_is(&misaligned, false) {
        alignment_fault_cond = SmtExp::Bool(false);
    }
    access_fault_cond = SmtExp::Or(Box::new(access_fault_cond), Box::new(no_match_so_far));
    let mut effects = vec![PendingBuiltinEffect::ReadReg(pma_regions_name, pma_regions)];
    if assume_aligned {
        if let Some(assertion) = plain_vmem_alignment_assert_exp(&args[0], width, info)? {
            effects.push(PendingBuiltinEffect::Assert(assertion));
        }
    }
    Ok(Some(PmaCheckComputation { access_fault_cond, access_fault, alignment_fault_cond, alignment_fault, effects }))
}

fn phys_access_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !env_flag("ISLA_RISCV_BUILTIN_PMP_CHECK") || !env_flag("ISLA_RISCV_BUILTIN_PMA_CHECK") {
        log!(log::VERBOSE, "phys_access_check builtin fallback: PMP/PMA summaries are not both enabled");
        return Ok(None);
    }

    let pmp_args = vec![args[2].clone(), args[3].clone(), args[0].clone(), args[1].clone()];
    let Some(pmp_result) = pmp_check_compute(&pmp_args, frame, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: pmpCheck child summary did not handle call");
        return Ok(None);
    };

    let pma_args = vec![args[2].clone(), args[3].clone(), args[0].clone(), args[4].clone()];
    let Some(pma_result) = pma_check_compute(&pma_args, frame, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: pmaCheck child summary did not handle call");
        return Ok(None);
    };

    let Some(pma_parts) = pma_result.parts_for_phys_access() else {
        log!(
            log::VERBOSE,
            "phys_access_check builtin fallback: pmaCheck child summary would leave symbolic inner exception"
        );
        return Ok(None);
    };
    let Some(result) = combine_phys_access_options(&pmp_result.parts, &pma_parts, shared_state, solver, info)? else {
        return Ok(None);
    };
    commit_pending_builtin_effects(pmp_result.effects, solver);
    commit_pending_builtin_effects(pma_result.effects, solver);
    Ok(Some(result))
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum ClintLoadHit {
    Msip,
    MtimecmpLow,
    MtimecmpFull,
    MtimecmpHigh,
    MtimeLow,
    MtimeFull,
    MtimeHigh,
}

fn clint_load_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if !function_returns_literal_false("zget_config_print_clint", shared_state) {
        log!(log::VERBOSE, "clint_load builtin fallback: get_config_print_clint is not literal false");
        return Ok(None);
    }

    let Some(width) = concrete_width_bytes(&args[2]) else {
        log!(log::VERBOSE, "clint_load builtin fallback: symbolic width");
        return Ok(None);
    };
    let Some((paddr, paddr_width)) = concrete_bv_u64(&args[1]) else {
        log!(log::VERBOSE, "clint_load builtin fallback: symbolic paddr");
        return Ok(None);
    };
    let Some((clint_base, clint_base_width)) = let_concrete_bv_u64("zplat_clint_base", frame, shared_state) else {
        log!(log::VERBOSE, "clint_load builtin fallback: missing concrete CLINT base");
        return Ok(None);
    };
    if paddr_width != clint_base_width {
        log!(log::VERBOSE, "clint_load builtin fallback: paddr/CLINT base width mismatch");
        return Ok(None);
    }
    let Some(offset) = paddr.checked_sub(clint_base) else {
        log!(log::VERBOSE, "clint_load builtin fallback: paddr below CLINT base");
        return Ok(None);
    };
    let Some(hit) = clint_load_exact_hit(offset, width) else {
        log!(log::VERBOSE, "clint_load builtin fallback: not a concrete exact CLINT load hit");
        return Ok(None);
    };

    let result = match hit {
        ClintLoadHit::Msip => clint_load_msip_result(width, frame, shared_state, solver, info)?,
        ClintLoadHit::MtimecmpLow => {
            clint_load_register_slice_result("zmtimecmp", 31, 0, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimecmpFull => {
            clint_load_register_slice_result("zmtimecmp", 63, 0, 64, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimecmpHigh => {
            clint_load_register_slice_result("zmtimecmp", 63, 32, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeLow => {
            clint_load_register_slice_result("zmtime", 31, 0, 32, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeFull => {
            clint_load_register_slice_result("zmtime", 63, 0, 64, frame, shared_state, solver, info)?
        }
        ClintLoadHit::MtimeHigh => {
            clint_load_register_slice_result("zmtime", 63, 32, 32, frame, shared_state, solver, info)?
        }
    };
    Ok(Some(result))
}

fn clint_load_exact_hit(offset: u64, width: u32) -> Option<ClintLoadHit> {
    match (offset, width) {
        (0x0000, 4 | 8) => Some(ClintLoadHit::Msip),
        (0x4000, 4) => Some(ClintLoadHit::MtimecmpLow),
        (0x4000, 8) => Some(ClintLoadHit::MtimecmpFull),
        (0x4004, 4) => Some(ClintLoadHit::MtimecmpHigh),
        (0xbff8, 4) => Some(ClintLoadHit::MtimeLow),
        (0xbff8, 8) => Some(ClintLoadHit::MtimeFull),
        (0xbffc, 4) => Some(ClintLoadHit::MtimeHigh),
        _ => None,
    }
}

fn clint_load_msip_result<'ir, B: BV>(
    width: u32,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let mip_name = lookup_required_symbol("zmip", shared_state, info)?;
    let Some(mip) = read_register_cloned(frame, mip_name, shared_state, solver, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip register".to_string(), info));
    };
    let Some(bits) = struct_field_value(&mip, "zbits", shared_state, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip.bits field".to_string(), info));
    };
    let Some((bits, bits_width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Err(ExecError::Type("clint_load builtin expected mip.bits bitvector".to_string(), info));
    };
    if bits_width <= 3 {
        return Err(ExecError::Type("clint_load builtin expected mip.bits to contain MSI".to_string(), info));
    }
    let target_width =
        width.checked_mul(8).ok_or_else(|| ExecError::Type("clint_load builtin width overflow".to_string(), info))?;
    let msi = SmtExp::Extract(3, 3, Box::new(bits));
    clint_load_ok_result(zero_extend_exp_to_width(msi, 1, target_width, info)?, shared_state, solver, info)
}

fn clint_load_register_slice_result<'ir, B: BV>(
    register: &str,
    high: u32,
    low: u32,
    target_width: u32,
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let register_name = lookup_required_symbol(register, shared_state, info)?;
    let Some(value) = read_register_cloned(frame, register_name, shared_state, solver, info)? else {
        return Err(ExecError::Type(format!("clint_load builtin expected {} register", register), info));
    };
    let Some((bits, bits_width)) = bitvector_exp_and_width(&value, solver, info)? else {
        return Err(ExecError::Type(format!("clint_load builtin expected {} bitvector", register), info));
    };
    if bits_width != 64 || high >= bits_width || low > high {
        return Err(ExecError::Type(format!("clint_load builtin unsupported {} width", register), info));
    }
    let slice_width = high - low + 1;
    let slice = if high == 63 && low == 0 { bits } else { SmtExp::Extract(high, low, Box::new(bits)) };
    clint_load_ok_result(zero_extend_exp_to_width(slice, slice_width, target_width, info)?, shared_state, solver, info)
}

fn clint_load_ok_result<B: BV>(
    value: SmtExp<Sym>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let ok_ctor = lookup_required_symbol("zOkzIbzCUExceptionTypezK", shared_state, info)?;
    Ok(Val::Ctor(ok_ctor, Box::new(smt_exp_to_value(value, solver)?)))
}

fn zero_extend_exp_to_width(
    exp: SmtExp<Sym>,
    from_width: u32,
    to_width: u32,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    if from_width == to_width {
        Ok(exp)
    } else if from_width < to_width {
        Ok(SmtExp::ZeroExtend(to_width - from_width, Box::new(exp)))
    } else {
        Err(ExecError::Type("clint_load builtin cannot narrow result".to_string(), info))
    }
}

fn pma_region_match_exp<'a, B: BV>(
    region: &'a Val<B>,
    addr: &SmtExp<Sym>,
    width_bits: &SmtExp<Sym>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<(SmtExp<Sym>, &'a Val<B>)>, ExecError> {
    let Some(base_value) = pma_struct_field(region, "zbase", shared_state, info)? else {
        return Ok(None);
    };
    let Some((base, base_width)) = bitvector_exp_and_width(base_value, solver, info)? else {
        return Ok(None);
    };
    if base_width != 64 {
        return Ok(None);
    }

    let Some(size_value) = pma_struct_field(region, "zsizze", shared_state, info)? else {
        return Ok(None);
    };
    let Some((size, size_width)) = bitvector_exp_and_width(size_value, solver, info)? else {
        return Ok(None);
    };
    if size_width != 64 {
        return Ok(None);
    }

    let Some(attributes) = pma_struct_field(region, "zattributes", shared_state, info)? else {
        return Ok(None);
    };

    Ok(Some((range_subset_exp(addr.clone(), width_bits.clone(), base, size), attributes)))
}

fn pma_access_permitted_exp<B: BV>(
    attributes: &Val<B>,
    access: &Val<B>,
    res_or_con: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = access else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => pma_bool_field_exp(attributes, "zexecutable", shared_state, info),
        "zLoadzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(false)) {
                return Ok(None);
            }
            pma_bool_field_exp(attributes, "zreadable", shared_state, info)
        }
        "zStorezIEmem_payloadz5zK" => pma_bool_field_exp(attributes, "zwritable", shared_state, info),
        "zLoadReservedzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(reservable) = pma_reservability_not_none_exp(attributes, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(readable), Box::new(reservable))))
        }
        "zStoreConditionalzIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(reservable) = pma_reservability_not_none_exp(attributes, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(writable), Box::new(reservable))))
        }
        "zAtomiczIEmem_payloadz5zK" => {
            if !matches!(res_or_con, Val::Bool(true)) {
                return Ok(None);
            }
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(readable), Box::new(writable))))
        }
        "zCacheAccesszIEmem_payloadz5zK" => pma_cache_access_permitted_exp(payload, attributes, shared_state, info),
        _ => Ok(None),
    }
}

fn pma_cache_access_permitted_exp<B: BV>(
    cache_op: &Val<B>,
    attributes: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zCB_zzero" => {
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(supports_cbo_zero) = pma_bool_field_exp(attributes, "zsupports_cbo_zzero", shared_state, info)?
            else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(writable), Box::new(supports_cbo_zero))))
        }
        "zCB_manage" => {
            let Some(readable) = pma_bool_field_exp(attributes, "zreadable", shared_state, info)? else {
                return Ok(None);
            };
            let Some(writable) = pma_bool_field_exp(attributes, "zwritable", shared_state, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::Or(Box::new(readable), Box::new(writable))))
        }
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                pma_bool_field_exp(attributes, "zreadable", shared_state, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                pma_bool_field_exp(attributes, "zwritable", shared_state, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                pma_bool_field_exp(attributes, "zexecutable", shared_state, info)
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn pma_bool_field_exp<B: BV>(
    attributes: &Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, field, shared_state, info)? else {
        return Ok(None);
    };
    bool_exp(value)
}

fn pma_reservability_not_none_exp<B: BV>(
    attributes: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, "zreservability", shared_state, info)? else {
        return Ok(None);
    };
    let Some(is_none) = enum_eq_exp(value, "zRsrvNone", shared_state, solver, info)? else {
        return Ok(None);
    };
    Ok(Some(SmtExp::Not(Box::new(is_none))))
}

fn pma_enum_field_eq_exp<B: BV>(
    attributes: &Val<B>,
    field: &str,
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Some(value) = pma_struct_field(attributes, field, shared_state, info)? else {
        return Ok(None);
    };
    enum_eq_exp(value, symbol, shared_state, solver, info)
}

fn pma_struct_field<'a, B: BV>(
    value: &'a Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<&'a Val<B>>, ExecError> {
    struct_field_value(value, field, shared_state, info)
}

fn struct_field_value<'a, B: BV>(
    value: &'a Val<B>,
    field: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<&'a Val<B>>, ExecError> {
    let Val::Struct(fields) = value else {
        return Ok(None);
    };
    let field = lookup_required_symbol(field, shared_state, info)?;
    Ok(fields.get(&field))
}

fn bool_exp<B: BV>(value: &Val<B>) -> Result<Option<SmtExp<Sym>>, ExecError> {
    match value {
        Val::Bool(value) => Ok(Some(SmtExp::Bool(*value))),
        Val::Symbolic(sym) => Ok(Some(SmtExp::Var(*sym))),
        _ => Ok(None),
    }
}

fn enum_eq_exp<B: BV>(
    value: &Val<B>,
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    match value {
        Val::Enum(_) | Val::Symbolic(_) => Ok(Some(SmtExp::Eq(
            Box::new(smt_value(value, info)?),
            Box::new(enum_symbol_exp(symbol, shared_state, solver, info)?),
        ))),
        _ => Ok(None),
    }
}

fn pmp_check_builtin<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(computation) = pmp_check_compute(args, frame, shared_state, solver, info)? else {
        return Ok(None);
    };
    let PmpCheckComputation { parts, effects } = computation;
    commit_pending_builtin_effects(effects, solver);
    option_exception_from_parts(&parts, shared_state, solver, info).map(Some)
}

fn pmp_check_compute<'ir, B: BV>(
    args: &[Val<B>],
    frame: &mut LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<PmpCheckComputation<B>>, ExecError> {
    if env_flag("ISLA_RISCV_ASSUME_PMP_OFF") {
        debug_assert!(pmp_off_assumption_ignores_privilege(&args[3]));
        return Ok(Some(pmp_check_off_computation()));
    }

    let Some(sys_pmp_count) = concrete_i64_let("zsys_pmp_count", frame, shared_state) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unknown PMP count");
        return Ok(None);
    };
    if sys_pmp_count == 0 {
        return Ok(Some(PmpCheckComputation {
            parts: OptionExceptionParts { is_some: SmtExp::Bool(false), fault: None },
            effects: Vec::new(),
        }));
    }
    let Ok(sys_pmp_count) = usize::try_from(sys_pmp_count) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: negative PMP count");
        return Ok(None);
    };
    if sys_pmp_count > 64 {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported PMP count");
        return Ok(None);
    }

    match concrete_i64_let("zsys_pmp_grain", frame, shared_state) {
        Some(0) => {}
        Some(_) => {
            log!(log::VERBOSE, "pmpCheck builtin fallback: non-zero PMP grain");
            return Ok(None);
        }
        None => {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unknown PMP grain");
            return Ok(None);
        }
    }

    let Some(priv_is_machine) = concrete_priv_is_machine(&args[3], shared_state) else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: symbolic privilege");
        return Ok(None);
    };
    let Some(fault) = access_fault_from_access_type_value(&args[2], shared_state, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported access fault");
        return Ok(None);
    };

    let pmpcfg_name = lookup_required_symbol("zpmpcfg_n", shared_state, info)?;
    let pmpaddr_name = lookup_required_symbol("zpmpaddr_n", shared_state, info)?;
    let Some(pmpcfg_vector) = read_register_value_cloned(frame, pmpcfg_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: missing pmpcfg_n register");
        return Ok(None);
    };
    let Some(pmpaddr_vector) = read_register_value_cloned(frame, pmpaddr_name, shared_state, solver, info)? else {
        log!(log::VERBOSE, "pmpCheck builtin fallback: missing pmpaddr_n register");
        return Ok(None);
    };

    let no_match = pmp_addr_match_enum("zPMP_NoMatch", shared_state, solver, info)?;
    let partial_match = pmp_addr_match_enum("zPMP_PartialMatch", shared_state, solver, info)?;
    let full_match = pmp_addr_match_enum("zPMP_Match", shared_state, solver, info)?;

    let mut no_match_so_far = SmtExp::Bool(true);
    let mut fault_cond = SmtExp::Bool(false);

    for i in 0..sys_pmp_count {
        let Some(cfg) = vector_entry(&pmpcfg_vector, i) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpcfg_n entry missing");
            return Ok(None);
        };
        let Some(pmpaddr) = vector_entry(&pmpaddr_vector, i) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpaddr_n entry missing");
            return Ok(None);
        };
        let Some(pmpaddr_width) = bitvector_width(&pmpaddr, solver) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: pmpaddr_n entry is not a bitvector");
            return Ok(None);
        };
        let Some(width_bits) = concrete_i64_as_bv_width(&args[1], pmpaddr_width) else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported width");
            return Ok(None);
        };
        let prev_pmpaddr = if i == 0 {
            Val::Bits(B::zeros(pmpaddr_width))
        } else {
            let Some(prev) = vector_entry(&pmpaddr_vector, i - 1) else {
                log!(log::VERBOSE, "pmpCheck builtin fallback: previous pmpaddr_n entry missing");
                return Ok(None);
            };
            prev
        };

        let Some(match_result) =
            pmp_match_addr_exp(&args[0], &width_bits, &cfg, &pmpaddr, &prev_pmpaddr, shared_state, solver, info)?
        else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpMatchAddr subexpression");
            return Ok(None);
        };
        let is_no_match = SmtExp::Eq(Box::new(match_result.clone()), Box::new(no_match.clone()));
        let is_partial_match = SmtExp::Eq(Box::new(match_result.clone()), Box::new(partial_match.clone()));
        let is_full_match = SmtExp::Eq(Box::new(match_result), Box::new(full_match.clone()));

        let rwx = match pmp_check_rwx_exp(&cfg, &args[2], shared_state, solver, info)? {
            Some(rwx) => rwx,
            None => {
                log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpCheckRWX subexpression");
                return Ok(None);
            }
        };
        let Some(locked) = pmpcfg_bit_is_set(&cfg, 7, shared_state, solver, info)? else {
            log!(log::VERBOSE, "pmpCheck builtin fallback: unsupported pmpLocked subexpression");
            return Ok(None);
        };
        let allowed =
            if priv_is_machine { SmtExp::Or(Box::new(rwx), Box::new(SmtExp::Not(Box::new(locked)))) } else { rwx };

        let partial_fault = SmtExp::And(Box::new(no_match_so_far.clone()), Box::new(is_partial_match));
        let match_fault = SmtExp::And(
            Box::new(no_match_so_far.clone()),
            Box::new(SmtExp::And(Box::new(is_full_match), Box::new(SmtExp::Not(Box::new(allowed))))),
        );
        fault_cond =
            SmtExp::Or(Box::new(fault_cond), Box::new(SmtExp::Or(Box::new(partial_fault), Box::new(match_fault))));
        no_match_so_far = SmtExp::And(Box::new(no_match_so_far), Box::new(is_no_match));
    }

    if !priv_is_machine {
        fault_cond = SmtExp::Or(Box::new(fault_cond), Box::new(no_match_so_far));
    }

    Ok(Some(PmpCheckComputation {
        parts: OptionExceptionParts { is_some: fault_cond, fault: Some(fault) },
        effects: vec![
            PendingBuiltinEffect::ReadReg(pmpcfg_name, pmpcfg_vector),
            PendingBuiltinEffect::ReadReg(pmpaddr_name, pmpaddr_vector),
        ],
    }))
}

fn pmp_check_off_builtin<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    debug_assert!(pmp_off_assumption_ignores_privilege(&args[3]));
    let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
    Ok(Some(Val::Ctor(none_ctor, Box::new(Val::Unit))))
}

fn pmp_check_off_computation<B: BV>() -> PmpCheckComputation<B> {
    PmpCheckComputation {
        parts: OptionExceptionParts { is_some: SmtExp::Bool(false), fault: None },
        effects: Vec::new(),
    }
}

fn pmp_off_assumption_ignores_privilege<B: BV>(_privilege: &Val<B>) -> bool {
    true
}

fn concrete_priv_is_machine<B: BV>(value: &Val<B>, shared_state: &SharedState<B>) -> Option<bool> {
    match value {
        Val::Enum(member) => Some(shared_state.symtab.to_str(member.to_name(shared_state)) == "zMachine"),
        _ => None,
    }
}

fn concrete_i64_as_bv_width<B: BV>(value: &Val<B>, width: u32) -> Option<Val<B>> {
    match value.clone().widen_int() {
        Val::I128(value) => u64::try_from(value).ok().map(|value| Val::Bits(B::new(value, width))),
        _ => None,
    }
}

fn read_register_cloned<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    name: Name,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let value = read_register_value_cloned(frame, name, shared_state, solver, info)?;
    if let Some(value) = &value {
        add_read_register_event(solver, name, value);
    }
    Ok(value)
}

fn read_register_value_cloned<'ir, B: BV>(
    frame: &mut LocalFrame<'ir, B>,
    name: Name,
    shared_state: &SharedState<'ir, B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    frame.regs_mut().get(name, shared_state, solver, info).map(|value| value.cloned())
}

fn add_read_register_event<B: BV>(solver: &mut Solver<B>, name: Name, value: &Val<B>) {
    solver.add_event(Event::ReadReg(name, Vec::new(), value.clone()));
}

fn vector_entry<B: BV>(value: &Val<B>, index: usize) -> Option<Val<B>> {
    match value {
        Val::Vector(entries) => entries.get(index).cloned(),
        _ => None,
    }
}

fn function_returns_literal_false<B: BV>(function_name: &str, shared_state: &SharedState<B>) -> bool {
    let Some(function) = shared_state.symtab.get(function_name) else {
        return false;
    };
    let Some((_, _, instrs)) = shared_state.functions.get(&function) else {
        return false;
    };

    let mut saw_false_return = false;
    for instr in *instrs {
        match instr {
            Instr::Copy(Loc::Id(id), Exp::Bool(false), _) if *id == RETURN => saw_false_return = true,
            Instr::End => return saw_false_return,
            _ => return false,
        }
    }
    false
}

fn htif_tohost_base_is_none<B: BV>(frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> bool {
    let Some(htif_base) = shared_state.symtab.get("zhtif_tohost_base") else {
        return false;
    };
    matches!(
        frame.regs().get_last_if_initialized(htif_base),
        Some(Val::Ctor(ctor, _)) if shared_state.symtab.to_str(*ctor) == "zNonezIbzK"
    )
}

fn let_bitvector_exp_and_width<B: BV>(
    name: &str,
    frame: &LocalFrame<B>,
    shared_state: &SharedState<B>,
) -> Option<(SmtExp<Sym>, u32)> {
    let name = shared_state.symtab.get(name)?;
    match frame.lets().get(&name) {
        Some(UVal::Init(Val::Bits(bits))) => Some((smt_sbits(*bits), bits.len())),
        _ => None,
    }
}

fn let_concrete_bv_u64<B: BV>(name: &str, frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> Option<(u64, u32)> {
    let name = shared_state.symtab.get(name)?;
    match frame.lets().get(&name) {
        Some(UVal::Init(value)) => concrete_bv_u64(value),
        _ => None,
    }
}

fn concrete_bv_u64<B: BV>(value: &Val<B>) -> Option<(u64, u32)> {
    match value {
        Val::Bits(bits) if bits.len() <= 64 => Some((bits.lower_u64(), bits.len())),
        _ => None,
    }
}

fn access_fault_from_access_type_value<B: BV>(
    access: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(exception_ctor) = access_fault_ctor_name(access, shared_state) else {
        return Ok(None);
    };
    let exception_ctor = lookup_required_symbol(exception_ctor, shared_state, info)?;
    Ok(Some(Val::Ctor(exception_ctor, Box::new(Val::Unit))))
}

fn alignment_fault_from_access_type_value<B: BV>(
    access: &Val<B>,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let Some(exception_ctor) = alignment_fault_ctor_name(access, shared_state) else {
        return Ok(None);
    };
    let exception_ctor = lookup_required_symbol(exception_ctor, shared_state, info)?;
    Ok(Some(Val::Ctor(exception_ctor, Box::new(Val::Unit))))
}

fn access_fault_ctor_name<B: BV>(access: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = access else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => Some("zE_Fetch_Access_Fault"),
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => Some("zE_Load_Access_Fault"),
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" | "zAtomiczIEmem_payloadz5zK" => {
            Some("zE_SAMO_Access_Fault")
        }
        "zCacheAccesszIEmem_payloadz5zK" => cache_access_fault_ctor_name(payload, shared_state),
        _ => None,
    }
}

fn alignment_fault_ctor_name<B: BV>(access: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = access else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zInstructionFetchzIEmem_payloadz5zK" => Some("zE_Fetch_Addr_Align"),
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => Some("zE_Load_Addr_Align"),
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" | "zAtomiczIEmem_payloadz5zK" => {
            Some("zE_SAMO_Addr_Align")
        }
        "zCacheAccesszIEmem_payloadz5zK" => cache_alignment_fault_ctor_name(payload, shared_state),
        _ => None,
    }
}

fn cache_access_fault_ctor_name<B: BV>(cache_op: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" | "zCB_zzero" => Some("zE_SAMO_Access_Fault"),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                Some("zE_Load_Access_Fault")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                Some("zE_SAMO_Access_Fault")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                Some("zE_Fetch_Access_Fault")
            }
            _ => None,
        },
        _ => None,
    }
}

fn cache_alignment_fault_ctor_name<B: BV>(cache_op: &Val<B>, shared_state: &SharedState<B>) -> Option<&'static str> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return None;
    };
    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" | "zCB_zzero" => Some("zE_SAMO_Addr_Align"),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                Some("zE_Load_Addr_Align")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                Some("zE_SAMO_Addr_Align")
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                Some("zE_Fetch_Addr_Align")
            }
            _ => None,
        },
        _ => None,
    }
}

enum PendingBuiltinEffect<B: BV> {
    ReadReg(Name, Val<B>),
    Assert(SmtExp<Sym>),
}

fn commit_pending_builtin_effects<B: BV>(effects: Vec<PendingBuiltinEffect<B>>, solver: &mut Solver<B>) {
    for effect in effects {
        match effect {
            PendingBuiltinEffect::ReadReg(name, value) => add_read_register_event(solver, name, &value),
            PendingBuiltinEffect::Assert(assertion) => solver.add(Def::Assert(assertion)),
        }
    }
}

struct PmpCheckComputation<B: BV> {
    parts: OptionExceptionParts<B>,
    effects: Vec<PendingBuiltinEffect<B>>,
}

struct PmaCheckComputation<B: BV> {
    access_fault_cond: SmtExp<Sym>,
    access_fault: Val<B>,
    alignment_fault_cond: SmtExp<Sym>,
    alignment_fault: Val<B>,
    effects: Vec<PendingBuiltinEffect<B>>,
}

impl<B: BV> PmaCheckComputation<B> {
    fn parts_for_phys_access(&self) -> Option<OptionExceptionParts<B>> {
        if smt_bool_is(&self.alignment_fault_cond, false) {
            return Some(OptionExceptionParts {
                is_some: self.access_fault_cond.clone(),
                fault: Some(self.access_fault.clone()),
            });
        }
        if smt_bool_is(&self.access_fault_cond, false) {
            return Some(OptionExceptionParts {
                is_some: self.alignment_fault_cond.clone(),
                fault: Some(self.alignment_fault.clone()),
            });
        }
        if self.access_fault == self.alignment_fault {
            return Some(OptionExceptionParts {
                is_some: SmtExp::Or(
                    Box::new(self.access_fault_cond.clone()),
                    Box::new(self.alignment_fault_cond.clone()),
                ),
                fault: Some(self.access_fault.clone()),
            });
        }
        None
    }
}

struct OptionExceptionParts<B: BV> {
    is_some: SmtExp<Sym>,
    fault: Option<Val<B>>,
}

fn combine_phys_access_options<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    if smt_bool_is(&pmp.is_some, false) {
        return option_exception_from_parts(pma, shared_state, solver, info).map(Some);
    }
    if smt_bool_is(&pma.is_some, false) {
        return option_exception_from_parts(pmp, shared_state, solver, info).map(Some);
    }

    let fault_cond = SmtExp::Or(Box::new(pmp.is_some.clone()), Box::new(pma.is_some.clone()));
    let Some(fault) = selected_phys_access_fault(pmp, pma, shared_state, solver, info)? else {
        log!(log::VERBOSE, "phys_access_check builtin fallback: symbolic inner exception would remain");
        return Ok(None);
    };
    option_exception_from_fault_cond(fault_cond, fault, shared_state, solver, info).map(Some)
}

fn option_exception_from_parts<B: BV>(
    parts: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if smt_bool_is(&parts.is_some, false) {
        let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
        return Ok(Val::Ctor(none_ctor, Box::new(Val::Unit)));
    }
    let fault = required_option_fault(parts, "phys_access_check builtin expected Some fault", info)?;
    option_exception_from_fault_cond(parts.is_some.clone(), fault.clone(), shared_state, solver, info)
}

fn selected_phys_access_fault<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
    shared_state: &SharedState<B>,
    _solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<Val<B>>, ExecError> {
    let pmp_fault = required_option_fault(pmp, "phys_access_check builtin expected PMP fault", info)?;
    let pma_fault = required_option_fault(pma, "phys_access_check builtin expected PMA fault", info)?;
    let Some((pmp_ctor, pmp_payload)) = concrete_exception_ctor_payload_or_fallback(pmp_fault, "PMP", info)? else {
        return Ok(None);
    };
    let Some((pma_ctor, pma_payload)) = concrete_exception_ctor_payload_or_fallback(pma_fault, "PMA", info)? else {
        return Ok(None);
    };
    let pmp_name = shared_state.symtab.to_str(pmp_ctor);
    let pma_name = shared_state.symtab.to_str(pma_ctor);
    let Some(chosen) = highest_priority_alignment_or_access_fault_name(pmp_name, pma_name) else {
        return Err(ExecError::Type(
            format!("phys_access_check builtin cannot prioritize {} vs {}", pmp_name, pma_name),
            info,
        ));
    };
    let (both_ctor, both_payload) =
        if chosen == pmp_name { (pmp_ctor, pmp_payload.clone()) } else { (pma_ctor, pma_payload.clone()) };

    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, true) {
        return Ok(Some(Val::Ctor(both_ctor, Box::new(both_payload))));
    }
    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, false) {
        return Ok(Some(Val::Ctor(pmp_ctor, Box::new(pmp_payload))));
    }
    if smt_bool_is(&pmp.is_some, false) && smt_bool_is(&pma.is_some, true) {
        return Ok(Some(Val::Ctor(pma_ctor, Box::new(pma_payload))));
    }
    if pmp_ctor == pma_ctor && pmp_payload == pma_payload && pmp_ctor == both_ctor && pmp_payload == both_payload {
        return Ok(Some(Val::Ctor(pmp_ctor, Box::new(pmp_payload))));
    }

    if phys_access_fault_selection_requires_fallback(pmp, pma) {
        return Ok(None);
    }

    Ok(None)
}

fn phys_access_fault_selection_requires_fallback<B: BV>(
    pmp: &OptionExceptionParts<B>,
    pma: &OptionExceptionParts<B>,
) -> bool {
    if smt_bool_is(&pmp.is_some, false) || smt_bool_is(&pma.is_some, false) {
        return false;
    }
    if smt_bool_is(&pmp.is_some, true) && smt_bool_is(&pma.is_some, true) {
        return false;
    }
    pmp.fault != pma.fault
}

fn required_option_fault<'a, B: BV>(
    parts: &'a OptionExceptionParts<B>,
    context: &str,
    info: SourceLoc,
) -> Result<&'a Val<B>, ExecError> {
    parts.fault.as_ref().ok_or_else(|| ExecError::Type(context.to_string(), info))
}

fn concrete_exception_ctor_payload_or_fallback<B: BV>(
    value: &Val<B>,
    context: &str,
    info: SourceLoc,
) -> Result<Option<(Name, Val<B>)>, ExecError> {
    match value {
        Val::Ctor(ctor, payload) => Ok(Some((*ctor, payload.as_ref().clone()))),
        Val::SymbolicCtor(_, _) => Ok(None),
        _ => Err(ExecError::Type(format!("phys_access_check builtin expected concrete {} exception", context), info)),
    }
}

fn highest_priority_alignment_or_access_fault_name<'a>(left: &'a str, right: &'a str) -> Option<&'a str> {
    let left_priority = alignment_or_access_fault_priority_name(left)?;
    let right_priority = alignment_or_access_fault_priority_name(right)?;
    if left_priority > right_priority {
        Some(left)
    } else {
        Some(right)
    }
}

fn alignment_or_access_fault_priority_name(name: &str) -> Option<u8> {
    match name {
        "zE_Fetch_Addr_Align" | "zE_Load_Addr_Align" | "zE_SAMO_Addr_Align" => Some(0),
        "zE_Fetch_Access_Fault" | "zE_Load_Access_Fault" | "zE_SAMO_Access_Fault" => Some(1),
        _ => None,
    }
}

fn option_exception_from_fault_cond<B: BV>(
    fault_cond: SmtExp<Sym>,
    fault: Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let some_ctor = lookup_required_symbol("zSomezIUExceptionTypezK", shared_state, info)?;
    let none_ctor = lookup_required_symbol("zNonezIUExceptionTypezK", shared_state, info)?;
    if smt_bool_is(&fault_cond, false) {
        return Ok(Val::Ctor(none_ctor, Box::new(Val::Unit)));
    }
    if smt_bool_is(&fault_cond, true) {
        return Ok(Val::Ctor(some_ctor, Box::new(fault)));
    }
    let discrim = solver.define_const(
        SmtExp::Ite(Box::new(fault_cond), Box::new(some_ctor.to_smt()), Box::new(none_ctor.to_smt())),
        info,
    );

    let mut possibilities = HashMap::default();
    possibilities.insert(some_ctor, fault);
    possibilities.insert(none_ctor, Val::Unit);
    Ok(Val::SymbolicCtor(discrim, possibilities))
}

fn option_exception_from_fault_conds<B: BV>(
    access_fault_cond: SmtExp<Sym>,
    access_fault: Val<B>,
    alignment_fault_cond: SmtExp<Sym>,
    alignment_fault: Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    if smt_bool_is(&alignment_fault_cond, false) {
        return option_exception_from_fault_cond(access_fault_cond, access_fault, shared_state, solver, info);
    }
    if smt_bool_is(&access_fault_cond, false) {
        return option_exception_from_fault_cond(alignment_fault_cond, alignment_fault, shared_state, solver, info);
    }

    let fault_cond = SmtExp::Or(Box::new(access_fault_cond), Box::new(alignment_fault_cond.clone()));
    if access_fault == alignment_fault {
        return option_exception_from_fault_cond(fault_cond, access_fault, shared_state, solver, info);
    }

    let (Val::Ctor(access_ctor, access_payload), Val::Ctor(alignment_ctor, alignment_payload)) =
        (access_fault, alignment_fault)
    else {
        return Err(ExecError::Type("pmaCheck builtin expected concrete exception constructors".to_string(), info));
    };

    let discrim = solver.define_const(
        SmtExp::Ite(Box::new(alignment_fault_cond), Box::new(alignment_ctor.to_smt()), Box::new(access_ctor.to_smt())),
        info,
    );

    let mut possibilities = HashMap::default();
    possibilities.insert(access_ctor, *access_payload);
    possibilities.insert(alignment_ctor, *alignment_payload);
    option_exception_from_fault_cond(fault_cond, Val::SymbolicCtor(discrim, possibilities), shared_state, solver, info)
}

fn smt_bool_is(exp: &SmtExp<Sym>, value: bool) -> bool {
    matches!(exp, SmtExp::Bool(actual) if *actual == value)
}

fn int_value_exp<B: BV>(value: &Val<B>, info: SourceLoc) -> Result<SmtExp<Sym>, ExecError> {
    match value {
        Val::I128(value) => Ok(smt_i128(*value)),
        Val::I64(value) => Ok(smt_i128(i128::from(*value))),
        Val::Symbolic(sym) => Ok(SmtExp::Var(*sym)),
        _ => Err(ExecError::Type(format!("integer expression {:?}", value), info)),
    }
}

fn concrete_i64_let<B: BV>(name: &str, frame: &LocalFrame<B>, shared_state: &SharedState<B>) -> Option<i64> {
    shared_state.symtab.get(name).and_then(|name| match frame.lets().get(&name) {
        Some(UVal::Init(Val::I64(value))) => Some(*value),
        _ => None,
    })
}

fn bitvector_exp_and_width<B: BV>(
    value: &Val<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<(SmtExp<Sym>, u32)>, ExecError> {
    let Some(width) = bitvector_width(value, solver) else {
        return Ok(None);
    };
    Ok(Some((smt_value(value, info)?, width)))
}

fn pmpcfg_a_bits<B: BV>(
    ent: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Struct(fields) = ent else {
        return Ok(None);
    };
    let bits_field = lookup_required_symbol("zbits", shared_state, info)?;
    let Some(bits) = fields.get(&bits_field) else {
        return Ok(None);
    };
    let Some((bits, width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Ok(None);
    };
    if width != 8 {
        return Ok(None);
    }
    Ok(Some(SmtExp::Extract(4, 3, Box::new(bits))))
}

fn pmpcfg_bit_is_set<B: BV>(
    ent: &Val<B>,
    bit: u32,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Struct(fields) = ent else {
        return Ok(None);
    };
    let bits_field = lookup_required_symbol("zbits", shared_state, info)?;
    let Some(bits) = fields.get(&bits_field) else {
        return Ok(None);
    };
    let Some((bits, width)) = bitvector_exp_and_width(bits, solver, info)? else {
        return Ok(None);
    };
    if width != 8 {
        return Ok(None);
    }
    Ok(Some(SmtExp::Eq(Box::new(SmtExp::Extract(bit, bit, Box::new(bits))), Box::new(smt_sbits(B::new(1, 1))))))
}

fn pmp_check_rwx_exp<B: BV>(
    ent: &Val<B>,
    access: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = access else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zLoadzIEmem_payloadz5zK" | "zLoadReservedzIEmem_payloadz5zK" => {
            pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)
        }
        "zStorezIEmem_payloadz5zK" | "zStoreConditionalzIEmem_payloadz5zK" => {
            pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)
        }
        "zAtomiczIEmem_payloadz5zK" => {
            let Some(r) = pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)? else {
                return Ok(None);
            };
            let Some(w) = pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::And(Box::new(r), Box::new(w))))
        }
        "zInstructionFetchzIEmem_payloadz5zK" => pmpcfg_bit_is_set(ent, 2, shared_state, solver, info),
        "zCacheAccesszIEmem_payloadz5zK" => pmp_check_rwx_cache_exp(payload, ent, shared_state, solver, info),
        _ => Ok(None),
    }
}

fn pmp_check_rwx_cache_exp<B: BV>(
    cache_op: &Val<B>,
    ent: &Val<B>,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    let Val::Ctor(ctor, payload) = cache_op else {
        return Ok(None);
    };

    match shared_state.symtab.to_str(*ctor) {
        "zCB_manage" => {
            let Some(r) = pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)? else {
                return Ok(None);
            };
            let Some(w) = pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)? else {
                return Ok(None);
            };
            Ok(Some(SmtExp::Or(Box::new(r), Box::new(w))))
        }
        "zCB_zzero" => pmpcfg_bit_is_set(ent, 1, shared_state, solver, info),
        "zCB_prefetch" => match payload.as_ref() {
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_I" => {
                pmpcfg_bit_is_set(ent, 2, shared_state, solver, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_R" => {
                pmpcfg_bit_is_set(ent, 0, shared_state, solver, info)
            }
            Val::Enum(member) if shared_state.symtab.to_str(member.to_name(shared_state)) == "zPREFETCH_W" => {
                pmpcfg_bit_is_set(ent, 1, shared_state, solver, info)
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn pmp_addr_match_enum<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    enum_symbol_exp(symbol, shared_state, solver, info)
}

fn enum_symbol_exp<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<SmtExp<Sym>, ExecError> {
    let member = lookup_required_symbol(symbol, shared_state, info)?;
    let Some((member_index, enum_size, enum_name)) = shared_state.type_info.enum_members.get(&member) else {
        return Err(ExecError::Type(format!("builtin expected enum member {}", symbol), info));
    };
    let enum_id = solver.get_enum(*enum_name, *enum_size);
    Ok(SmtExp::Enum(EnumMember { enum_id, member: *member_index }))
}

fn unsigned_bv_exp_to_i128(exp: SmtExp<Sym>, width: u32) -> Result<SmtExp<Sym>, ExecError> {
    if width > 128 {
        Err(ExecError::Type(
            format!("pmpMatchAddr cannot zero-extend {}-bit value to int", width),
            SourceLoc::unknown(),
        ))
    } else if width == 128 {
        Ok(exp)
    } else {
        Ok(SmtExp::ZeroExtend(128 - width, Box::new(exp)))
    }
}

fn pmp_range_match_exp(
    begin: SmtExp<Sym>,
    end: SmtExp<Sym>,
    addr: SmtExp<Sym>,
    width: SmtExp<Sym>,
    no_match: &SmtExp<Sym>,
    partial_match: &SmtExp<Sym>,
    full_match: &SmtExp<Sym>,
) -> SmtExp<Sym> {
    let addr_end = SmtExp::Bvadd(Box::new(addr.clone()), Box::new(width));
    let no_match_cond = SmtExp::Or(
        Box::new(SmtExp::Bvsle(Box::new(addr_end.clone()), Box::new(begin.clone()))),
        Box::new(SmtExp::Bvsle(Box::new(end.clone()), Box::new(addr.clone()))),
    );
    let full_match_cond = SmtExp::And(
        Box::new(SmtExp::Bvsle(Box::new(begin), Box::new(addr))),
        Box::new(SmtExp::Bvsle(Box::new(addr_end), Box::new(end))),
    );
    SmtExp::Ite(
        Box::new(no_match_cond),
        Box::new(no_match.clone()),
        Box::new(SmtExp::Ite(Box::new(full_match_cond), Box::new(full_match.clone()), Box::new(partial_match.clone()))),
    )
}

const PLAIN_VMEM_MISALIGNED: &str = "misaligned concrete address";

fn vmem_alignment_exception<B: BV>(
    address: Val<B>,
    exception_ctor_name: &str,
    result_err_ctor_name: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Val<B>, ExecError> {
    let exception_ctor = lookup_required_vmem_symbol(exception_ctor_name, shared_state, info)?;
    let memory_exception_ctor = lookup_required_vmem_symbol("zMemory_Exception", shared_state, info)?;
    let result_err_ctor = lookup_required_vmem_symbol(result_err_ctor_name, shared_state, info)?;
    let address_len = match &address {
        Val::Bits(address) => address.len(),
        _ => {
            return Err(ExecError::Type(
                format!("vmem alignment exception requires concrete address, got {:?}", address),
                info,
            ))
        }
    };
    let address_field = lookup_required_vmem_symbol(
        &format!("ztuplez3z5bv{}_z5unionz0zzExceptionType0", address_len),
        shared_state,
        info,
    )?;
    let exception_field = lookup_required_vmem_symbol(
        &format!("ztuplez3z5bv{}_z5unionz0zzExceptionType1", address_len),
        shared_state,
        info,
    )?;

    let exception = Val::Ctor(exception_ctor, Box::new(Val::Unit));
    let mut memory_exception_fields = HashMap::default();
    memory_exception_fields.insert(address_field, address);
    memory_exception_fields.insert(exception_field, exception);
    let memory_exception = Val::Ctor(memory_exception_ctor, Box::new(Val::Struct(memory_exception_fields)));

    Ok(Val::Ctor(result_err_ctor, Box::new(memory_exception)))
}

fn lookup_required_vmem_symbol<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Name, ExecError> {
    lookup_required_symbol(symbol, shared_state, info)
}

fn lookup_required_symbol<B: BV>(
    symbol: &str,
    shared_state: &SharedState<B>,
    info: SourceLoc,
) -> Result<Name, ExecError> {
    shared_state
        .symtab
        .get(symbol)
        .ok_or_else(|| ExecError::Type(format!("builtin expected IR symbol {}", symbol), info))
}

fn validate_plain_vmem_write<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    if let Some(reason) = validate_plain_vmem_common(
        &args[0],
        &args[1],
        &args[3],
        &args[4],
        &args[5],
        &args[6],
        "zStorezIEmem_payloadz5zK",
        shared_state,
        solver,
        info,
    )? {
        return Ok(Some(reason));
    }

    let width = match concrete_width_bytes(&args[1]) {
        Some(width) => width,
        None => return Ok(Some("non-concrete write width")),
    };
    let data_bits = crate::primop_util::length_bits(&args[2], solver, info)?;
    if data_bits != width * 8 {
        return Ok(Some("write data length does not match width"));
    }

    Ok(None)
}

fn validate_plain_vmem_read<B: BV>(
    args: &[Val<B>],
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    validate_plain_vmem_common(
        &args[0],
        &args[2],
        &args[3],
        &args[4],
        &args[5],
        &args[6],
        "zLoadzIEmem_payloadz5zK",
        shared_state,
        solver,
        info,
    )
}

fn validate_plain_vmem_common<B: BV>(
    address: &Val<B>,
    width: &Val<B>,
    access: &Val<B>,
    aq: &Val<B>,
    rl: &Val<B>,
    res: &Val<B>,
    expected_access_ctor: &str,
    shared_state: &SharedState<B>,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<Option<&'static str>, ExecError> {
    if *aq != Val::Bool(false) {
        return Ok(Some("aq is not false"));
    }
    if *rl != Val::Bool(false) {
        return Ok(Some("rl is not false"));
    }
    if *res != Val::Bool(false) {
        return Ok(Some("reservation access is not supported"));
    }
    if !is_data_access_ctor(access, expected_access_ctor, shared_state) {
        return Ok(Some("access is not ordinary Data load/store"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_IDENTITY_TRANSLATION") {
        return Ok(Some("identity translation is not explicitly assumed"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_PMP_PERMITS") {
        return Ok(Some("PMP permission is not explicitly assumed"));
    }
    if !env_flag("ISLA_RISCV_VMEM_ASSUME_PLAIN_RAM") {
        return Ok(Some("plain RAM region is not explicitly assumed"));
    }

    let width = match concrete_width_bytes(width) {
        Some(width) => width,
        None => return Ok(Some("non-concrete access width")),
    };
    if width == 0 {
        return Err(ExecError::Type("vmem builtin received zero-width access".to_string(), SourceLoc::unknown()));
    }

    match is_concretely_aligned(address, width) {
        Some(true) => Ok(None),
        Some(false) => Ok(Some(PLAIN_VMEM_MISALIGNED)),
        None if env_flag("ISLA_RISCV_VMEM_ASSUME_ALIGNED") => {
            assert_plain_vmem_alignment(address, width, solver, info)?;
            Ok(None)
        }
        None => Ok(Some("alignment is not proven")),
    }
}

fn assert_plain_vmem_alignment<B: BV>(
    address: &Val<B>,
    width: u32,
    solver: &mut Solver<B>,
    info: SourceLoc,
) -> Result<(), ExecError> {
    if let Some(assertion) = plain_vmem_alignment_assert_exp(address, width, info)? {
        solver.add(Def::Assert(assertion));
    }
    Ok(())
}

fn plain_vmem_alignment_assert_exp<B: BV>(
    address: &Val<B>,
    width: u32,
    info: SourceLoc,
) -> Result<Option<SmtExp<Sym>>, ExecError> {
    if width == 1 {
        return Ok(None);
    }
    if !width.is_power_of_two() {
        return Err(ExecError::Type(
            format!("vmem builtin cannot assert non-power-of-two alignment width {}", width),
            info,
        ));
    }

    let align_bits = width.trailing_zeros();
    let low_bits = SmtExp::Extract(align_bits - 1, 0, Box::new(smt_value(address, info)?));
    let zero = SmtExp::Bits64(B64::zeros(align_bits));
    Ok(Some(SmtExp::Eq(Box::new(low_bits), Box::new(zero))))
}

fn concrete_width_bytes<B: BV>(width: &Val<B>) -> Option<u32> {
    match width.clone().widen_int() {
        Val::I128(width) => u32::try_from(width).ok(),
        _ => None,
    }
}

fn is_concretely_aligned<B: BV>(address: &Val<B>, width: u32) -> Option<bool> {
    match address {
        Val::Bits(addr) => Some(addr.lower_u64() % u64::from(width) == 0),
        _ => None,
    }
}

fn is_data_access_ctor<B: BV>(access: &Val<B>, expected_ctor: &str, shared_state: &SharedState<B>) -> bool {
    match access {
        Val::Ctor(ctor, payload) if shared_state.symtab.to_str(*ctor) == expected_ctor => match payload.as_ref() {
            Val::Enum(member) => {
                let enum_name = shared_state.symtab.to_str(member.enum_id.to_name());
                enum_name == "zmem_payload" && member.member == 0
            }
            _ => false,
        },
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvector::b64::B64;

    fn bv64(value: u64, width: u32) -> SmtExp<Sym> {
        smt_sbits(B64::new(value, width))
    }

    fn i128_bv(value: i128) -> SmtExp<Sym> {
        smt_i128(value)
    }

    fn eval_bool(exp: SmtExp<Sym>) -> bool {
        match exp {
            SmtExp::Bool(value) => value,
            SmtExp::And(lhs, rhs) => eval_bool(*lhs) && eval_bool(*rhs),
            SmtExp::Or(lhs, rhs) => eval_bool(*lhs) || eval_bool(*rhs),
            SmtExp::Not(exp) => !eval_bool(*exp),
            SmtExp::Bvule(lhs, rhs) => {
                let (lhs, lhs_width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(lhs_width, rhs_width);
                lhs <= rhs
            }
            _ => panic!("unsupported bool expression in test: {:?}", exp),
        }
    }

    fn eval_bv(exp: SmtExp<Sym>) -> (u128, u32) {
        match exp {
            SmtExp::Bits64(bits) => (u128::from(bits.lower_u64()), bits.len()),
            SmtExp::Bits(bits) => {
                let mut value = 0_u128;
                for (index, bit) in bits.iter().enumerate() {
                    if *bit {
                        value |= 1_u128 << index;
                    }
                }
                (value, bits.len() as u32)
            }
            SmtExp::Bvadd(lhs, rhs) => {
                let (lhs, width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(width, rhs_width);
                ((lhs + rhs) & mask(width), width)
            }
            SmtExp::Bvsub(lhs, rhs) => {
                let (lhs, width) = eval_bv(*lhs);
                let (rhs, rhs_width) = eval_bv(*rhs);
                assert_eq!(width, rhs_width);
                (lhs.wrapping_sub(rhs) & mask(width), width)
            }
            _ => panic!("unsupported bitvector expression in test: {:?}", exp),
        }
    }

    fn mask(width: u32) -> u128 {
        if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        }
    }

    #[test]
    fn range_subset_exp_matches_sail_wraparound_cases() {
        assert!(eval_bool(range_subset_exp(bv64(0xffff_fffc, 32), bv64(4, 32), bv64(0xffff_fff0, 32), bv64(0x20, 32))));
        assert!(!eval_bool(range_subset_exp(
            bv64(0xffff_fffc, 32),
            bv64(0x24, 32),
            bv64(0xffff_fff0, 32),
            bv64(0x20, 32)
        )));
        assert!(!eval_bool(range_subset_exp(bv64(0x10, 32), bv64(4, 32), bv64(0xffff_fff0, 32), bv64(0x20, 32))));
    }

    #[test]
    fn unbounded_range_contains_exp_does_not_wrap() {
        assert!(eval_bool(unbounded_range_contains_exp(i128_bv(0xffff_fffc), i128_bv(0xffff_fff0), i128_bv(0x20), 4)));
        assert!(!eval_bool(unbounded_range_contains_exp(
            i128_bv(i128::from(u64::MAX) - 1),
            i128_bv(i128::from(u64::MAX) - 8),
            i128_bv(8),
            4,
        )));
    }

    #[test]
    fn clint_off_predicates_return_false_only_when_safe() {
        assert!(matches!(clint_disabled_predicate_result::<B64>(), Some(Val::Bool(false))));
        assert!(clint_off_requires_within_mmio_builtin(true, false));
        assert!(!clint_off_requires_within_mmio_builtin(true, true));
        assert!(!clint_off_requires_within_mmio_builtin(false, false));
        assert!(matches!(
            clint_disabled_within_mmio_result(true, Val::<B64>::Bool(true), SourceLoc::unknown()),
            Ok(Some(Val::Bool(true)))
        ));
        assert!(matches!(
            clint_disabled_within_mmio_result(true, Val::<B64>::Bool(false), SourceLoc::unknown()),
            Ok(Some(Val::Bool(false)))
        ));
        assert!(clint_disabled_within_mmio_result(false, Val::<B64>::Bool(true), SourceLoc::unknown()).is_err());
    }

    #[test]
    fn pmp_off_assumption_does_not_require_concrete_privilege() {
        assert!(pmp_off_assumption_ignores_privilege(&Val::<B64>::Symbolic(Sym::from_u32(1))));
        let computation = pmp_check_off_computation::<B64>();
        assert!(matches!(computation.parts.is_some, SmtExp::Bool(false)));
        assert!(computation.parts.fault.is_none());
        assert!(computation.effects.is_empty());
    }

    #[test]
    fn phys_access_priority_prefers_access_and_right_tie() {
        assert_eq!(alignment_or_access_fault_priority_name("zE_Load_Addr_Align"), Some(0));
        assert_eq!(alignment_or_access_fault_priority_name("zE_Load_Access_Fault"), Some(1));
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_Load_Addr_Align"),
            Some("zE_Load_Access_Fault"),
        );
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_Load_Access_Fault"),
            Some("zE_Load_Access_Fault"),
        );
        assert_eq!(
            highest_priority_alignment_or_access_fault_name("zE_Load_Access_Fault", "zE_SAMO_Access_Fault"),
            Some("zE_SAMO_Access_Fault"),
        );
    }

    #[test]
    fn symbolic_phys_access_exception_requests_fallback() {
        let fault: Val<B64> = Val::SymbolicCtor(Sym::from_u32(1), HashMap::default());
        let result = concrete_exception_ctor_payload_or_fallback(&fault, "test", SourceLoc::unknown()).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn symbolic_phys_access_fault_choice_requests_fallback() {
        let pmp = OptionExceptionParts {
            is_some: SmtExp::Var(Sym::from_u32(1)),
            fault: Some(Val::Ctor(Name::from_u32(100), Box::new(Val::<B64>::Unit))),
        };
        let pma = OptionExceptionParts {
            is_some: SmtExp::Var(Sym::from_u32(2)),
            fault: Some(Val::Ctor(Name::from_u32(101), Box::new(Val::<B64>::Unit))),
        };
        assert!(phys_access_fault_selection_requires_fallback(&pmp, &pma));
    }

    #[test]
    fn builtin_metadata_keeps_fallback_calls_at_runtime() {
        assert_eq!(Buildin::from_riscv_function("range_subset"), Some(Buildin::RiscvRangeSubset));
        assert_eq!(Buildin::from_riscv_function("pmpCheck"), Some(Buildin::RiscvPmpCheck));
        assert_eq!(Buildin::from_riscv_function("vmem_read_addr"), Some(Buildin::RiscvVmemReadAddr));
        assert_eq!(Buildin::from_riscv_function("unknown"), None);
    }

    #[test]
    fn clint_load_exact_hit_table_matches_sail_branches() {
        assert_eq!(clint_load_exact_hit(0x0000, 4), Some(ClintLoadHit::Msip));
        assert_eq!(clint_load_exact_hit(0x0000, 8), Some(ClintLoadHit::Msip));
        assert_eq!(clint_load_exact_hit(0x4000, 4), Some(ClintLoadHit::MtimecmpLow));
        assert_eq!(clint_load_exact_hit(0x4000, 8), Some(ClintLoadHit::MtimecmpFull));
        assert_eq!(clint_load_exact_hit(0x4004, 4), Some(ClintLoadHit::MtimecmpHigh));
        assert_eq!(clint_load_exact_hit(0xbff8, 4), Some(ClintLoadHit::MtimeLow));
        assert_eq!(clint_load_exact_hit(0xbff8, 8), Some(ClintLoadHit::MtimeFull));
        assert_eq!(clint_load_exact_hit(0xbffc, 4), Some(ClintLoadHit::MtimeHigh));
        assert_eq!(clint_load_exact_hit(0x4004, 8), None);
        assert_eq!(clint_load_exact_hit(0x0004, 4), None);
    }
}
