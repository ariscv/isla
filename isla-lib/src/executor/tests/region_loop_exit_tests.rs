use super::loop_segment_tests::{equivalent_scalar_paths, scan_paths_with_limits};
use super::*;

#[test]
fn region_loop_exit_keeps_register_writes_across_rounds_with_small_budget() {
    let mut shared = empty_shared_state();
    let register = shared.symtab.intern("zloop_exit_state");
    shared.registers.insert(register, Ty::I128);
    let limits = ExecutionLimits::default();
    let off = scan_paths_with_limits(&shared, 8, 40, Some(register), limits.clone());
    assert_eq!(off.len(), 9);
    for strategy in [crate::config::MergeStrategy::Recursive, crate::config::MergeStrategy::Flat] {
        let mut on_limits = limits.clone().with_path_merging(true);
        on_limits.merge_strategy = strategy;
        let on = scan_paths_with_limits(&shared, 8, 40, Some(register), on_limits);
        assert_eq!(on.len(), 1, "同一循环的各轮返回必须到达同一出口");
        equivalent_scalar_paths(&off, &on, 8);
        equivalent_register_paths(&off, &on, 8);
    }
}
