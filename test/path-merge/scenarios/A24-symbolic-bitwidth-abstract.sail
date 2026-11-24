// --- TOML
// title = "抽象事件的变长实参按可行位宽拆分"
// intent = "在 A23 的掩码计算中调用抽象原语，检查四个可行位宽对应的路径及掩码结果。"
// inputs = { path_level = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 4
// ---
default Order dec
$include <prelude.sail>

$abstract audit_observe
val audit_observe = "audit_observe" : forall 'n, 'n >= 0. bits('n) -> unit

register path_level : bits(2)
register out_value : bits(45)

function level_mask_vpn(level : bits(2)) -> bits(45) = {
  let shift = unsigned(level) * 9;
  let levelMask = sail_ones(shift);
  audit_observe(levelMask);
  let vpn : bits(45) = sail_ones(45);
  vpn & not_vec(sail_zero_extend(levelMask, 45))
}

function prop() -> bool = {
  out_value = level_mask_vpn(path_level);
  let reference = sail_shiftleft(sail_ones(45), unsigned(path_level) * 9);
  out_value == reference
}
