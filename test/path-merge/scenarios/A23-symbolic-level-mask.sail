// --- TOML
// title = "超级页层级决定掩码位宽"
// intent = "按 add_to_TLB 的写法构造变长 levelMask，再将掩码和页号收束为定长。"
// inputs = { path_level = 2 }
// expect_paths_unmerged = 1
// expect_paths_merged = 1
// ---
default Order dec
$include <prelude.sail>

register path_level : bits(2)
register out_value : bits(45)

function level_mask_vpn(level : bits(2)) -> bits(45) = {
  let shift = unsigned(level) * 9;
  let levelMask = sail_ones(shift);
  let vpn : bits(45) = sail_ones(45);
  vpn & not_vec(sail_zero_extend(levelMask, 45))
}

function prop() -> bool = {
  out_value = level_mask_vpn(path_level);
  let reference = sail_shiftleft(sail_ones(45), unsigned(path_level) * 9);
  out_value == reference
}
