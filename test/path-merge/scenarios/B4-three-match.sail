// --- TOML
// title = "三路 match 共用后继"
// intent = "穷举 00、01 和高位为 1 的默认分支。"
// inputs = { path_x = 2 }
// expect_paths_unmerged = 3
// expect_paths_merged = 1
// must_merge = "三臂都提供两位结果，默认臂保留 x。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(2)
register out_value : bits(2)

function prop(x : bits(2)) -> bool = {
  path_x = x;
  out_value = match x { 0b00 => 0b11, 0b01 => 0b10, _ => x };
  out_value == xor_vec(x, not_vec(x[1 .. 1]) @ not_vec(x[1 .. 1]))
}
