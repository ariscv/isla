// --- TOML
// title = "外层两臂的标签集合分别是 {b,c} 和 {c,d}"
// intent = "核对两外臂的字符串都能在同一出口按原输入比较。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "按 x、y 选择字符串 b、c 或 d，两个 c 取同一值，四个输入共用一个出口。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(2)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let label = if x == 0b0 then {
    if y == 0b0 then "b" else "c"
  } else {
    if y == 0b0 then "c" else "d"
  };
  out_value = if label == "b" then 0b00 else if label == "c" then 0b01 else 0b10;
  out_value == (and_vec(x, y) @ xor_vec(x, y))
}
