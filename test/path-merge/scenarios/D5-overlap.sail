// --- TOML
// title = "外层两臂的标签集合分别是 {b,c} 和 {c,d}"
// intent = "核对两个 c 跨外臂汇合且只覆盖(0,1) 和 (1,0)。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 3
// must_merge = "两个 c 有相同活跃字符串，合成一条。"
// must_not_merge = "严格字符串口径保留 b 与 d 各一条，二者都不能进入 c 组。"
// merge_concrete_values = false
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
