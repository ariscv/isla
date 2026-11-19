// --- TOML
// title = "三个 I64 片段 3、符号值、7"
// intent = "检查含符号桥接成员的三个守卫是否各有确定归属。"
// inputs = { path_x = 2, path_y = 1 }
// expect_paths_unmerged = 3
// expect_paths_merged = 3
// must_not_merge = "待用户审核：3 与 7 在严格整数口径下互斥，符号成员独立归类；三组的归属不依赖到达顺序。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(2)
register path_y : bits(1)
register out_value : bits(3)

function prop(x : bits(2), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let v : range(0, 7) = if x == 0b01 then unsigned(y) else if x == 0b00 then 3 else 7;
  out_value = get_slice_int(3, v, 0);
  let hi = x[1 .. 1];
  let lo = x[0 .. 0];
  out_value == (hi @ or_vec(hi, not_vec(lo)) @ or_vec(or_vec(hi, not_vec(lo)), y))
}
