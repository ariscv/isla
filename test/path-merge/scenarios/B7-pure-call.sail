// --- TOML
// title = "单臂调用纯函数"
// intent = "只有 x=1 时调用纯函数计算翻转位。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "调用没有额外效应且返回位宽相同。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

function flip(b : bits(1)) -> bits(1) = not_vec(b)

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  out_value = if x == 0b0 then y else flip(y);
  out_value == xor_vec(x, y)
}
