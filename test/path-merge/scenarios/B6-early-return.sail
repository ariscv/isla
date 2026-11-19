// --- TOML
// title = "臂内提前返回"
// intent = "核对提前返回和走到函数末尾的两条调用路径。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "返回调用点时两出口都交付一位结果。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

function pick(x : bits(1)) -> bits(1) = {
  if x == 0b0 then return 0b0;
  0b1
}

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  out_value = pick(x);
  out_value == x
}
