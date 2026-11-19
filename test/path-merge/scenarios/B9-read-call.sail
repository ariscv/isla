// --- TOML
// title = "臂内调用读寄存器函数"
// intent = "比较通过调用和直接读取同一寄存器的结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两臂都读取 R 一次，最终值可条件选择。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)
function getR() -> bits(1) = R

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  R = y;
  out_value = if x == 0b0 then getR() else not_vec(R);
  out_value == xor_vec(x, y)
}
