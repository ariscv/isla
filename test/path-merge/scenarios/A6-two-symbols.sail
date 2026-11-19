// --- TOML
// title = "区分两个符号表达式"
// intent = "在汇合后区分两个符号表达式，用输入核对结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两个等宽表达式可用分支守卫选取。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let v : bits(1) = if x == 0b0 then y else not_vec(y);
  out_value = v;
  out_value == xor_vec(x, y)
}
