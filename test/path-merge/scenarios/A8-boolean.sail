// --- TOML
// title = "读回不同布尔值"
// intent = "在汇合后读回不同布尔值，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "单个布尔表达式可以表示两臂的真值。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : bool = if x == 0b0 then false else true;
  out_value = v;
  out_value == (x == 0b1)
}
