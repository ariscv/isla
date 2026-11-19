// --- TOML
// title = "单菱形的共同后继"
// intent = "两条边选择一位数据，在同一个取反操作前汇合。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "共同后继只需要被选择的一位。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v = if x == 0b0 then 0b1 else 0b0;
  out_value = not_vec(v);
  out_value == x
}
