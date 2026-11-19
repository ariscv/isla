// --- TOML
// title = "单臂赋值"
// intent = "省略 else 时核对未写分支的入口值。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "一位 ITE 可以选择旧值或新值。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  var v = 0b0;
  if x == 0b1 then v = 0b1;
  out_value = v;
  out_value == x
}
