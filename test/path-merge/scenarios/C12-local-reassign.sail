// --- TOML
// title = "覆盖局部变量"
// intent = "两个分支改写同一个局部变量再读回。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "旧值已被覆盖且无外部写。"
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
  var v = y;
  if x == 0b0 then v = not_vec(v) else v = 0b0;
  out_value = v;
  out_value == and_vec(not_vec(x), not_vec(y))
}
