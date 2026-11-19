// --- TOML
// title = "区分常量位和符号位"
// intent = "在汇合后区分常量位和符号位，用输入核对结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "常量零和符号位可以放入同宽 ITE。"
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
  let v : bits(1) = if x == 0b0 then 0b0 else y;
  out_value = v;
  out_value == and_vec(x, y)
}
