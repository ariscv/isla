// --- TOML
// title = "读回具体与符号整数"
// intent = "在汇合后读回具体与符号整数，用输入核对结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "符号整数与单个具体值可用相同整数位宽按守卫选择。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(3)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let v : range(0, 7) = if x == 0b0 then 3 else unsigned(y);
  out_value = get_slice_int(3, v, 0);
  out_value == (0b0 @ not_vec(x) @ or_vec(not_vec(x), y))
}
