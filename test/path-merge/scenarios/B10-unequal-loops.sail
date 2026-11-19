// --- TOML
// title = "两臂执行不同次数的有界循环"
// intent = "左臂翻转一次，右臂翻转两次，在循环结束后读回局部值。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "循环结束后只保留最终一位，且没有外部效应。"
// status = "xfail"
// reason = "两种迭代次数结束后仍有两条完成路径，最终翻转位核对通过。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  var b = 0b0;
  if x == 0b0 then {
    foreach (i from 0 to 0) { b = not_vec(b) }
  } else {
    foreach (i from 0 to 1) { b = not_vec(b) }
  };
  out_value = b;
  out_value == not_vec(x)
}
