// --- TOML
// title = "读回不同具体整数"
// intent = "在汇合后读回不同具体整数，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两个三位非负整数都能无损表示为有守卫的整数。"
// status = "xfail"
// reason = "total-merge-design.md §3（整数消费）：3 和 7 已合并，切片前的整数转换在区域外按守卫重试，最终有两条路径。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(3)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : range(0, 7) = if x == 0b0 then 3 else 7;
  out_value = get_slice_int(3, v, 0);
  out_value == (x @ 0b11)
}
