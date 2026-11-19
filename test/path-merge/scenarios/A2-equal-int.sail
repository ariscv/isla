// --- TOML
// title = "读回相同具体整数"
// intent = "在汇合后读回相同具体整数，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两臂的整数均为 3。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(3)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : range(0, 7) = if x == 0b0 then 3 else 3;
  out_value = get_slice_int(3, v, 0);
  out_value == 0b011
}
