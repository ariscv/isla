// --- TOML
// title = "比较相同具体字符串"
// intent = "在汇合后比较相同具体字符串，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两臂都提供同一个字符串。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : string = if x == 0b0 then "cat" else "cat";
  out_value = v == "cat";
  out_value == true
}
