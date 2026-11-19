// --- TOML
// title = "比较同一标签的不同字符串"
// intent = "在汇合后比较同一标签的不同字符串，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "严格字符串口径下，同一 P 的互异负载各保留一条。"
// merge_concrete_values = false
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

union U = { P : string }

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : U = if x == 0b0 then P("a") else P("c");
  out_value = match v { P(s) => s == "c" };
  out_value == (x == 0b1)
}
