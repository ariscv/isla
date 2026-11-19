// --- TOML
// title = "合并后继续消费不同的具体字符串"
// intent = "同一汇合点应保留两种字符串，并在后续比较时选中对应值。"
// inputs = { path_x = 1 }
// must_merge = "字符串的选择由输入决定，并能在后续比较时恢复。"
// status = "xfail"
// reason = "默认配置未启用具体值守卫合并，字符串差异保留两条路径。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let label = if x == 0b0 then "zero" else "one";
  out_value = if label == "zero" then 0b0 else 0b1;
  out_value == x
}
