// --- TOML
// title = "四个片段按兼容性汇合"
// intent = "两条结果路径各取两个外层臂的片段，并保留内层字符串区别。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 2
// must_merge = "对同一个内层输入，两臂的字符串相同且结果位宽一致。"
// must_not_merge = "默认的具体值表示要求两个活跃字符串保持在各自的组内。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(2)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  var label : string = "init";
  let high : bits(1) = if x == 0b0 then {
    label = if y == 0b0 then "left" else "right";
    0b0
  } else {
    label = if y == 0b0 then "left" else "right";
    0b1
  };
  out_value = high @ (if label == "left" then 0b0 else 0b1);
  out_value == (x @ y)
}
