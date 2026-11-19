// --- TOML
// title = "四个片段按兼容性汇合"
// intent = "核对四个输入在共同出口各自得到 x @ y。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "带守卫的字符串由 y 选择，结果高位由 x 选择，四个输入共用一条路径。"
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
