// --- TOML
// title = "合并两层菱形分叉"
// intent = "完成内层和外层汇合，并保留四个输入对应的结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 4
// must_merge = "四种结果都是两位位向量，且状态写入相同。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(2)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  out_value = if x == 0b0 then {
    if y == 0b0 then 0b00 else 0b01
  } else {
    if y == 0b0 then 0b10 else 0b11
  };
  out_value == (x @ y)
}
