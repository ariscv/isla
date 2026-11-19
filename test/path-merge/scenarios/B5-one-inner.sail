// --- TOML
// title = "只在外层一臂再分叉"
// intent = "在内层和外层汇合后检查三个叶子的结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 3
// expect_paths_merged = 1
// must_merge = "外层跳过内层时直接给出零。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  out_value = if x == 0b0 then 0b0 else {
    if y == 0b0 then 0b0 else 0b1
  };
  out_value == and_vec(x, y)
}
