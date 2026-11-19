// --- TOML
// title = "读取定长向量的元素"
// intent = "在汇合后读取定长向量的元素，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "同长向量各位置可独立选择。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : vector(2, bits(1)) = if x == 0b0 then [0b1, 0b0] else [0b1, 0b1];
  out_value = v[1] @ v[0];
  out_value == (0b1 @ x)
}
