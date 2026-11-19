// --- TOML
// title = "交换两个独立寄存器的写入次序"
// intent = "两臂各写 R 和 S 一次，比较交换写序后的完整寄存器后态。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "忽略独立寄存器的写入次序，按 x 恢复两次写的效果，最终 R=x、S=1−x。"
// status = "ready"
// registers = ["R", "S"]
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)
register S : bits(1)

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then { R = 0b0; S = 0b1 } else { S = 0b0; R = 0b1 };
  out_value = R @ S;
  out_value == (x @ not_vec(x))
}
