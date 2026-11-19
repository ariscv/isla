// --- TOML
// initialized_registers = ["R"]
// title = "单臂初始化寄存器"
// intent = "在同一出口区分单臂写入与另一臂保留的未初始化槽。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "按 x 保留 R 的初始化状态。x=0 时 R 已初始化为 1，x=1 时仍未初始化，首次读取才取得该臂的入口初值。"
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then R = 0b1;
  out_value = x;
  true
}
