// --- TOML
// title = "单臂初始化寄存器"
// intent = "检查一个出口拥有已写值、另一个仍保留入口未初始化槽时的分组。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "严格初始化形状下两臂应保留各自的槽状态。"
// status = "todo"
// reason = "导出只有已初始化的标量值；需区分入口 Uninit 与 Init，并核对每组的槽状态。"
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
