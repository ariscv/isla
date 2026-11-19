// --- TOML
// title = "失败断言是独立错误出口"
// intent = "区分 x=0 的断言失败与 x=1 的正常完成。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 1
// expect_paths_merged = 1
// must_merge = "所有到达正常后继的输入共用一条完成路径；本例的正常域只有 x=1。"
// must_not_merge = "x=0 的失败断言保留为独立错误终态，正常路径数只计 x=1。"
// status = "todo"
// reason = "merge-principle-audit.md §7（可达错误）：property 缺少可逐项核对的错误种类和守卫。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then assert(false);
  out_value = x;
  out_value == 0b1
}
