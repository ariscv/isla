// --- TOML
// title = "失败断言是独立错误出口"
// intent = "区分 x=0 的断言失败与 x=1 的正常完成。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 1
// expect_paths_merged = 1
// must_not_merge = "一条正常路径外还应有一个错误叶子；错误不能吞掉正常结果。"
// status = "todo"
// reason = "property 将未捕获错误作为整次执行失败；需导出错误种类与守卫，分别断言正常和错误各一条。"
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
