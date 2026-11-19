// --- TOML
// title = "比较不同枚举成员"
// intent = "在汇合后比较不同枚举成员，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "可用有限标签按输入选出枚举成员。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

enum Colour = { Red, Blue }

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : Colour = if x == 0b0 then Red else Blue;
  out_value = match v { Red => false, Blue => true };
  out_value == (x == 0b1)
}
