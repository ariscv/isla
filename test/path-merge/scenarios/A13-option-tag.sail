// --- TOML
// title = "辨别 Some 和 None"
// intent = "在汇合后辨别 Some 和 None，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "可选值的标签由 x 唯一决定，Some 的负载为一位。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

$include <option.sail>

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : option(bits(1)) = if x == 0b0 then None() else Some(0b1);
  out_value = match v { Some(b) => 0b1 @ b, None() => 0b00 };
  out_value == (x @ x)
}
