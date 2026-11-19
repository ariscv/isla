// --- TOML
// title = "区分 union 的相同标签与相同负载"
// intent = "在汇合后区分 union 的相同标签与相同负载，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "标签与一位负载都可按输入确定。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

union U = { P : bits(1), Q : unit }

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : U = if x == 0b0 then P(0b1) else P(0b1);
  out_value = match v { P(b) => 0b1 @ b, Q() => 0b00 };
  out_value == 0b11
}
