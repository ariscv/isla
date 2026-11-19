// --- TOML
// title = "辨别不同位宽"
// intent = "在汇合后辨别不同位宽，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "按 x 保留位宽和值。length 在 x=0 时读到 4，在 x=1 时读到 8。"
// status = "xfail"
// reason = "total-merge-design.md §2（变宽位向量）：当前值合并要求位宽相同，4 位和 8 位分别完成。"
// ---
default Order dec
$include <prelude.sail>

type packet = { 'n, 'n in {4, 8}. bits('n) }

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : packet = if x == 0b0 then 0xA else 0xAA;
  out_value = length(v) == 8;
  out_value == (x == 0b1)
}
