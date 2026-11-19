// --- TOML
// title = "辨别不同位宽"
// intent = "在汇合后辨别不同位宽，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "宽度是后续 length 的输入；固定宽度的 ITE 不能同时保留两种宽度。"
// status = "ready"
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
