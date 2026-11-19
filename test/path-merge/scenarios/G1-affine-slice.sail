// --- TOML
// title = "层号乘加得到同宽切片"
// intent = "四个层号取页号的不同部分，结果都为 4 位。"
// inputs = { path_level = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "高低端点共用一个层号，四个结果位宽相同。"
// ---
default Order dec
$include <prelude.sail>
mapping levels : bits(2) <-> {0, 1, 2, 3} = {
  0b00 <-> 0, 0b01 <-> 1, 0b10 <-> 2, 0b11 <-> 3,
}
register path_level : bits(2)
register out_value : bits(4)
function prop(x : bits(2)) -> bool = {
  path_level = x;
  let 'level = levels(x);
  let vpn = 0xabcd;
  out_value = vpn[(level + 1) * 4 - 1 .. level * 4];
  let shifted = sail_shiftright(vpn, unsigned(x) * 4);
  out_value == shifted[3 .. 0]
}
