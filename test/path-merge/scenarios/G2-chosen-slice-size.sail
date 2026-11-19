// --- TOML
// title = "独立选择层号与每级位数"
// intent = "两类位宽分别取四个层级，切片扩展后每个输入都得到相应的位。"
// inputs = { path_mode = 3 }
// expect_paths_unmerged = 8
// expect_paths_merged = 1
// must_merge = "同宽切片可直接汇合，4 位和 5 位结果扩展后也可汇合。"
// ---
default Order dec
$include <prelude.sail>
mapping levels : bits(2) <-> {0, 1, 2, 3} = {
  0b00 <-> 0, 0b01 <-> 1, 0b10 <-> 2, 0b11 <-> 3,
}
register path_mode : bits(3)
register out_value : bits(5)
function prop(m : bits(3)) -> bool = {
  path_mode = m;
  let 'level = levels(m[1 .. 0]);
  let 'size = if m[2 .. 2] == 0b0 then 4 else 5;
  let vpn = 0xabcde;
  out_value = sail_zero_extend(vpn[(level + 1) * size - 1 .. level * size], 5);
  let r4 = sail_shiftright(vpn, unsigned(m[1 .. 0]) * 4);
  let r5 = sail_shiftright(vpn, unsigned(m[1 .. 0]) * 5);
  let expected = if m[2 .. 2] == 0b0 then 0b0 @ r4[3 .. 0] else r5[4 .. 0];
  out_value == expected
}
