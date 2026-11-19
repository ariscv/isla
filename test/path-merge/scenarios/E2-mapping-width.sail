// --- TOML
// title = "直接返回 mapping 正向映射的整数"
// intent = "检查 Sail 生成的 forwards 函数能否合并四个返回值。"
// inputs = { path_mode = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "正向映射是全函数，四个整数可共用一个带守卫的返回槽。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register out_value : bits(6)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  out_value = get_slice_int(6, w, 0);
  let table = sail_shiftright(0x39302720, 8 * unsigned(m));
  out_value == table[5 .. 0]
}
