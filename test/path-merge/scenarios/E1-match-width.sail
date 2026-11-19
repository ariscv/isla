// --- TOML
// title = "直接返回 match 选出的整数"
// intent = "检查四种模式与返回整数的一一对应。"
// inputs = { path_mode = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "四个互斥输入抵达同一个返回点，一个带守卫的整数即可表示全部结果。"
// status = "xfail"
// reason = "严格合并保留四个整数，开启具体值合并后读回整数仍得到四条完成路径。"
// ---
default Order dec
$include <prelude.sail>
function mode_width(m : bits(2)) -> {32, 39, 48, 57} =
  match m { 0b00 => 32, 0b01 => 39, 0b10 => 48, _ => 57 }
register path_mode : bits(2)
register out_value : bits(6)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  out_value = get_slice_int(6, w, 0);
  let table = sail_shiftright(0x39302720, 8 * unsigned(m));
  out_value == table[5 .. 0]
}
