// --- TOML
// title = "按模式选择 VPN 每级位数后切片"
// intent = "取第 1 级 VPN 下标，检查 Sv32 的 10 位和其它模式的 9 位。"
// inputs = { path_mode = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "即使选择每级位数时需要分为两组，取出下标并扩展到 10 位后也能再次汇合。"
// status = "xfail"
// reason = "9 位的三个输入已合回一条。9 位和 10 位切片仍分别继续，最终有两条路径。"
// ---
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register out_value : bits(10)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  let 'n = if w == 32 then 10 else 9;
  let vpn = 0x000abc00;
  out_value = sail_zero_extend(vpn[2 * n - 1 .. n], 10);
  let table = sail_shiftright(0x015e015e015e02af, 16 * unsigned(m));
  out_value == table[9 .. 0]
}
