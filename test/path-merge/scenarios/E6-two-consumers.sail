// --- TOML
// title = "同一个宽度同时用于切片和整数比较"
// intent = "同时观测切片的符号位和独立的宽度比较，四种输入有四种不同输出。"
// inputs = { path_mode = 2 }
// registers = ["wide"]
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "两个消费者共享一个模式，第二次消费只能沿用同一个宽度，四个互斥输入最终可共用一条路径。"
// status = "xfail"
// reason = "两次消费保持宽度一致，两种配置最终均为四条，尚未合回一条。"
// ---
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register wide : bool
register out_value : bits(1)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let 'w = mode_width(m);
  let addr = 0x0000800080000000;
  let s : bits(64) = sail_sign_extend(addr[w - 1 .. 0], 64);
  out_value = s[63 .. 63];
  wide = w >= 48;
  (out_value == not_vec(m[0 .. 0])) & (wide == (m[1 .. 1] == 0b1))
}
