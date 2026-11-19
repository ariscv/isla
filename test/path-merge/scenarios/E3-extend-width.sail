// --- TOML
// title = "按映射位宽切片并比较两种扩展"
// intent = "将截取的低位分别零扩展和符号扩展到 64 位，两次比较的结果均可观测。"
// inputs = { path_mode = 2 }
// registers = ["zero_match"]
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "切片需要的四个位宽由同一输入决定，扩展后两个比较都产生固定位宽的结果。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register zero_match : bool
register out_value : bool
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let 'w = mode_width(m);
  let addr = 0x0000800000000000;
  let low = addr[w - 1 .. 0];
  let z : bits(64) = sail_zero_extend(low, 64);
  let s : bits(64) = sail_sign_extend(low, 64);
  zero_match = z == addr;
  out_value = s == addr;
  (zero_match == (m[1 .. 1] == 0b1)) & (out_value == (m == 0b11))
}
