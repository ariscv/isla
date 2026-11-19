// --- TOML
// title = "同一寄存器接收两种值"
// intent = "把同一寄存器上的条件写入合成一条路径，并保留最终读回值。"
// inputs = { path_x = 1 }
// registers = ["X"]
// must_merge = "两臂对同一寄存器写入等宽位向量。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(2)
register X : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then X = 0b01 else X = 0b11;
  out_value = X;
  out_value == (x @ 0b1)
}
