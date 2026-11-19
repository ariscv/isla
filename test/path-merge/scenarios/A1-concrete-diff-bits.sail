// --- TOML
// title = "合并两个不同的等宽位向量"
// intent = "让一次汇合保留两个具体位向量各自对应的输入。"
// inputs = { path_x = 1 }
// must_merge = "两个值的位宽相同，一条路径可按守卫选择值。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  out_value = if x == 0b0 then 0b10 else 0b11;
  out_value == (0b1 @ x)
}
