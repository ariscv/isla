// --- TOML
// title = "读取等长列表的首项"
// intent = "在汇合后读取等长列表的首项，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两个列表都只有一个元素，其值可由守卫选择。"
// ---
default Order dec
$include <prelude.sail>

val push_bit = {c: "cons"} : (bits(1), list(bits(1))) -> list(bits(1))

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : list(bits(1)) = if x == 0b0 then push_bit(0b0, [||]) else push_bit(0b1, [||]);
  out_value = match v { hd :: [||] => 0b1 @ hd, _ => 0b00 };
  out_value == (0b1 @ x)
}
