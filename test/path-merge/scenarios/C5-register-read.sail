// --- TOML
// title = "从两臂读取不同寄存器"
// intent = "检查两份入口寄存器值都能在对应守卫下读回。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "读操作不改变后态，输出位宽相同。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)
register S : bits(1)

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  R = y;
  S = not_vec(y);
  out_value = if x == 0b0 then R else S;
  out_value == xor_vec(x, y)
}
