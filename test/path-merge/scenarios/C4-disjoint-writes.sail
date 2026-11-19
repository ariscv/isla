// --- TOML
// title = "两臂写不同寄存器"
// intent = "比较执行结束时两个寄存器的完整后态。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "每个寄存器在未写分支都有确定的入口值。"
// status = "ready"
// registers = ["R", "S"]
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)
register S : bits(1)

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  R = 0b0;
  S = 0b0;
  if x == 0b0 then R = 0b1 else S = 0b1;
  out_value = R @ S;
  out_value == (not_vec(x) @ x)
}
