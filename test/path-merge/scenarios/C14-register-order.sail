// --- TOML
// title = "严格寄存器写序成环"
// intent = "检查 R 后 S 和 S 后 R 的两条有序路径。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "两种写序相互矛盾，单一固定寄存器次序不能满足二者。"
// status = "ready"
// ordered_events = true
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
  if x == 0b0 then { R = 0b0; S = 0b1 } else { S = 0b0; R = 0b1 };
  out_value = R @ S;
  out_value == (x @ not_vec(x))
}
