// --- TOML
// title = "读取结构体的两个字段"
// intent = "在汇合后读取结构体的两个字段，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "字段同型且 lo 的差异可以用一位表示。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

struct Pair = { hi : bits(1), lo : bits(1) }

register path_x : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : Pair = if x == 0b0 then struct { hi = 0b1, lo = 0b0 } else struct { hi = 0b1, lo = 0b1 };
  out_value = v.hi @ v.lo;
  out_value == (0b1 @ x)
}
