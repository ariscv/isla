// --- TOML
// title = "分支内同名 let"
// intent = "核对两个作用域中的同名绑定只影响各自的结果。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两臂的局部绑定离开作用域后只留返回位。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  out_value = if x == 0b0 then { let b = not_vec(y); b } else { let b = y; b };
  out_value == xor_vec(not_vec(x), y)
}
