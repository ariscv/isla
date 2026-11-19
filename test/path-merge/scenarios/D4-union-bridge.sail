// --- TOML
// title = "P(\"a\")、Q(())、P(\"c\") 的分组"
// intent = "改变源码嵌套次序后，四个输入仍共同覆盖同一条路径。"
// inputs = { path_x = 2 }
// expect_paths_unmerged = 3
// expect_paths_merged = 1
// must_merge = "标签按输入选择；P 域内按守卫取 a 或 c，Q 取单位负载。与 D9 的路径数和输入划分完全相同，唯一守卫覆盖 x=0…3。"
// ---
default Order dec
$include <prelude.sail>

union U = { P : string, Q : unit }

register path_x : bits(2)
register out_value : bits(2)

function prop(x : bits(2)) -> bool = {
  path_x = x;
  let v : U = if x == 0b01 then Q() else if x == 0b00 then P("a") else P("c");
  out_value = match v { Q() => 0b01, P(s) => if s == "a" then 0b00 else 0b10 };
  out_value == (x[1 .. 1] @ and_vec(not_vec(x[1 .. 1]), x[0 .. 0]))
}
