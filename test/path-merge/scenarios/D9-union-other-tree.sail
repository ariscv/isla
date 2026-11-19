// --- TOML
// title = "P(\"a\")、Q(())、P(\"c\") 的分组"
// intent = "只交换判别条件的嵌套次序，检查同一输入映射下的三个目标组。"
// inputs = { path_x = 2 }
// expect_paths_unmerged = 3
// expect_paths_merged = 3
// must_not_merge = "待用户审核：严格标签与负载下 P 的两种字符串各占一组，Q 单独一组，避免任选一个 P 接纳 Q。"
// merge_concrete_values = false
// status = "xfail"
// reason = "实测 Q 与 P(「c」) 同组，P(「a」) 独立；守卫划分少一组。"
// ---
default Order dec
$include <prelude.sail>

union U = { P : string, Q : unit }

register path_x : bits(2)
register out_value : bits(2)

function prop(x : bits(2)) -> bool = {
  path_x = x;
  let v : U = if x == 0b00 then P("a") else if x == 0b01 then Q() else P("c");
  out_value = match v { Q() => 0b01, P(s) => if s == "a" then 0b00 else 0b10 };
  out_value == (x[1 .. 1] @ and_vec(not_vec(x[1 .. 1]), x[0 .. 0]))
}
