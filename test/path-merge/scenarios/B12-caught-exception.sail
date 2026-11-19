// --- TOML
// title = "调用方捕获臂内异常"
// intent = "把被捕获的异常与普通返回投影为不同的一位。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "异常被捕获后有共同的正常后继。"
// status = "xfail"
// reason = "merge-principle-audit.md §5（异常出口与调用方延续）：捕获异常的分支已正常返回，在共同后继仍与普通返回分别完成。"
// ---
default Order dec
$include <prelude.sail>

union exception = { Stop : unit }
function maybe(x : bits(1)) -> bits(1) = if x == 0b1 then throw(Stop()) else 0b0

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  out_value = try { maybe(x) } catch { Stop() => 0b1 };
  out_value == x
}
