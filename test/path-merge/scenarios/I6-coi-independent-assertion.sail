// --- TOML
// title = "出口切除独立的断言"
// intent = "一组位向量等式限定独立自由输入，另一组等式限定分支与输出。启用约束锥切片时应实际省略前一组约束。"
// inputs = { path_x = 8 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// require_coi_slice = true
// must_merge = "两个出口的宽度与布局相同，可用 ITE 合并。"
// must_not_merge = "无。"
// ---
default Order dec
$include <prelude.sail>
val "assume" : bool -> unit

register path_x : bits(8)
register out_value : bits(8)

function constrain_independent() -> unit = {
  let scratch : bits(8) = undefined;
  assume(scratch != 0x00)
}

function prop(x : bits(8)) -> bool = {
  path_x = x;
  constrain_independent();
  assume(x != 0xff);
  out_value = if x == 0x12 then 0x01 else 0x02;
  out_value == (if x == 0x12 then 0x01 else 0x02)
}
