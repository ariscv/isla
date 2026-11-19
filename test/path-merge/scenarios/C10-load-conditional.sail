// --- TOML
// title = "只在一个分支读取"
// intent = "x=1 恰好读取一次，x=0 不读取，读值的低位由 y 指定。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "使用读守卫保留 x=1 的单笔读和 x=0 的空序列。"
// ---
default Order dec
$include <prelude.sail>

val load = {c: "platform_read_mem"} : (unit, int, bits(64), int) -> bits(8)
val "assume" : bool -> unit

register path_x : bits(1)
register path_y : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let v = if x == 0b1 then {
    let b = load((), 64, 0x0000000000001000, 1);
    assume(b == (0b0000000 @ y));
    b
  } else {
    0x00
  };
  out_value = v[0 .. 0];
  out_value == and_vec(x, y)
}
