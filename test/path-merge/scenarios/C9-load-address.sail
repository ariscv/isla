// --- TOML
// title = "两臂从不同地址读取"
// intent = "以 y 指定可读字节的低位，比较实际读事件及返回字节。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "每臂恰好一次读；相同种类和宽度允许按守卫选择地址与数据。"
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
  let v = if x == 0b0 then {
    let b = load((), 64, 0x0000000000001000, 1);
    assume(b == (0b0000000 @ y));
    b
  } else {
    let b = load((), 64, 0x0000000000001001, 1);
    assume(b == (0b0000000 @ y));
    b
  };
  out_value = v[0 .. 0];
  out_value == y
}
