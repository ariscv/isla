// --- TOML
// title = "只在一个分支读取"
// intent = "以 y 指定可读字节的低位，比较实际读事件及返回字节。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "另一臂没有读事件，无条件读会改变执行迹。"
// status = "todo"
// reason = "两种位宽实跑时 off 通过；合并路径的 JSON 缺每笔读的生效守卫，未执行那笔读的数据也被要求唯一。需按输入过滤事件后对照。"
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
    0x00
  };
  out_value = v[0 .. 0];
  out_value == and_vec(not_vec(x), y)
}
