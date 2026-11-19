// --- TOML
// title = "只在一个分支读取"
// intent = "以 y 指定可读字节的低位，比较实际读事件及返回字节。"
// inputs = { path_x = 1, path_y = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "目标为每个输入按事件守卫投影，x=1 恰好读一次，x=0 零次。"
// status = "todo"
// reason = "total-merge-design.md §4（条件访存）：现有正文在 x=0 读、x=1 跳过，与裁定的输入极性相反。导出还缺每笔读的生效守卫，须分别核实次数、地址和读值。"
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
