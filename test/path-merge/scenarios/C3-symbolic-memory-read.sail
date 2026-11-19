// --- TOML
// title = "保留符号访存读值"
// intent = "在汇合后继续使用实际访存产生的符号字节，并保留读事件。"
// inputs = { path_x = 1, path_mem = 1 }
// must_merge = "两臂读取同一个已取得的字节，后续只选择返回位。"
// ---
default Order dec
$include <prelude.sail>
val load = {c: "platform_read_mem"} : (unit, int, bits(64), int) -> bits(8)
val "assume" : bool -> unit

register path_x : bits(1)
register path_mem : bits(1)
register out_value : bits(2)

function prop(x : bits(1)) -> bool = {
  let byte = load((), 64, 0x0000000000001000, 1);
  assume(byte[7 .. 1] == 0b0000000);
  path_x = x;
  path_mem = byte[0 .. 0];
  let high = if x == 0b0 then 0b0 else 0b1;
  out_value = high @ byte[0 .. 0];
  out_value == (x @ path_mem)
}
