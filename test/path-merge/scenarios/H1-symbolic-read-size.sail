// --- TOML
// title = "读取一或两字节"
// intent = "每个输入执行一次对应长度的读，扩展后的值与读事件的数据一致。"
// inputs = { path_mode = 1, path_byte = 8 }
// must_merge = "读事件各自保留长度和守卫，扩展成同宽的结果可以汇合。"
// ---
default Order dec
$include <prelude.sail>

val load = {c: "platform_read_mem"} : forall 'n, 'n in {1, 2}. (unit, int, bits(64), int('n)) -> bits(8 * 'n)
val "assume" : bool -> unit
register path_mode : bits(1)
register path_byte : bits(8)
register out_value : bits(16)

function prop(mode : bits(1), byte : bits(8)) -> bool = {
  path_mode = mode;
  path_byte = byte;
  let 'size = if mode == 0b0 then 1 else 2;
  let data = load((), 64, 0x0000000000001000, size);
  out_value = sail_zero_extend(data, 16);
  assume(out_value == (0x00 @ byte));
  out_value == (0x00 @ byte)
}
