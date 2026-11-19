// --- TOML
// sequential_ram = true
// title = "写入一或两字节"
// intent = "同一条写操作通过符号长度选取待写数据，事件保留相应字节。"
// inputs = { path_mode = 1 }
// must_merge = "两种输入各写一次，同一地址的不同长度和数据由守卫区分。"
// ---
default Order dec
$include <prelude.sail>

val store = {c: "platform_write_mem"} : forall 'n, 'n in {1, 2}. (unit, int, bits(64), int('n), bits(8 * 'n)) -> bool
register path_mode : bits(1)
register out_value : bits(1)

function prop(mode : bits(1)) -> bool = {
  path_mode = mode;
  let 'size = if mode == 0b0 then 1 else 2;
  let data = 0xABCD[8 * size - 1 .. 0];
  let _ = store((), 64, 0x0000000000001000, size, data);
  out_value = mode;
  true
}
