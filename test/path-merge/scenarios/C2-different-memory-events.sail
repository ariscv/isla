// --- TOML
// sequential_ram = true
// title = "保留不同数量的访存事件"
// intent = "保留一臂的一次写和另一臂的两次写，以及各自的地址和数据。"
// inputs = { path_x = 1 }
// expect_paths_merged = 1
// must_merge = "一条路径保留各臂的一笔或两笔写，以及原有次序。"
// ---
default Order dec
$include <prelude.sail>
val store = {c: "platform_write_mem"} : (unit, int, bits(64), int, bits(8)) -> bool

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then {
    let _ = store((), 64, 0x0000000000001000, 1, 0xA1);
    ()
  } else {
    let _ = store((), 64, 0x0000000000001000, 1, 0xB2);
    let _ = store((), 64, 0x0000000000001001, 1, 0xC3);
    ()
  };
  out_value = x;
  true
}
