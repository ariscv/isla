// --- TOML
// title = "两笔写的顺序相反"
// intent = "逐输入比较两个地址的写入先后。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "一条路径按 x 投影两笔内存写，保留各自的字节与先后。x=0 先写 0x1000，x=1 先写 0x1001。"
// status = "xfail"
// reason = "total-merge-design.md §4（有序内存后缀）：当前直接写留下两条路径，缺少在一个出口按 x 选择并投影两笔写的有序后缀。"
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
    let _ = store((), 64, 0x0000000000001001, 1, 0xA1);
    ()
  } else {
    let _ = store((), 64, 0x0000000000001001, 1, 0xA1);
    let _ = store((), 64, 0x0000000000001000, 1, 0xA1);
    ()
  };
  out_value = x;
  true
}
