// --- TOML
// title = "两笔写的顺序相反"
// intent = "逐输入比较两个地址的写入先后。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "按固定地址的访问次序审阅，两种相反次序分别保留。"
// status = "ready"
// ordered_events = true
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
