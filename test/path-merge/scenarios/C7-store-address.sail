// --- TOML
// title = "不同地址写相同字节"
// intent = "核对每个输入恰好一次写及其地址和字节。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "按输入选择写请求的地址，每个输入恰好产生原地址、原字节的一笔写。"
// status = "xfail"
// reason = "merge-principle-audit.md §2（直接内存写）：两笔候选请求的地址不同，当前模型保留两条写路径。"
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
    let _ = store((), 64, 0x0000000000001001, 1, 0xA1);
    ()
  };
  out_value = x;
  true
}
