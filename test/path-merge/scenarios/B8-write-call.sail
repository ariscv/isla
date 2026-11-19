// --- TOML
// title = "臂内调用写寄存器函数"
// intent = "比较直接写与通过被调函数写的最终寄存器。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "两臂都写同一个一位寄存器一次。"
// status = "xfail"
// reason = "merge-principle-audit.md §2（被调函数的状态写）：臂内调用写 R，当前与直接写 R 的正常臂各自完成。"
// registers = ["R"]
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)
function put(b : bits(1)) -> unit = { R = b }

register path_x : bits(1)
register out_value : bits(1)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  if x == 0b0 then put(0b0) else R = 0b1;
  out_value = R;
  out_value == x
}
