// --- TOML
// title = "五个叶子按 a、b、c 分三组"
// intent = "五个互斥叶子各给出 a、b、a、b、c，核对完整的三组输入。"
// inputs = { path_x = 3 }
// expect_paths_unmerged = 5
// expect_paths_merged = 3
// must_merge = "两个 a 同组，两个 b 同组。"
// must_not_merge = "严格字符串下 a、b、c 各有一个继续执行的出口。"
// status = "ready"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(3)
register out_value : bits(2)

function prop(x : bits(3)) -> bool = {
  path_x = x;
  let label = if x[2 .. 1] == 0b00 then {
    if x[0 .. 0] == 0b0 then "a" else "b"
  } else {
    if x[2 .. 2] == 0b1 then "c" else if x[0 .. 0] == 0b0 then "a" else "b"
  };
  out_value = if label == "a" then 0b00 else if label == "b" then 0b01 else 0b10;
  out_value == (x[2 .. 2] @ and_vec(not_vec(x[2 .. 2]), x[0 .. 0]))
}
