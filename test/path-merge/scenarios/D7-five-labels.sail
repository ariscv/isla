// --- TOML
// title = "五个叶子的三个不同字符串合成一组"
// intent = "核对五个叶子的字符串投影和覆盖全部输入的一条守卫。"
// inputs = { path_x = 3 }
// expect_paths_unmerged = 5
// expect_paths_merged = 1
// must_merge = "五个叶子的 a、b、c 可按原输入选择。所有八个输入覆盖同一条路径，字符串比较仍能区分三个值。"
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
