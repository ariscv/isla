// --- TOML
// title = "层号递减时的组合下标"
// intent = "以相同次数递减两种层号起点，逐次读取字符串向量的具体下标。"
// inputs = { path_mode = 2 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "循环次数一致，按下标分别读取字符串并保留各自守卫。"
// ---
default Order dec
$include <prelude.sail>
register path_mode : bits(2)
register out_value : bits(2)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let 'start = if m[0 .. 0] == 0b0 then 1 else 2;
  let 'stride = if m[1 .. 1] == 0b0 then 2 else 3;
  let data : vector(8, string) = ["clear", "set", "clear", "set", "clear", "set", "set", "clear"];
  out_value = 0b00;
  foreach (i from 1 downto 0) {
    let 'level = start + i - 1;
    let bit = if data[level * stride + 1] == "set" then 0b1 else 0b0;
    out_value = out_value[0 .. 0] @ bit;
  };
  let expected = sail_shiftright(0x71, unsigned(m) * 2);
  out_value == expected[1 .. 0]
}
