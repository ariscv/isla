// --- TOML
// title = "四个叶子各自读取 R 后合并"
// intent = "核对全域合并后每个输入的寄存器读足迹和读值。"
// inputs = { path_x = 1, path_y = 1, path_z = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 1
// must_merge = "四个字符串按 x、y 选择，每个输入仍恰好产生原分支的一笔 ReadReg(R)，读值与 path_z 相同。"
// status = "todo"
// reason = "total-merge-design.md §4（寄存器读足迹）：当前 property 导出寄存器后态，缺少逐输入核对 ReadReg(R) 次数与发生条件的记录。"
// ---
default Order dec
$include <prelude.sail>

register R : bits(1)

register path_x : bits(1)
register path_y : bits(1)
register path_z : bits(1)
register out_value : bits(1)

function prop(x : bits(1), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  var label : string = "";
  let data = if x == 0b0 then {
    if y == 0b0 then { let b = R; label = "a"; b } else { let b = R; label = "b"; b }
  } else {
    if y == 0b0 then { let b = R; label = "c"; b } else { let b = R; label = "d"; b }
  };
  path_z = data;
  out_value = data;
  let tag = if label == "a" then 0b00 else if label == "b" then 0b01 else if label == "c" then 0b10 else 0b11;
  tag == (x @ y)
}
