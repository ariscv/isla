// --- TOML
// title = "四个结果组各自读取 R"
// intent = "每个叶子先读同一 R，再写互异字符串；每组都应保留自己的读事件。"
// inputs = { path_x = 1, path_y = 1, path_z = 1 }
// expect_paths_unmerged = 4
// expect_paths_merged = 4
// must_not_merge = "四个活跃标签各一组，每组的迹都必须出现 ReadReg(R)。"
// status = "todo"
// reason = "运行器导出访存事件与最终寄存器值；缺逐组的 ReadReg(R)、守卫与事件次序，后态正确仍可能漏读事件。"
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
