// --- TOML
// title = "内层不能合并，外层仍合并"
// intent = "内层区域的两臂字符串不同且不合并（merge_concrete_values=false），内层岔成两个普通片段；外层 a 的两臂仍在自己的汇合点合并，并把标签相同的到达项并成一组。"
// inputs = { path_a = 1, path_z = 1 }
// merge_concrete_values = false
// expect_local_rejection = "IncompatibleState"
// expect_paths_unmerged = 3
// expect_paths_merged = 2
// must_merge = "a=0,z=0 与 a=1 的标签同为 p，状态等价，必须在外层汇合点并成一条路径。"
// must_not_merge = "a=0,z=1 的标签是 q，与 p 不能并。"
// ---
default Order dec
$include <prelude.sail>

register path_a : bits(1)
register path_z : bits(1)
register out_value : bits(2)

function prop(a : bits(1), z : bits(1)) -> bool = {
  path_a = a;
  path_z = z;
  var label : string = "init";
  var r : bits(1) = 0b0;
  if a == 0b0 then {
    // 内层区域：两臂写不同字符串，在汇合点不兼容。
    if z == 0b0 then { label = "p"; r = 0b0 } else { label = "q"; r = 0b1 }
  } else {
    label = "p";
    r = 0b1
  };
  out_value = r @ (if label == "p" then 0b0 else 0b1);
  let expected : bits(2) = if a == 0b0 then (if z == 0b0 then 0b00 else 0b11) else 0b10;
  out_value == expected
}
