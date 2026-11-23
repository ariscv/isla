// --- TOML
// title = "外层汇合点把状态等价的片段并成最少的组"
// intent = "外层 a 的两臂各有一个内层区域（z、w），内层都因标签不同退化成两个片段，共 4 个片段。外层汇合点上标签相同的片段状态等价，必须并成 2 组，而不是 4 条路径。"
// inputs = { path_a = 1, path_z = 1, path_w = 1 }
// merge_concrete_values = false
// expect_paths_unmerged = 4
// expect_paths_merged = 2
// must_merge = "(a=0,z=0) 与 (a=1,w=0) 标签同为 p；(a=0,z=1) 与 (a=1,w=1) 标签同为 q。"
// ---
default Order dec
$include <prelude.sail>

register path_a : bits(1)
register path_z : bits(1)
register path_w : bits(1)
register out_value : bits(2)

function prop(a : bits(1), z : bits(1), w : bits(1)) -> bool = {
  path_a = a;
  path_z = z;
  path_w = w;
  var label : string = "init";
  var r : bits(1) = 0b0;
  if a == 0b0 then {
    if z == 0b0 then { label = "p"; r = 0b0 } else { label = "q"; r = 0b1 }
  } else {
    if w == 0b0 then { label = "p"; r = 0b1 } else { label = "q"; r = 0b0 }
  };
  out_value = r @ (if label == "p" then 0b0 else 0b1);
  let expected : bits(2) =
    if a == 0b0 then (if z == 0b0 then 0b00 else 0b11) else (if w == 0b0 then 0b10 else 0b01);
  out_value == expected
}
