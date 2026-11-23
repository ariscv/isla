// --- TOML
// title = "四层嵌套，中间层失败，内外两侧都有已合并内容"
// intent = "d（最外）、a、b、c（最内）四层。c 层两臂标签相同，先合并成功；b 层两臂标签 p/q 不同，在 b 的汇合点失败；a、d 层仍合并。没有“最外层/最内层”特殊层。"
// inputs = { path_d = 1, path_a = 1, path_b = 1, path_c = 1 }
// merge_concrete_values = false
// expect_local_rejection = "IncompatibleState"
// expect_paths_unmerged = 5
// expect_paths_merged = 2
// must_merge = "标签 p 的到达项（d=1、a=1、b=0 下的 c 两种）必须并成一条路径；c 层已合并的前缀保留。"
// must_not_merge = "d=0,a=0,b=1 的标签是 q，单独一条路径。"
// ---
default Order dec
$include <prelude.sail>

register path_d : bits(1)
register path_a : bits(1)
register path_b : bits(1)
register path_c : bits(1)
register out_value : bits(3)

function prop(d : bits(1), a : bits(1), b : bits(1), c : bits(1)) -> bool = {
  path_d = d;
  path_a = a;
  path_b = b;
  path_c = c;
  var label : string = "init";
  var r : bits(2) = 0b00;
  if d == 0b0 then {
    if a == 0b0 then {
      if b == 0b0 then {
        // 最内层：标签相同，可合并。
        if c == 0b0 then { label = "p"; r = 0b00 } else { label = "p"; r = 0b01 }
      } else {
        // 中间层：到这里标签与上面的 p 不同（q），b 区域在汇合点不兼容。
        label = "q";
        r = 0b10
      }
    } else {
      label = "p";
      r = 0b11
    }
  } else {
    label = "p";
    r = 0b11
  };
  out_value = r @ (if label == "p" then 0b0 else 0b1);
  let expected : bits(3) =
    if d == 0b1 then 0b110
    else if a == 0b1 then 0b110
    else if b == 0b0 then (if c == 0b0 then 0b000 else 0b010)
    else 0b101;
  out_value == expected
}
