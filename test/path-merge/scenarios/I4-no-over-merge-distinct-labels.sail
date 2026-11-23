// --- TOML
// title = "标签两两不同的片段不得过度合并"
// intent = "与 I3 同构，但三种标签 p、q、s：(a=0,z=0)->p，(a=0,z=1) 与 (a=1,w=0)->q，(a=1,w=1)->s。状态不等价的片段不能并，期望正好 3 条路径。"
// inputs = { path_a = 1, path_z = 1, path_w = 1 }
// merge_concrete_values = false
// expect_paths_unmerged = 4
// expect_paths_merged = 3
// must_merge = "(a=0,z=1) 与 (a=1,w=0) 标签同为 q，并成一条。"
// must_not_merge = "p 与 s 单独保留，不得为了少路径而合并不等价的状态。"
// ---
default Order dec
$include <prelude.sail>

register path_a : bits(1)
register path_z : bits(1)
register path_w : bits(1)
register out_value : bits(3)

function label_bits(k : string) -> bits(2) =
  if k == "p" then 0b00 else if k == "q" then 0b01 else 0b10

function prop(a : bits(1), z : bits(1), w : bits(1)) -> bool = {
  path_a = a;
  path_z = z;
  path_w = w;
  var label : string = "init";
  var r : bits(1) = 0b0;
  if a == 0b0 then {
    if z == 0b0 then { label = "p"; r = 0b0 } else { label = "q"; r = 0b1 }
  } else {
    if w == 0b0 then { label = "q"; r = 0b0 } else { label = "s"; r = 0b1 }
  };
  out_value = r @ label_bits(label);
  let expected : bits(3) =
    if a == 0b0 then (if z == 0b0 then 0b000 else 0b101)
    else (if w == 0b0 then 0b001 else 0b110);
  out_value == expected
}
