// --- TOML
// title = "区域中途失败：失败点之前已合并的前缀保留"
// intent = "a=0 臂先汇合由 b 选择的值并写入寄存器。随后的 bits_str(a) 需要求解模型，在延后模式下触发 UnknownDeferredMode。应固化已完成的合并并只重试该原语。"
// inputs = { path_a = 1, path_b = 1 }
// registers = ["prefix_value"]
// expect_paths_unmerged = 3
// expect_paths_merged = 2
// expect_prefix_rejection = "UnknownDeferredMode"
// must_merge = "a=0 时 b=0 和 b=1 共用一条完成路径，并保留已固化的内层合并记录与 prefix_value。"
// ---
default Order dec
$include <prelude.sail>

register path_a : bits(1)
register path_b : bits(1)
register prefix_value : bits(1)
register out_value : bits(1)

function prop(a : bits(1), b : bits(1)) -> bool = {
  path_a = a;
  path_b = b;
  var r : bits(1) = 0b0;
  if a == 0b0 then {
    if b == 0b0 then { r = 0b0 } else { r = 0b1 };
    prefix_value = r;
    // 当前守卫已将 a 约束为 0；普通执行可证明格式化操作只有一个结果。
    let text = bits_str(a);
    out_value = if text == bits_str(0b0) then r else not_vec(r)
  } else {
    prefix_value = 0b1;
    out_value = 0b1
  };
  out_value == or_vec(a, b)
}
