// --- TOML
// title = "三个 I64 片段 3、符号值、7"
// intent = "将具体与符号 I64 汇合，在切片时保留原值。"
// inputs = { path_x = 2, path_y = 1 }
// expect_paths_unmerged = 3
// expect_paths_merged = 1
// must_merge = "3、unsigned(y)、7 按 x 选取。整数消费者均须使用活动守卫下的原整数，本例核对三位切片。"
// status = "xfail"
// reason = "total-merge-design.md §2–3（具体与符号 I64、整数消费）：外层汇合拒绝不兼容状态，已合并的整数又在切片前按守卫重试，三组分别完成。"
// ---
default Order dec
$include <prelude.sail>

register path_x : bits(2)
register path_y : bits(1)
register out_value : bits(3)

function prop(x : bits(2), y : bits(1)) -> bool = {
  path_x = x;
  path_y = y;
  let v : range(0, 7) = if x == 0b01 then unsigned(y) else if x == 0b00 then 3 else 7;
  out_value = get_slice_int(3, v, 0);
  let hi = x[1 .. 1];
  let lo = x[0 .. 0];
  out_value == (hi @ or_vec(hi, not_vec(lo)) @ or_vec(or_vec(hi, not_vec(lo)), y))
}
