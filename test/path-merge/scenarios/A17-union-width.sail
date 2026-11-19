// --- TOML
// title = "读取同一构造子的负载宽度"
// intent = "在汇合后读取同一构造子的负载宽度，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "保留 P 标签，在其负载内按 x 选择位宽。解包后 length 在 x=0 时为 4，在 x=1 时为 8。"
// status = "xfail"
// reason = "total-merge-design.md §2（union 负载）：P 的两种负载宽度无法构造同宽 ITE，解包后仍分别完成。"
// ---
default Order dec
$include <prelude.sail>

type packet = { 'n, 'n in {4, 8}. bits('n) }
union U = { P : packet }

register path_x : bits(1)
register out_value : bool

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : U = if x == 0b0 then P(0xA) else P(0xAA);
  out_value = match v { P(b) => length(b) == 8 };
  out_value == (x == 0b1)
}
