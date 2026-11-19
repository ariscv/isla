// --- TOML
// title = "读取同一构造子的负载宽度"
// intent = "在汇合后读取同一构造子的负载宽度，用输入核对结果。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 2
// must_not_merge = "同一 P 的负载宽度仍由后续消费者观测，严格表示下分作两条。"
// status = "ready"
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
