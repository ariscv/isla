// --- TOML
// title = "检查负载长度，再拼接和扩展"
// intent = "两种宽度共用同一条路径，检查拼接的结果和原生长度。"
// inputs = { path_x = 1 }
// expect_paths_unmerged = 2
// expect_paths_merged = 1
// must_merge = "4 位与 8 位负载分别拼接 4 位，最后扩展到共同的 12 位。"
// ---
default Order dec
$include <prelude.sail>

type packet = { 'n, 'n in {4, 8}. bits('n) }
union response = { Ok : packet }

register path_x : bits(1)
register out_value : bits(12)

function prop(x : bits(1)) -> bool = {
  path_x = x;
  let v : response = if x == 0b0 then Ok(0xA) else Ok(0x3A);
  match v {
    Ok(b) => {
      let short = length(b) == 4;
      let joined = b @ 0x5;
      out_value = sail_zero_extend(joined, 12);
      (short == (x == 0b0)) & (out_value == (if x == 0b0 then 0x0A5 else 0x3A5))
    }
  }
}
