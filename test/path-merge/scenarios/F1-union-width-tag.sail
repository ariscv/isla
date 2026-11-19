// --- TOML
// title = "调用者只检查 Ok 标签"
// intent = "调用方把 Ok 的 32 位和 64 位负载视作同一个标签，同时区分 Err。"
// inputs = { path_x = 2 }
// expect_paths_unmerged = 3
// expect_paths_merged = 1
// must_merge = "调用者只检查标签时，三个输入域共用一条继续路径。"
// ---
default Order dec
$include <prelude.sail>

type packet = { 'n, 'n in {32, 64}. bits('n) }
union response = { Ok : packet, Err : unit }

function respond(x : bits(2)) -> response =
  if x == 0b11 then Err(())
  else if x == 0b00 then Ok(0x00000005)
  else Ok(0x0000000000000007)

register path_x : bits(2)
register out_value : bool

function prop(x : bits(2)) -> bool = {
  path_x = x;
  out_value = match respond(x) { Ok(_) => true, Err(_) => false };
  out_value == (x != 0b11)
}
