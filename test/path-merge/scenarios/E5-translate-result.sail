// --- TOML
// title = "从 Bare 提前返回到翻译结果"
// intent = "同时覆盖 Bare、地址非规范、辅助函数成功和辅助函数报错四种结果。"
// inputs = { path_mode = 3 }
// expect_paths_unmerged = 5
// expect_paths_merged = 1
// must_merge = "断言在所有合法位宽上成立，Bare 与三个翻译出口最终均返回带标签和负载的正常结果。"
// status = "xfail"
// reason = "严格模式最终有两条，开启具体值合并后有五条。两种配置均覆盖所有输入。"
// ---
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
union Walk = { Ok : bits(2), Err : bits(2) }
function walk(w : {32, 39, 48, 57}) -> Walk = if w == 48 then Err(0b10) else Ok(0b11)
function translate(m : bits(3)) -> Walk = {
  if m[2 .. 2] == 0b1 then return Ok(0b00);
  let 'w = mode_width(m[1 .. 0]);
  let addr = 0x0000004000000000;
  assert(w <= length(addr));
  let low = addr[w - 1 .. 0];
  if sail_sign_extend(low, 64) != addr then Err(0b01) else
    match walk(w) { Ok(p) => Ok(xor_vec(p, 0b10)), Err(e) => Err(xor_vec(e, 0b01)) }
}
register path_mode : bits(3)
register out_value : bits(3)
function prop(m : bits(3)) -> bool = {
  path_mode = m;
  out_value = match translate(m) { Ok(p) => 0b0 @ p, Err(e) => 0b1 @ e };
  let table = sail_shiftright(0x0000000001070505, 8 * unsigned(m));
  out_value == table[2 .. 0]
}
