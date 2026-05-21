default Order dec

$include <prelude.sail>

// 模式来源: 同 range_match_chain.sat.sail，但断言所有分类结果都在合法范围内
// unsat: 所有路径的分类结果都是 >= 0 的

function classify(x: bits(4)) -> int = {
  if      x == 0b0000 then 0
  else if x == 0b0001 then 1
  else if x == 0b0010 then 2
  else if x == 0b0011 then 3
  else if x == 0b0100 then 4
  else if x == 0b0101 then 5
  else if x == 0b0110 then 6
  else                      7
}

function prop(x: bits(4)) -> bool = {
  classify(x) >= 0
}
