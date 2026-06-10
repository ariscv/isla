default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 pmpRangeMatch 的三路分支 (NoMatch/PartialMatch/Match)
// 用 if-else 链对符号值做多路判定，模拟符号执行中分支爆炸的场景
// sat: 存在使得 prop 为 false 的输入（x 在某些值下不满足条件）

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
  classify(x) == 0
}
