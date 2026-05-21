default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 pmpCheck 串行 foreach + match 的 fork 路径
// 符号 bits 参数在 foreach 中按位分支，每次迭代 fork 一路
// 3 次循环 × 2 路 = 最多 8 条路径，在 max_total_forks(512) 内安全完成
// unsat: 无论 x 的低 3 位如何，反转后仍等于反转后的自身

function prop(x: bits(3)) -> bool = {
  var acc : bits(3) = 0b000;
  foreach (i from 0 to 2) {
    if x[i] == bitone then {
      acc[i] = bitzero
    } else {
      acc[i] = bitone
    }
  };
  acc == acc
}
