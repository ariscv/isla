default Order dec

$include <prelude.sail>

// 模式来源: 同 nested_foreach_branch.sat，断言 bv 和自身相等（恒真）
// unsat: 无论 y 值如何，bv == bv 总是成立

function prop(y: bits(4)) -> bool = {
  var bv : bits(16) = 0x0000;
  foreach (i from 0 to 3) {
    foreach (j from 0 to 3) {
      if y[0] == bitone then {
        bv[i * 4 + j] = bitone
      } else {
        bv = bv
      }
    }
  };
  bv == bv
}
