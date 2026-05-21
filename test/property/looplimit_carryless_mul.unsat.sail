default Order dec

$include <prelude.sail>

// 模式来源: 同 looplimit_carryless_mul.sat
// unsat: 累积结果恒等于自身

function prop(a: bits(8)) -> bool = {
  var acc : bits(8) = 0x00;
  foreach (i from 0 to 7) {
    if a[i] == bitone then {
      acc[i] = bitone
    } else {
      acc = acc
    }
  };
  acc == acc
}
