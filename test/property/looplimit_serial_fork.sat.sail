default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 pmpCheck 的串行 foreach + match
// 每次循环迭代对枚举做 match，各迭代的分支累加产生全局 fork
// 验证 max_total_forks 限制
// sat: 存在 x 使得结果为 false（x 的低位不是全 1）

function prop(x: bits(8)) -> bool = {
  var acc : bits(8) = 0xFF;
  foreach (i from 0 to 7) {
    if x[i] == bitone then {
      acc[i] = bitzero
    } else {
      acc = acc
    }
  };
  acc == 0xFF
}
