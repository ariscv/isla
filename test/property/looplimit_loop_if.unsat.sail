default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 pmpCheck 的 foreach (i from 0 to sys_pmp_count - 1)
// 每次循环迭代内有 if-else 分支（类似 match pmpMatchAddr 的三路分支）
// 验证: 循环内分支在执行限制下正确收敛

function prop() -> bool = {
  var acc : bits(8) = 0xFF;
  foreach (i from 0 to 7) {
    if acc[i] == bitone then {
      acc[i] = bitzero
    } else {
      acc = acc
    }
  };
  acc == 0x00
}
