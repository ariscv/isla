default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 reset_pmp 的 foreach (i from 0 to 63)
// 大范围循环测试 max_backjumps_per_loop 限制下引擎能否正确完成
// 验证: 循环正确执行 64 次迭代

function prop() -> bool = {
  var bv : bits(64) = 0x0000000000000000;
  foreach (i from 0 to 63) {
    bv[i] = bitone
  };
  bv == 0xFFFFFFFFFFFFFFFF
}
