default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv/model/core/arithmetic.sail::carryless_mul
// 8 位版本: foreach 8 次迭代，每次对符号位 a[i] 分支 → 2^8=256 条路径
// 验证 max_forks_per_branch 限制下路径爆炸受控

function prop(a: bits(8)) -> bool = {
  var acc : bits(8) = 0x00;
  foreach (i from 0 to 7) {
    if a[i] == bitone then {
      acc[i] = bitone
    } else {
      acc = acc
    }
  };
  acc != 0x00
}
