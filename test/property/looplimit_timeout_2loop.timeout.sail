default Order dec

$include <prelude.sail>

// 双循环 64 位版本: 两个独立 foreach 各有不同的分支指令
// 第一个循环 fork ~1024 条路径，第二个循环的分支指令是新的 → 再 fork 一轮
// 总路径 ~2048+，64 位 bitvector SMT 开销大 → 总时间超过 5 秒
// 用于验证执行超时行为

function prop(a: bits(64), b: bits(64)) -> bool = {
  var acc : bits(64) = 0x0000000000000000;
  foreach (i from 0 to 63) {
    if a[i] == bitone then {
      acc[i] = bitone
    } else {
      acc = acc
    }
  };
  foreach (j from 0 to 63) {
    if b[j] == bitone then {
      acc[j] = bitone
    } else {
      acc = acc
    }
  };
  acc != 0x0000000000000000
}
