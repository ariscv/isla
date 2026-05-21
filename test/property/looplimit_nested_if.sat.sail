default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 process_vlseg 的嵌套 foreach + 内部分支
// 外层循环 + 内层循环 + 条件分支，模拟向量内存操作中的路径爆炸模式
// sat: 存在 y 使得结果不为全零

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
  bv != 0x0000
}
