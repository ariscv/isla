default Order dec

$include <prelude.sail>

// 模式来源: sail-riscv 中 process_vlseg / process_vsseg 的嵌套 foreach 循环
// 验证: 嵌套循环正确执行，符号执行引擎在 max_backjumps_per_loop 限制下完成

function prop() -> bool = {
  var bv : bits(16) = 0x0000;
  foreach (i from 0 to 3) {
    foreach (j from 0 to 3) {
      bv[i * 4 + j] = bitone
    }
  };
  bv == 0xFFFF
}
