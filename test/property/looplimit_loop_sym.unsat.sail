default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

// 模式来源: sail-riscv 中 pmpCheck 循环内对 pmpMatchAddr 结果做 match
// 每次迭代根据符号条件选择不同路径，类似 match { NoMatch => skip, Match => return }
// unsat: 只要 assumed 条件成立，最终结果必然正确

function prop() -> bool = {
  var bv : bits(10) = 0b1111111111;
  foreach (i from 0 to 9) {
    let flag : bool = undefined;
    assume(flag == (i < 5));
    if flag then {
      bv[i] = bitzero
    } else {
      bv = bv
    }
  };
  bv == 0b1111100000
}
