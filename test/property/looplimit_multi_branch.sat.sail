default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

// 模式来源: sail-riscv 中 pmpCheckRWX 对 MemoryAccessType 的 match
// 符号枚举参数产生多路分支 fork，验证 max_forks_per_branch 限制
// sat: 存在 e 使得 e != A（即 B/C/D/E/F 都使结果为 false）

enum E = A | B | C | D | E | F

function prop(e: E) -> bool = {
  e == A
}
