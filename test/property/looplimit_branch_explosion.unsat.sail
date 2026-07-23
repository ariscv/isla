default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

// 模式来源: sail-riscv 中 check_PTE_permission 的多层 match 嵌套
// 第一层 match 分支后，第二层又有分支，总路径数指数增长
// 验证 max_forks_per_branch + max_forks_per_path 联合限制
// unsat: 两层枚举分类结果之和总是 >= 0

enum E1 = A | B | C | D
enum E2 = X | Y | Z

function f1(e: E1) -> int = {
  match e {
    A => 0, B => 1, C => 2, D => 3
  }
}

function f2(e: E2) -> int = {
  match e {
    X => 10, Y => 20, Z => 30
  }
}

function prop(e1: E1, e2: E2) -> bool = {
  (f1(e1) + f2(e2)) >= 0
}
