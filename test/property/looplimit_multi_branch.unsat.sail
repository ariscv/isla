default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

// 模式来源: 同 looplimit_multi_branch.sat，断言 match 结果总有定义
// unsat: 无论 e 是哪个枚举成员，match 总能返回一个值

enum E = A | B | C | D | E | F

function classify(e: E) -> int = {
  match e {
    A => 0, B => 1, C => 2, D => 3, E => 4, F => 5
  }
}

function prop(e: E) -> bool = {
  classify(e) >= 0
}
