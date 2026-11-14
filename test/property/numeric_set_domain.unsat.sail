default Order dec

$include <prelude.sail>

// 用通用相等避免类型检查器直接把有限集合性质折叠成常量。
val runtime_eq = "eq_int" : (int, int) -> bool

type element_width = {1, 2, 4, 8}

function prop(width : element_width) -> bool = {
  runtime_eq(width, 1) | runtime_eq(width, 2) |
  runtime_eq(width, 4) | runtime_eq(width, 8)
}
