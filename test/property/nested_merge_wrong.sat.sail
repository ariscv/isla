$include "include/nested_merge.sail"

// 故意把 z=1 的标签也规定为 10，要求框架找到反例。
function prop(a : bits(2), z : bits(2)) -> bool = {
  let expected : bits(8) = 0b00 @ a @ z @ 0b10;
  candidate_three(a, z, "b", "c", "c") == expected
}
