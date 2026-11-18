$include "include/nested_merge.sail"

function prop(a : bits(2), z : bits(2)) -> bool = {
  let expected : bits(8) = 0b00 @ a @ z @ z;
  candidate_three(a, z, "b", "c", "d") == expected
}
