$include "include/nested_merge.sail"

function prop(a : bits(2), z : bits(2)) -> bool = {
  let expected : bits(8) = 0b00 @ a @ z @ reference_tag(z);
  candidate_callee(a, z) == expected
}
