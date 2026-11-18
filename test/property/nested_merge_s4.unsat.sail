$include "include/nested_merge.sail"

function prop(w : bits(1), a : bits(1), z : bits(2)) -> bool = {
  let expected : bits(8) = 0b00 @ w @ a @ z @ reference_tag(z);
  candidate_three_levels(w, a, z) == expected
}
