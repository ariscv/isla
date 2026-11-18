$include "include/nested_merge.sail"

function prop(m : bits(1), z : bits(1)) -> bool = {
  let expected : bits(8) = 0b0000 @ m @ z @ (m @ not_vec(m));
  candidate_boundary(m, z) == expected
}
