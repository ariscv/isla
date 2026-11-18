$include "include/nested_merge.sail"

function prop(w : bits(1), m : bits(1), z : bits(1)) -> bool = {
  let expected : bits(8) = 0b000 @ w @ m @ z @ (m @ not_vec(m));
  candidate_wrapped(w, m, z) == expected
}
