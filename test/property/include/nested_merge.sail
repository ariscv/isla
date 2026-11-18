default Order dec
$include <prelude.sail>

val "assume" : bool -> unit

register path_a : bits(2)
register path_z : bits(2)

function string_tag(k : string) -> bits(2) =
  if k == "b" then 0b01 else if k == "c" then 0b10 else 0b11

// z=1 的标签是 01，z=2、3 的标签是 10。
function reference_tag(z : bits(2)) -> bits(2) =
  z[1 .. 1] @ not_vec(z[1 .. 1])

// S1：三路 a × 三路 z。9→2，按 z=1 与 z∈{2,3} 分组。
// c2、c3 的 k 相同，各自的 r 取 10、11，可用 ITE 合并。b1 的 k 与它们不同。
// S2：三个 k 都是 b，9→1。S3：三个 k 两两不同，9→3，按 z 分组。
// 控制：只将 S1 的 b1 改为与 c2、c3 相同的 c，9→1。
function candidate_three(a : bits(2), z : bits(2), b : string, c : string, d : string) -> bits(8) = {
  assume(a != 0b00);
  assume(z != 0b00);
  var k : string = "initial";
  var r : bits(2) = 0b00;
  let picked : bits(2) = if a == 0b01 then {
    if z == 0b01 then {
      k = b;
      r = 0b01
    } else {
      if z == 0b10 then {
        k = c;
        r = 0b10
      } else {
        k = d;
        r = 0b11
      }
    };
    0b01
  } else if a == 0b10 then {
    if z == 0b01 then {
      k = b;
      r = 0b01
    } else {
      if z == 0b10 then {
        k = c;
        r = 0b10
      } else {
        k = d;
        r = 0b11
      }
    };
    0b10
  } else {
    if z == 0b01 then {
      k = b;
      r = 0b01
    } else {
      if z == 0b10 then {
        k = c;
        r = 0b10
      } else {
        k = d;
        r = 0b11
      }
    };
    0b11
  };
  0b00 @ picked @ r @ string_tag(k)
}

// S4：w、a 两个二路外层与三路 z。12→2，按 z=1 与 z∈{2,3} 分组。
function candidate_three_levels(w : bits(1), a : bits(1), z : bits(2)) -> bits(8) = {
  assume(z != 0b00);
  var k : string = "initial";
  var r : bits(2) = 0b00;
  var middle : bits(1) = 0b0;
  let outer : bits(1) = if w == 0b0 then {
    middle = if a == 0b0 then {
      if z == 0b01 then {
        k = "b";
        r = 0b01
      } else {
        if z == 0b10 then {
          k = "c";
          r = 0b10
        } else {
          k = "c";
          r = 0b11
        }
      };
      0b0
    } else {
      if z == 0b01 then {
        k = "b";
        r = 0b01
      } else {
        if z == 0b10 then {
          k = "c";
          r = 0b10
        } else {
          k = "c";
          r = 0b11
        }
      };
      0b1
    };
    0b0
  } else {
    middle = if a == 0b0 then {
      if z == 0b01 then {
        k = "b";
        r = 0b01
      } else {
        if z == 0b10 then {
          k = "c";
          r = 0b10
        } else {
          k = "c";
          r = 0b11
        }
      };
      0b0
    } else {
      if z == 0b01 then {
        k = "b";
        r = 0b01
      } else {
        if z == 0b10 then {
          k = "c";
          r = 0b10
        } else {
          k = "c";
          r = 0b11
        }
      };
      0b1
    };
    0b1
  };
  0b00 @ outer @ middle @ r @ string_tag(k)
}

// S5：调用方三路 a，内层三路 z 位于被调函数。9→2，形状同 S1。
function inner_callee(z : bits(2)) -> (string, bits(2)) = {
  var k : string = "initial";
  var r : bits(2) = 0b00;
  if z == 0b01 then {
    k = "b";
    r = 0b01
  } else {
    if z == 0b10 then {
      k = "c";
      r = 0b10
    } else {
      k = "c";
      r = 0b11
    }
  };
  (k, r)
}

function candidate_callee(a : bits(2), z : bits(2)) -> bits(8) = {
  assume(a != 0b00);
  assume(z != 0b00);
  var k : string = "initial";
  var r : bits(2) = 0b00;
  let picked : bits(2) = if a == 0b01 then {
    let (next_k, next_r) = inner_callee(z);
    k = next_k;
    r = next_r;
    0b01
  } else if a == 0b10 then {
    let (next_k, next_r) = inner_callee(z);
    k = next_k;
    r = next_r;
    0b10
  } else {
    let (next_k, next_r) = inner_callee(z);
    k = next_k;
    r = next_r;
    0b11
  };
  0b00 @ picked @ r @ string_tag(k)
}

// S6 边界：内层 z 可合并。中层自己的汇合点遇到不同字符串，4→2，按 m 分组。
function candidate_boundary(m : bits(1), z : bits(1)) -> bits(8) = {
  var k : string = "initial";
  var r : bits(1) = 0b0;
  let middle : bits(1) = if m == 0b0 then {
    r = if z == 0b0 then 0b0 else 0b1;
    k = "b";
    0b0
  } else {
    r = if z == 0b0 then 0b0 else 0b1;
    k = "c";
    0b1
  };
  0b0000 @ middle @ r @ string_tag(k)
}

// S6：再包一层 w，8→2。两条路径各自覆盖 w 的两个取值，仍按 m 分组。
function candidate_wrapped(w : bits(1), m : bits(1), z : bits(1)) -> bits(8) = {
  var k : string = "initial";
  var r : bits(1) = 0b0;
  var middle : bits(1) = 0b0;
  let outer : bits(1) = if w == 0b0 then {
    middle = if m == 0b0 then {
      r = if z == 0b0 then 0b0 else 0b1;
      k = "b";
      0b0
    } else {
      r = if z == 0b0 then 0b0 else 0b1;
      k = "c";
      0b1
    };
    0b0
  } else {
    middle = if m == 0b0 then {
      r = if z == 0b0 then 0b0 else 0b1;
      k = "b";
      0b0
    } else {
      r = if z == 0b0 then 0b0 else 0b1;
      k = "c";
      0b1
    };
    0b1
  };
  0b000 @ outer @ middle @ r @ string_tag(k)
}
