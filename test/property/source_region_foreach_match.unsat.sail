default Order dec

$include <prelude.sail>

val "assume" : bool -> unit

$property
function prop(x : bit, a : int) -> bool = {
  assume(a > 0);
  var result : bool = true;
  foreach (i from 0 to a) {
    match x {
      bitzero => {
        result = i >= 0
      },
      bitone => {
        result = i >= 0
      }
    };
    if i == 0 then return result else ()
  };
  true
}
