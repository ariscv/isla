default Order dec
$include <prelude.sail>

// 非连续集合必须完整保留，不能退化为范围。
type access_width = {1, 2, 4, 8}
union request = { Read : (bits(8), access_width) }
val read_width : request -> int
function read_width(Read(_, width)) = width

register _PC : bits(64)
enum read_kind = { Read_plain, Read_ifetch }
register dummy : read_kind

// 返回值使用普通 int，防止类型检查器直接消去待验证条件。
val prop : request -> bool
function prop(req) = {
  let width = read_width(req);
  assert(width == 1 | width == 2 | width == 4 | width == 8);
  true
}

val witness1 : request -> bool
function witness1(req) = { assert(read_width(req) != 1); true }

val witness2 : request -> bool
function witness2(req) = { assert(read_width(req) != 2); true }

val witness4 : request -> bool
function witness4(req) = { assert(read_width(req) != 4); true }

val witness8 : request -> bool
function witness8(req) = { assert(read_width(req) != 8); true }
