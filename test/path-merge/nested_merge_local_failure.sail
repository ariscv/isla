default Order dec
$include <prelude.sail>

// ===== 骨架（待 Codex 审核与补全）=====
// 约定：
//  - 外层用 a∈{1,2,3} 选 3 条臂，臂间只差常量（可合并）。
//  - 内层用 z∈{1,2,3} 选 3 条臂：z==1 留下具体整数 k=1，z==2、z==3 留下 k=2（c2、c3 同值，b1 不同）。
//    不同的具体整数在合并时无法写成 ite（Isla 要求具体 I64），因此 b1 与 c 不可合并。
//  - k 在内层汇合点之后、外层汇合点之前被使用（例如传给需要具体值的原语 `zeros(k)` 或比较），之后不再使用或仍使用（S6）。
//  - 返回值需让各路径可区分（把 a、z 与 k 组合进结果），便于逐输入比对。

register _PC : bits(64)
enum read_kind = { Read_plain, Read_ifetch }
register dummy : read_kind

// S1：外层 3 × 内层 {b1,c2,c3}
val s1 : (bits(2), bits(2)) -> bits(8)
function s1(a, z) = {
  // TODO：补全：外层 match a { 1 => ... 2 => ... 3 => ... }，内层 match z { 1 => k=1, 2 => k=2, 3 => k=2 }
  0x00
}

// S2：外层 3 × 内层全同值（TODO）
// S3：外层 3 × 内层三值互异（TODO）
// S4：三层嵌套仅最内层部分失败（TODO）
// S5：被调函数内层失败，调用方合并成功（TODO）
// S6：失败发生在外层汇合点自己（TODO）
