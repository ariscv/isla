# vector access 符号索引方案 findings

## 当前采用：SMT Array

目标是把 `vs2_val[idx]` 视为类似加法的独立 SMT 运算，而不是在 executor 里展开成 `idx == 0 / idx == 1 / ...` 的嵌套 ITE。

当前实现路径：

- Sail 继续调用通用 primop：`isla_vector_access_or_default(VLMAX, vs2_val, idx, zeros())`
- Rust primop 将 `Val::Vector` 编码成 SMT array：
  - fresh array base：`Array(BitVec(index_width), BitVec(element_width))`
  - 对有效元素生成 `store(array, i, values[i])`
  - 用 `select(array, idx)` 表达访问
  - 外层只保留一层 unsigned bound：`ite(idx < valid_len, select(...), default)`

这样可以消掉 Sail 级 `if idx < VLMAX then ... else ...` 的路径分叉，同时避免把 symbolic vector access 降成逐元素 equality 链。

## 备选项 1：`mux2(idx < VLMAX, vs2_val[idx], zeros())`

优点：

- Sail 改动最小。
- 可以消掉显式 `if` 带来的路径 fork。

问题：

- `mux2` 参数是 eager 求值，`vs2_val[idx]` 会先执行；具体越界 index 可能先触发 out-of-bounds。
- `idx < VLMAX` 仍会走整数比较路径，可能继续触发 solver check。
- 当前 `vector_access` 对 `Val::Vector + symbolic idx` 仍会展开成 nested ITE，不满足“原子访问”的目标。

## 备选项 2：uninterpreted function

形式类似：

```smt2
(declare-fun vec_access (VecId Index) Elem)
```

优点：

- 最接近“把访问当成完全原子运算”。
- 表达式最小，solver 负担低。

问题：

- 如果没有额外约束 `vec_access(vec, i) == values[i]`，语义会欠约束。
- 加完整约束后又会回到逐元素关系，只是换成 UF 等式。
- 需要设计稳定的 vector identity，否则不同 vector 值可能被错误混同。

## 备选项 3：packed bitvector dynamic extract

形式是把 vector 打包成一个大 bitvector，再用 shift/extract：

```smt2
extract(SEW-1, 0, packed >> (idx * SEW))
```

优点：

- 不引入 array theory。
- 不需要逐个 `idx == i` 的 ITE。
- 对 bitvector solver 来说语义精确。

问题：

- 仍需要构造 `packed = concat(values[n-1], ..., values[0])`。
- 动态 shift 的 bitvector 表达式可能很宽，`num_elem * SEW` 大时可能比 array select 更重。
- 对非均匀 element width 或未来非 bitvector element 不适合。

## 后续可选：Sail 侧 V 寄存器数组化

如果后面要更彻底，可以考虑让 sail-riscv 的 V 寄存器读写在 symbolic extra-op 路径直接暴露为 array 风格结构，而不是先读成 Sail vector 再由 primop 转成 SMT array。

这可能减少 repeated store-chain 构造，但改动面更大，涉及 `read_vreg`、`write_vreg`、mask/tail 语义和 IR 生成形态，建议等当前 array-select primop 的性能数据稳定后再评估。
