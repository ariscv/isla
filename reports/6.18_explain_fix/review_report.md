# ../sail-riscv 暂存区改动 review 报告

## 范围与来源

本报告只解释 `../sail-riscv` 当前暂存区内容，来源为：

```sh
git -C ../sail-riscv diff --cached --name-status
git -C ../sail-riscv diff --cached --stat
git -C ../sail-riscv show :<path>
```

暂存区条目如下：

```text
A  .codex
A  diff
M  model/core/arithmetic.sail
M  model/extensions/K/zbkb_insts.sail
M  model/extensions/K/zbkx_insts.sail
M  model/extensions/V/vext_arith_insts.sail
M  model/extensions/V/vext_control.sail
M  model/extensions/V/vext_utils_insts.sail
M  model/extensions/V/vext_vm_insts.sail
```

总体设计是：非 `SYMBOLIC` 编译时保持原始实现；`SYMBOLIC` 编译时保留一份 `*_default` 原始语义实现，并通过运行时开关 `__isla_use_extra_ops` 决定是否调用 Isla 侧内置操作。这样可以避免普通 Sail 目标和没有对应内置函数的平台受到影响。

核心开关代码在 `model/core/arithmetic.sail` 中新增：

```sail
$ifdef SYMBOLIC
register __isla_use_extra_ops : bool = false

val isla_brev8 = pure "isla_brev8" : forall 'm, 'm >= 0 & mod('m, 8) == 0. bits('m) -> bits('m)
val isla_rev8 = pure "isla_rev8" : forall 'm, 'm >= 0 & mod('m, 8) == 0. bits('m) -> bits('m)
val isla_carryless_mul = pure "isla_carryless_mul" : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits(2 * 'n)
val isla_carryless_mulr = pure "isla_carryless_mulr" : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
val isla_count_ones = pure "isla_count_ones" : forall 'n, 'n >= 0. bits('n) -> range(0, 'n)
$endif
```

## 涉及的指令总览

| 改动位置 | 直接或间接受影响的指令 | 指令用法 | 指令语义摘要 |
| --- | --- | --- | --- |
| `arithmetic.sail` `brev8` | `brev8 rd, rs1`，向量 crypto `vbrev8.v`，GHASH/GCM 辅助路径 | 一般为 `rd, rs1` 或 `vd, vs2[, vm]` | 每个字节内部 bit 反序，不改变字节顺序 |
| `arithmetic.sail` `rev8` / `vrev8` | `rev8 rd, rs1`，`vrev8.v vd, vs2[, vm]`，SHA 向量 crypto 辅助路径 | 标量 `rd, rs1`，向量 `vd, vs2[, vm]` | 按字节反转元素或寄存器内的字节顺序 |
| `arithmetic.sail` `carryless_mul` / `carryless_mulr` | `clmul rd, rs1, rs2`，`clmulh rd, rs1, rs2`，`clmulr rd, rs1, rs2`，`vclmul.*` / `vclmulh.*` | 三寄存器或向量 crypto 操作 | 在 GF(2) 上做无进位乘法；`clmul` 取低半，`clmulh` 取高半，`clmulr` 取反向对齐结果 |
| `arithmetic.sail` `count_ones` | `cpop rd, rs1`，`cpopw rd, rs1` | `rd, rs1` | 统计源操作数中为 1 的 bit 数 |
| `zbkb_insts.sail` | `zip rd, rs1`，`unzip rd, rs1` | RV32 only | `zip` 交织低/高 16 bit；`unzip` 做相反的解交织 |
| `zbkx_insts.sail` | `xperm8 rd, rs1, rs2`，`xperm4 rd, rs1, rs2` | 三寄存器 | 用 `rs2` 中每个 byte/nibble 作为索引，从 `rs1` 选 byte/nibble；越界为 0 |
| `vext_control.sail` | 所有读写向量寄存器或 mask 的 V 指令 | 被 V 指令公共路径调用 | 读取/写回向量寄存器组，读取普通 mask 和 carry mask |
| `vext_utils_insts.sail` | V merge/move/immediate/carry/compare 指令，`vrev8`，SHA crypto 辅助 | 公共 helper | 处理 scalar 截取/扩展、5-bit 立即数扩展、mask 初始化、向量选择、8 元素写回 |
| `vext_arith_insts.sail` | `vmerge.vvm`，`vmv.v.v`，`vmerge.vxm`，`vmv.v.x`，`vadd.vi`，`vrsub.vi`，`vand.vi`，`vor.vi`，`vxor.vi`，`vsaddu.vi`，`vsadd.vi`，`vsll.vi`，`vsrl.vi`，`vsra.vi`，`vssrl.vi`，`vssra.vi`，`vmerge.vim`，`vmv.v.i` | OPIVV/OPIVX/OPIVI | 向量 merge/move 和向量-立即数整数算术/逻辑/移位/饱和操作 |
| `vext_vm_insts.sail` | `vmadc.vim`，`vmadc.vi`，`vadc.vim`，`vmseq.vi`，`vmsne.vi`，`vmsleu.vi`，`vmsle.vi`，`vmsgtu.vi`，`vmsgt.vi` | OPIVI mask/carry/compare | 带 5-bit 立即数的进位 mask、加法和比较 mask 结果 |

## 1. `model/core/arithmetic.sail`

### 改动代码

`brev8`、`carryless_mul`、`carryless_mulr`、`rev8`、`count_ones` 都改成同一个模式：原始实现放在 `$ifndef SYMBOLIC`；`$else` 中复制原始实现为 `*_default`，再用 `__isla_use_extra_ops` 选择 Isla 内置函数或默认实现。

```sail
$ifndef SYMBOLIC
val brev8 : forall 'm, 'm >= 0 & mod('m, 8) == 0. (bits('m)) -> bits('m)
function brev8(input) = {
  var output : bits('m) = zeros();
  foreach (i from 0 to ('m - 8) by 8)
    output[i+7..i] = reverse_bits(input[i+7..i]);
  output
}
$else
val brev8_default : forall 'm, 'm >= 0 & mod('m, 8) == 0. (bits('m)) -> bits('m)
function brev8_default(input) = {
  var output : bits('m) = zeros();
  foreach (i from 0 to ('m - 8) by 8)
    output[i+7..i] = reverse_bits(input[i+7..i]);
  output
}

val brev8 : forall 'm, 'm >= 0 & mod('m, 8) == 0. (bits('m)) -> bits('m)
function brev8(input) =
  if __isla_use_extra_ops then isla_brev8(input)
  else brev8_default(input)
$endif
```

```sail
val carryless_mul : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits(2 * 'n)
function carryless_mul(a, b) =
  if __isla_use_extra_ops then isla_carryless_mul(a, b)
  else carryless_mul_default(a, b)

val carryless_mulr : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
function carryless_mulr(a, b) =
  if __isla_use_extra_ops then isla_carryless_mulr(a, b)
  else carryless_mulr_default(a, b)

val rev8 : forall 'm, 'm >= 0 & mod('m, 8) == 0. (bits('m)) -> bits('m)
function rev8(input) =
  if __isla_use_extra_ops then isla_rev8(input)
  else rev8_default(input)

val count_ones : forall 'n, 'n >= 0. (bits('n)) -> range(0, 'n)
function count_ones(x) =
  if __isla_use_extra_ops then isla_count_ones(x)
  else count_ones_default(x)
```

### 指令语义和用法

`brev8 rd, rs1`：把 `rs1` 中每个 8-bit 字节分别 bit 反序后写入 `rd`。例如每个 byte 的 bit 位置 `7..0` 反转为 `0..7`，字节之间位置不交换。

`rev8 rd, rs1`：按 byte 粒度反转整个 `rs1` 的 byte 顺序后写入 `rd`，RV32 和 RV64 都有对应编码。

`clmul rd, rs1, rs2`：对 `rs1` 和 `rs2` 做无进位乘法，取低 `xlen` bit。

`clmulh rd, rs1, rs2`：同样做无进位乘法，取高 `xlen` bit。

`clmulr rd, rs1, rs2`：做反向对齐的无进位乘法结果，用于 Zbc。

`cpop rd, rs1` / `cpopw rd, rs1`：统计 `rs1` 全宽或低 32 bit 中 1 的个数。

### 改动理由

这些 helper 原始实现都包含循环、动态切片或宽度相关表达式。符号执行时容易把循环展开成很大的表达式，或者触发 Isla 侧对动态长度/动态 slice 的限制。把这些基础 bit 操作替换成 Isla primitive 后，可以让 solver 直接处理一个受控的外部语义函数，减少 IR 展开和求解压力。

### 改动部分语义

当没有定义 `SYMBOLIC` 时，代码就是原实现。当定义 `SYMBOLIC` 但运行时 `__isla_use_extra_ops == false` 时，仍走 `*_default` 原实现。当 `__isla_use_extra_ops == true` 时才调用 `isla_*`。因此 review 重点是确认 Isla 侧 primitive 与默认 Sail 实现逐 bit 等价。

## 2. `model/extensions/K/zbkb_insts.sail`

### 改动代码

`ZIP` 和 `UNZIP` 被拆成非 SYMBOLIC 原始分支和 SYMBOLIC 分支。SYMBOLIC 分支只额外增加 `xlen != 32` 时返回非法指令的运行时保护。

```sail
$ifndef SYMBOLIC
function clause execute ZIP(rs1, rd) = {
  assert(xlen == 32);
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen_bytes*4 - 1)) {
    result[i*2] = rs1_val[i];
    result[i*2 + 1] = rs1_val[i + xlen_bytes*4];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
$else
function clause execute ZIP(rs1, rd) = {
  if __isla_use_extra_ops & xlen != 32 then return Illegal_Instruction();
  assert(xlen == 32);
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen_bytes*4 - 1)) {
    result[i*2] = rs1_val[i];
    result[i*2 + 1] = rs1_val[i + xlen_bytes*4];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
$endif
```

```sail
$ifndef SYMBOLIC
function clause execute UNZIP(rs1, rd) = {
  assert(xlen == 32);
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen_bytes*4 - 1)) {
    result[i] = rs1_val[i*2];
    result[i + xlen_bytes*4] = rs1_val[i*2 + 1];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
$else
function clause execute UNZIP(rs1, rd) = {
  if __isla_use_extra_ops & xlen != 32 then return Illegal_Instruction();
  assert(xlen == 32);
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen_bytes*4 - 1)) {
    result[i] = rs1_val[i*2];
    result[i + xlen_bytes*4] = rs1_val[i*2 + 1];
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
$endif
```

### 指令语义和用法

`zip rd, rs1`：RV32 指令。把 `rs1` 的低 16 bit 和高 16 bit 交错写入 `rd`，低半部分 bit 放到偶数位置，高半部分 bit 放到奇数位置。

`unzip rd, rs1`：RV32 指令。把 `rs1` 偶数位置 bit 和奇数位置 bit 拆回低半/高半，语义上是 `zip` 的逆变换。

### 改动理由

编码约束已经限制 `xlen == 32`，但符号执行或特定 decode/探索路径可能仍进入执行函数并触发 `assert(xlen == 32)`。SYMBOLIC + extra-op 模式下将这种情况转成 `Illegal_Instruction()`，避免因为 RV64 场景的 assert 中断符号执行。

### 改动部分语义

正常 RV32 语义不变。只有 `SYMBOLIC` 且 `__isla_use_extra_ops` 打开时，非 RV32 进入该执行函数会返回非法指令，而不是继续触发 assert。非 SYMBOLIC 分支完全保留原始代码。

## 3. `model/extensions/K/zbkx_insts.sail`

### 改动代码

`XPERM8` / `XPERM4` 保留原始实现，并在 SYMBOLIC 分支中新增 Isla primitive wrapper。

```sail
$ifndef SYMBOLIC
function clause execute XPERM8(rs2, rs1, rd) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen - 8) by 8) {
    let index = unsigned(rs2_val[i+7..i]);
    result[i+7..i] = if 8*index < xlen
                     then rs1_val[8*index+7..8*index]
                     else zeros()
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
$else
val isla_xperm8 = pure "isla_xperm8" : (xlenbits, xlenbits) -> xlenbits

val xperm8_default : (xlenbits, xlenbits) -> xlenbits
function xperm8_default(rs1_val, rs2_val) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen - 8) by 8) {
    let index = unsigned(rs2_val[i+7..i]);
    result[i+7..i] = if 8*index < xlen
                     then rs1_val[8*index+7..8*index]
                     else zeros()
  };
  result
}

val xperm8 : (xlenbits, xlenbits) -> xlenbits
function xperm8(rs1_val, rs2_val) =
  if __isla_use_extra_ops then isla_xperm8(rs1_val, rs2_val)
  else xperm8_default(rs1_val, rs2_val)

function clause execute XPERM8(rs2, rs1, rd) = {
  X(rd) = xperm8(X(rs1), X(rs2));
  RETIRE_SUCCESS
}
$endif
```

```sail
val isla_xperm4 = pure "isla_xperm4" : (xlenbits, xlenbits) -> xlenbits

val xperm4_default : (xlenbits, xlenbits) -> xlenbits
function xperm4_default(rs1_val, rs2_val) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (xlen - 4) by 4) {
    let index = unsigned(rs2_val[i+3..i]);
    result[i+3..i] = if 4*index < xlen
                     then rs1_val[4*index+3..4*index]
                     else zeros()
  };
  result
}

val xperm4 : (xlenbits, xlenbits) -> xlenbits
function xperm4(rs1_val, rs2_val) =
  if __isla_use_extra_ops then isla_xperm4(rs1_val, rs2_val)
  else xperm4_default(rs1_val, rs2_val)
```

### 指令语义和用法

`xperm8 rd, rs1, rs2`：把 `rs2` 的每个 byte 当成索引，从 `rs1` 中取对应 byte 写到结果同位置；如果 `8 * index >= xlen`，该结果 byte 为 0。

`xperm4 rd, rs1, rs2`：与 `xperm8` 相同，但粒度为 nibble，使用 `4 * index < xlen` 判断是否越界。

### 改动理由

原始实现含有由 `rs2` 数据决定的动态索引，如 `rs1_val[8*index+7..8*index]`。对符号 `rs2`，这会产生符号下标和动态切片问题。Isla primitive 可以把 permutation 作为一个整体操作交给后端处理。

### 改动部分语义

非 SYMBOLIC 原始执行体保持在上方。SYMBOLIC 分支中 `__isla_use_extra_ops == false` 仍调用 `xperm*_default`；打开后调用 `isla_xperm*`。review 重点是确认 Isla primitive 对越界索引写 0，并且 byte/nibble 顺序与 Sail 默认实现一致。

## 4. `model/extensions/V/vext_control.sail`

### 改动代码

#### `read_vreg`

```sail
val isla_read_vreg = pure "isla_read_vreg" :
  forall 'n 'sew, 'n >= 0 & is_sew_bitsize('sew) .
  (int('n), int('sew), int, vlenbits, vlenbits, vlenbits, vlenbits, vlenbits, vlenbits, vlenbits, vlenbits) -> vector('n, bits('sew))

function read_vreg_extra(num_elem, SEW, LMUL_pow, vrid) = {
  let vrid_val = unsigned(vregidx_bits(vrid));
  let LMUL_pow_reg = if LMUL_pow < 0 then 0 else LMUL_pow;
  let LMUL = 2 ^ LMUL_pow_reg;
  let vrid_end = vrid_val + LMUL;
  assert(vrid_end <= 32, "Invalid register group: group " ^ dec_str(vrid_val) ^ " ends at " ^ dec_str(vrid_end) ^ " and overflows the largest register number (32).");
  assert(vrid_val % LMUL == 0, "Invalid register group: group " ^ dec_str(vrid_val) ^ " is not a multiple of its EMUL " ^ dec_str(LMUL) ^ ".");

  let zero_vreg : vlenbits = zeros();
  isla_read_vreg(
    num_elem,
    SEW,
    0,
    V(vrid),
    if vrid_val + 1 < 32 then V(vrid + 1) else zero_vreg,
    if vrid_val + 2 < 32 then V(vrid + 2) else zero_vreg,
    if vrid_val + 3 < 32 then V(vrid + 3) else zero_vreg,
    if vrid_val + 4 < 32 then V(vrid + 4) else zero_vreg,
    if vrid_val + 5 < 32 then V(vrid + 5) else zero_vreg,
    if vrid_val + 6 < 32 then V(vrid + 6) else zero_vreg,
    if vrid_val + 7 < 32 then V(vrid + 7) else zero_vreg
  )
}

function read_vreg(num_elem, SEW, LMUL_pow, vrid) =
  if __isla_use_extra_ops then read_vreg_extra_by_sew(num_elem, SEW, LMUL_pow, vrid)
  else read_vreg_default(num_elem, SEW, LMUL_pow, vrid)
```

#### `write_vreg`

```sail
val isla_pack_vreg = pure "isla_pack_vreg" : forall 'n 'sew, 'n >= 0 & is_sew_bitsize('sew) . (int('sew), int, vector('n, bits('sew))) -> vector(8, vlenbits)

function write_vreg_extra(num_elem, SEW, LMUL_pow, vrid, vec) = {
  let group_size = 2 ^ max(LMUL_pow, 0);
  let packed : vector(8, vlenbits) = match SEW {
    8  => isla_pack_vreg(8, vlen, vec),
    16 => isla_pack_vreg(16, vlen, vec),
    32 => isla_pack_vreg(32, vlen, vec),
    64 => isla_pack_vreg(64, vlen, vec),
  };
  V(vrid) = packed[0];
  if group_size > 1 then V(vrid + 1) = packed[1];
  if group_size > 2 then V(vrid + 2) = packed[2];
  if group_size > 3 then V(vrid + 3) = packed[3];
  if group_size > 4 then V(vrid + 4) = packed[4];
  if group_size > 5 then V(vrid + 5) = packed[5];
  if group_size > 6 then V(vrid + 6) = packed[6];
  if group_size > 7 then V(vrid + 7) = packed[7]
}

function write_vreg(num_elem, SEW, LMUL_pow, vrid, vec) =
  if __isla_use_extra_ops then write_vreg_extra(num_elem, SEW, LMUL_pow, vrid, vec)
  else write_vreg_default(num_elem, SEW, LMUL_pow, vrid, vec)
```

#### `read_vmask` / `read_vmask_carry`

```sail
function read_vmask_extra(num_elem, vm, vrid) = {
  match num_elem {
    1   => read_vmask_inner(1, vm, vrid),
    2   => read_vmask_inner(2, vm, vrid),
    4   => read_vmask_inner(4, vm, vrid),
    8   => read_vmask_inner(8, vm, vrid),
    16  => read_vmask_inner(16, vm, vrid),
    32  => read_vmask_inner(32, vm, vrid),
    64  => read_vmask_inner(64, vm, vrid),
    128 => read_vmask_inner(128, vm, vrid),
    256 => read_vmask_inner(256, vm, vrid),
    512 => read_vmask_inner(512, vm, vrid),
    _   => read_vmask_inner(num_elem, vm, vrid),
  }
}

function read_vmask(num_elem, vm, vrid) =
  if __isla_use_extra_ops then read_vmask_extra(num_elem, vm, vrid)
  else read_vmask_inner(num_elem, vm, vrid)

function read_vmask_carry(num_elem, vm, vrid) =
  if __isla_use_extra_ops then read_vmask_carry_extra(num_elem, vm, vrid)
  else read_vmask_carry_inner(num_elem, vm, vrid)
```

### 指令语义和用法

这里不是某一条单独指令的执行体，而是 V 扩展公共读写路径。所有执行 `read_vreg` / `write_vreg` / `read_vmask` / `read_vmask_carry` 的 V 指令都会间接受影响，尤其是本次暂存区改动中的 merge/move/immediate/carry/compare 指令。

`read_vreg(num_elem, SEW, LMUL_pow, vrid)`：从以 `vrid` 开头的向量寄存器组中，按 SEW 拆出 `num_elem` 个元素。

`write_vreg(num_elem, SEW, LMUL_pow, vrid, vec)`：把元素向量重新打包，写回以 `vrid` 开头的寄存器组。

`read_vmask`：`vm == 1` 表示不启用 mask，返回全 1；否则读 `v0` 或目标 mask 寄存器低 `num_elem` bit，高位补 1。

`read_vmask_carry`：carry/borrow 指令专用，`vm == 1` 表示没有 carry-in，返回全 0；否则读 mask bit。

### 改动理由

V 寄存器读写原实现依赖 `vector_init`、循环和动态 bit offset；mask 读依赖动态切片 `V(vrid)[num_elem - 1 .. 0]`。这些在符号执行时会造成动态长度或动态 slice 约束。新增代码通过 SEW/num_elem 分发，把常见长度具体化，并用 Isla primitive 处理打包/拆包。

### 改动部分语义

寄存器组合法性检查仍在 Sail 中执行，包括 `vrid_end <= 32` 和寄存器组起点对齐。extra 分支最多显式传入 8 个 V 寄存器，符合 LMUL 最大为 8 的模型假设。`write_vreg_extra` 根据 `group_size` 只写实际寄存器组内的寄存器。

## 5. `model/extensions/V/vext_utils_insts.sail`

### 改动代码

#### scalar 和立即数扩展

```sail
$else
val get_scalar : forall 'm, is_sew_bitsize('m). (regidx, int('m)) -> bits('m)
function get_scalar(rs1, SEW) = {
  match SEW {
    8  => X(rs1)[7 .. 0],
    16 => X(rs1)[15 .. 0],
    32 => X(rs1)[31 .. 0],
    64 => {
      if 64 <= xlen then X(rs1)[63 .. 0] else sign_extend(64, X(rs1))
    },
  }
}

val sign_extend_simm_to_sew : forall 'm, is_sew_bitsize('m). (bits(5), int('m)) -> bits('m)
function sign_extend_simm_to_sew(simm, SEW) = {
  match SEW {
    8  => sign_extend(8, simm),
    16 => sign_extend(16, simm),
    32 => sign_extend(32, simm),
    64 => sign_extend(64, simm),
  }
}
$endif
```

#### 8 元素写回

```sail
function write_velem_oct_vec(vd, SEW, input, i) =
  if __isla_use_extra_ops then {
    write_single_element(SEW, 8 * i + 0, vd, input[0]);
    write_single_element(SEW, 8 * i + 1, vd, input[1]);
    write_single_element(SEW, 8 * i + 2, vd, input[2]);
    write_single_element(SEW, 8 * i + 3, vd, input[3]);
    write_single_element(SEW, 8 * i + 4, vd, input[4]);
    write_single_element(SEW, 8 * i + 5, vd, input[5]);
    write_single_element(SEW, 8 * i + 6, vd, input[6]);
    write_single_element(SEW, 8 * i + 7, vd, input[7])
  } else {
    write_velem_oct_vec_default(vd, SEW, input, i)
  }
```

#### mask 初始化和向量选择 primitive

```sail
val isla_init_mask = pure "isla_init_mask" : forall 'n 'p, 'n >= 0 . (int('n), nat, int, int('p), bits('n)) -> bits('n)
val isla_vector_select = pure "isla_vector_select" : forall 'n 'm, 'n >= 0 . (bits('n), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
val isla_masktypei_result = pure "isla_masktypei_result" : forall 'n 'm 'p, 'n >= 0 . (int('n), nat, int, int('p), bits('n), bits('m), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
val isla_masktypev_result = pure "isla_masktypev_result" : forall 'n 'm 'p, 'n >= 0 . (int('n), nat, int, int('p), bits('n), vector('n, bits('m)), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
val isla_vector_rev8 = pure "isla_vector_rev8" : forall 'n 'm, 'n >= 0 & 'm >= 0. vector('n, bits('m * 8)) -> vector('n, bits('m * 8))
```

```sail
function init_masked_result(num_elem, EEW, LMUL_pow, vd_val, vm_val) = {
  if __isla_use_extra_ops then {
    let start_element : nat = match get_start_element() {
      Ok(v)   => v,
      Err(()) => return Err(())
    };
    let end_element   = get_end_element();
    let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (2 ^ (0 - LMUL_pow));
    assert(num_elem >= real_num_elem);
    Ok((vd_val, isla_init_mask(num_elem, start_element, end_element, real_num_elem, vm_val)))
  } else {
    init_masked_result_default(num_elem, EEW, LMUL_pow, vd_val, vm_val)
  }
}

function init_masked_result_carry(num_elem, EEW, LMUL_pow, vd_val) = {
  if __isla_use_extra_ops then {
    let start_element : nat = match get_start_element() {
      Ok(v)   => v,
      Err(()) => return Err(())
    };
    let end_element   = get_end_element();
    let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (2 ^ (0 - LMUL_pow));
    assert(num_elem >= real_num_elem);
    Ok((vd_val, isla_init_mask(num_elem, start_element, end_element, real_num_elem, ones())))
  } else {
    init_masked_result_carry_default(num_elem, EEW, LMUL_pow, vd_val)
  }
}

function init_masked_result_cmp(num_elem, EEW, LMUL_pow, vd_val, vm_val) = {
  if __isla_use_extra_ops then {
    let start_element : nat = match get_start_element() {
      Ok(v)   => v,
      Err(()) => return Err(())
    };
    let end_element   = get_end_element();
    let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (2 ^ (0 - LMUL_pow));
    assert(num_elem >= real_num_elem);
    Ok((vd_val, isla_init_mask(num_elem, start_element, end_element, real_num_elem, vm_val)))
  } else {
    init_masked_result_cmp_default(num_elem, EEW, LMUL_pow, vd_val, vm_val)
  }
}
```

#### `vrev8`

```sail
function vrev8(_m, input) =
  if __isla_use_extra_ops then isla_vector_rev8(input)
  else vrev8_default(_m, input)
```

### 指令语义和用法

`get_scalar` 被 `vmerge.vxm`、`vmv.v.x`、`vclmul.vx` 等向量-标量指令使用，用于把整数寄存器 `rs1` 截取或符号扩展到 SEW。

`sign_extend_simm_to_sew` 被 OPIVI 指令使用：`vadd.vi`、`vrsub.vi`、`vand.vi`、`vor.vi`、`vxor.vi`、`vsaddu.vi`、`vsadd.vi`、`vsll.vi`、`vsrl.vi`、`vsra.vi`、`vssrl.vi`、`vssra.vi`、`vmerge.vim`、`vmv.v.i`、`vmadc.vim`、`vmadc.vi`、`vadc.vim`、`vmseq.vi`、`vmsne.vi`、`vmsleu.vi`、`vmsle.vi`、`vmsgtu.vi`、`vmsgt.vi`。它把 5-bit signed immediate 扩展到当前 SEW。

`init_masked_result*` 是 V 指令公共 mask/tail/prestart 语义：`vstart` 前的元素不更新；`vl` 之后和 fractional LMUL 之外的元素属于 tail；`vm_val` 为 0 的 body 元素不更新；返回的 mask 表示哪些元素实际参与当前指令计算。

`vrev8` 是向量 crypto helper：对每个向量元素做 byte 反转，供 `vrev8.v` 和 SHA 辅助路径使用。

### 改动理由

`get_scalar` 原实现用 `X(rs1)[SEW - 1 .. 0]` 这种动态宽度 slice；`sign_extend(simm)` 在符号 SEW 上也会触发宽度推导问题。mask 初始化和向量选择原来需要遍历 `num_elem`，在 symbolic VLEN/LMUL/SEW 组合下会快速膨胀。新增 helper 通过 SEW match 和 Isla primitive 降低动态宽度、动态循环和动态向量初始化压力。

### 改动部分语义

extra 分支中的 `init_masked_result*` 返回 `vd_val` 作为初始结果，并只用 `isla_init_mask` 生成更新 mask。这与当前默认实现中 tail/mask agnostic 仍保持 `vd_val` 的 TODO 行为一致。如果后续模型真正实现 agnostic 写 1 或未定义值，这里需要同步调整 Isla primitive 或 extra 分支。

## 6. `model/extensions/V/vext_arith_insts.sail`

### 改动代码：`vmerge.vvm` / `vmv.v.v`

`MASKTYPEV` 对应汇编 `vmerge.vvm vd, vs2, vs1, v0`。改动将 merge 结果抽成 `masktypev_result`，extra 模式调用 `isla_masktypev_result`。

```sail
val masktypev_result : forall 'n 'm 'p, 'n >= 0 & is_sew_bitsize('m) .
  (int('n), nat, int, int('p), bits('n), vector('n, bits('m)), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
function masktypev_result(num_elem, start_element, end_element, real_num_elem, vm_val, vs1_val, vs2_val, vd_val) =
  if __isla_use_extra_ops then isla_masktypev_result(num_elem, start_element, end_element, real_num_elem, vm_val, vs1_val, vs2_val, vd_val)
  else masktypev_result_default(num_elem, start_element, end_element, real_num_elem, vm_val, vs1_val, vs2_val, vd_val)

function clause execute MASKTYPEV(vs2, vs1, vd) = {
  let start_element : nat = match get_start_element() {
    Ok(v)   => v,
    Err(()) => return Illegal_Instruction()
  };
  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); // max(VLMAX,VLEN/SEW))
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); // VLMAX

  if illegal_vd_masked(vd) |
     not(valid_reg_group(vs1, LMUL_pow)) |
     not(valid_reg_group(vs2, LMUL_pow)) |
     not(valid_reg_group(vd, LMUL_pow))
  then return Illegal_Instruction();

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : bits('n)             = read_vmask(num_elem, 0b0, zvreg);
  let vs1_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let result = masktypev_result(num_elem, start_element, end_element, real_num_elem, vm_val, vs1_val, vs2_val, vd_val);

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}
```

`MOVETYPEV` 对应汇编 `vmv.v.v vd, vs1`。改动将“mask 为 1 的元素从输入覆盖到 initial_result”抽成 `vector_select_result`。

```sail
val vector_select_result : forall 'n 'm, 'n >= 0 .
  (int('n), bits('n), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
function vector_select_result(num_elem, mask, initial_result, input) =
  if __isla_use_extra_ops then isla_vector_select(mask, initial_result, input)
  else vector_select_result_default(num_elem, mask, initial_result, input)

function clause execute MOVETYPEV(vs1, vd) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_vd_unmasked() |
     not(valid_reg_group(vs1, LMUL_pow)) |
     not(valid_reg_group(vd, LMUL_pow))
  then return Illegal_Instruction();

  let 'n = num_elem;
  let 'm = SEW;

  let vs1_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) : (vector('n, bits('m)), bits('n)) = match init_masked_result(num_elem, SEW, LMUL_pow, vd_val, ones()) {
    Ok(v)   => v,
    Err(()) => return Illegal_Instruction()
  };
  let result = vector_select_result(num_elem, mask, initial_result, vs1_val);

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}
```

### 指令语义和用法：OPIVV

`vmerge.vvm vd, vs2, vs1, v0`：对每个 body 元素，如果 `v0[i] == 1`，结果取 `vs1[i]`，否则取 `vs2[i]`；prestart/tail 保持原目标寄存器语义。

`vmv.v.v vd, vs1`：把 `vs1` 的 active 元素复制到 `vd`，不显式使用 `v0` mask。

### 改动代码：`vmerge.vxm` / `vmv.v.x`

```sail
val masktypei_result : forall 'n 'm 'p, 'n >= 0 & is_sew_bitsize('m) .
  (int('n), nat, int, int('p), bits('n), bits('m), vector('n, bits('m)), vector('n, bits('m))) -> vector('n, bits('m))
function masktypei_result(num_elem, start_element, end_element, real_num_elem, vm_val, scalar_val, vs2_val, vd_val) =
  if __isla_use_extra_ops then isla_masktypei_result(num_elem, start_element, end_element, real_num_elem, vm_val, scalar_val, vs2_val, vd_val)
  else masktypei_result_default(num_elem, start_element, end_element, real_num_elem, vm_val, scalar_val, vs2_val, vd_val)

function clause execute MASKTYPEX(vs2, rs1, vd) = {
  let start_element : nat = match get_start_element() {
    Ok(v)   => v,
    Err(()) => return Illegal_Instruction()
  };

  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); // max(VLMAX,VLEN/SEW))
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); // VLMAX

  if illegal_vd_masked(vd) |
     not(valid_reg_group(vs2, LMUL_pow)) |
     not(valid_reg_group(vd, LMUL_pow))
  then return Illegal_Instruction();

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : bits('n)             = read_vmask(num_elem, 0b0, zvreg);
  let rs1_val : bits('m)             = get_scalar(rs1, SEW);
  let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let result = masktypei_result(num_elem, start_element, end_element, real_num_elem, vm_val, rs1_val, vs2_val, vd_val);

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}
```

`MOVETYPEX` 增加默认实现和按 SEW/LMUL 具体化的 extra 实现：

```sail
val execute_movetypex_extra_with_num_elem : forall 'n 'm, 'n >= 0 & is_sew_bitsize('m).
  (int('n), int('m), LMUL_pow, regidx, vregidx) -> ExecutionResult
function execute_movetypex_extra_with_num_elem(num_elem, SEW, LMUL_pow, rs1, vd) = {
  if illegal_vd_unmasked() | not(valid_reg_group(vd, LMUL_pow))
  then return Illegal_Instruction();

  let 'n = num_elem;
  let 'm = SEW;

  let rs1_val : bits('m)             = get_scalar(rs1, 'm);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) : (vector('n, bits('m)), bits('n)) = match init_masked_result(num_elem, SEW, LMUL_pow, vd_val, ones()) {
    Ok(v)   => v,
    Err(()) => return Illegal_Instruction()
  };
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == 0b1 then result[i] = rs1_val
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}

function clause execute MOVETYPEX(rs1, vd) =
  if __isla_use_extra_ops then {
  let SEW_extra = get_sew();
  let LMUL_pow_extra = get_lmul_pow();
  let LMUL_pow_reg = if LMUL_pow_extra < 0 then 0 else LMUL_pow_extra;
  match SEW_extra {
    8 => match LMUL_pow_reg {
      0 => execute_movetypex_extra_with_num_elem(32, 8, LMUL_pow_extra, rs1, vd),
      1 => execute_movetypex_extra_with_num_elem(64, 8, LMUL_pow_extra, rs1, vd),
      2 => execute_movetypex_extra_with_num_elem(128, 8, LMUL_pow_extra, rs1, vd),
      3 => execute_movetypex_extra_with_num_elem(256, 8, LMUL_pow_extra, rs1, vd),
      _ => Illegal_Instruction(),
    },
    16 => match LMUL_pow_reg {
      0 => execute_movetypex_extra_with_num_elem(16, 16, LMUL_pow_extra, rs1, vd),
      1 => execute_movetypex_extra_with_num_elem(32, 16, LMUL_pow_extra, rs1, vd),
      2 => execute_movetypex_extra_with_num_elem(64, 16, LMUL_pow_extra, rs1, vd),
      3 => execute_movetypex_extra_with_num_elem(128, 16, LMUL_pow_extra, rs1, vd),
      _ => Illegal_Instruction(),
    },
    32 => match LMUL_pow_reg {
      0 => execute_movetypex_extra_with_num_elem(8, 32, LMUL_pow_extra, rs1, vd),
      1 => execute_movetypex_extra_with_num_elem(16, 32, LMUL_pow_extra, rs1, vd),
      2 => execute_movetypex_extra_with_num_elem(32, 32, LMUL_pow_extra, rs1, vd),
      3 => execute_movetypex_extra_with_num_elem(64, 32, LMUL_pow_extra, rs1, vd),
      _ => Illegal_Instruction(),
    },
    64 => match LMUL_pow_reg {
      0 => execute_movetypex_extra_with_num_elem(4, 64, LMUL_pow_extra, rs1, vd),
      1 => execute_movetypex_extra_with_num_elem(8, 64, LMUL_pow_extra, rs1, vd),
      2 => execute_movetypex_extra_with_num_elem(16, 64, LMUL_pow_extra, rs1, vd),
      3 => execute_movetypex_extra_with_num_elem(32, 64, LMUL_pow_extra, rs1, vd),
      _ => Illegal_Instruction(),
    },
  }
} else {
  execute_movetypex_default(rs1, vd)
}
```

### 指令语义和用法：OPIVX

`vmerge.vxm vd, vs2, rs1, v0`：对每个 body 元素，如果 `v0[i] == 1`，结果取 scalar `rs1` 扩展/截断到 SEW 后的值，否则取 `vs2[i]`。

`vmv.v.x vd, rs1`：把 scalar `rs1` 扩展/截断到 SEW 后广播到 `vd` 的 active 元素。

### 改动代码：OPIVI

OPIVI 执行体的关键变化是 `sign_extend(simm)` 改为 `sign_extend_simm_to_sew(simm, SEW)`，并让 `MASKTYPEI` 复用 `masktypei_result`。

```sail
function clause execute VITYPE(funct6, vm, vs2, simm, vd) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) |
     not(valid_reg_group(vs2, LMUL_pow)) |
     not(valid_reg_group(vd, LMUL_pow))
  then return Illegal_Instruction();

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : bits('n)             = read_vmask(num_elem, vm, zvreg);
  let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);
  let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) : (vector('n, bits('m)), bits('n)) = match init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val) {
    Ok(v)   => v,
    Err(()) => return Illegal_Instruction()
  };
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == 0b1 then {
      result[i] = match funct6 {
        VI_VADD    => vs2_val[i] + imm_val,
        VI_VRSUB   => imm_val - vs2_val[i],
        VI_VAND    => vs2_val[i] & imm_val,
        VI_VOR     => vs2_val[i] | imm_val,
        VI_VXOR    => vs2_val[i] ^ imm_val,
        VI_VSADDU  => unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, imm_val) ),
        VI_VSADD   => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, imm_val) ),
        VI_VSLL    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        vs2_val[i] << shift_amount
                      },
        VI_VSRL    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        vs2_val[i] >> shift_amount
                      },
        VI_VSRA    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        (v_double >> shift_amount)[SEW - 1 .. 0]
                      },
        VI_VSSRL   => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        (vs2_val[i] >> shift_amount) + zero_extend('m, rounding_incr)
                      },
        VI_VSSRA   => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        (v_double >> shift_amount)[SEW - 1 .. 0] + zero_extend('m, rounding_incr)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}
```

```sail
let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);
let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
let result = masktypei_result(num_elem, start_element, end_element, real_num_elem, vm_val, imm_val, vs2_val, vd_val);

let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);
```

### 指令语义和用法：OPIVI

`vadd.vi vd, vs2, simm[, vm]`：active 元素执行 `vs2[i] + sign_extend(simm)`。

`vrsub.vi vd, vs2, simm[, vm]`：active 元素执行 `sign_extend(simm) - vs2[i]`。

`vand.vi` / `vor.vi` / `vxor.vi`：active 元素执行与/或/异或。

`vsaddu.vi` / `vsadd.vi`：active 元素执行无符号/有符号饱和加法，必要时设置 `vxsat`。

`vsll.vi` / `vsrl.vi` / `vsra.vi`：按立即数低 log2(SEW) 位做左移、逻辑右移、算术右移。

`vssrl.vi` / `vssra.vi`：带 fixed-point rounding increment 的逻辑/算术右移。

`vmerge.vim vd, vs2, simm, v0`：按 `v0` 选择 immediate 或 `vs2[i]`。

`vmv.v.i vd, simm`：把 5-bit signed immediate 扩展到 SEW 后广播到 active 元素。

### 改动理由

`vmerge` / `vmv` 原始实现中有按 `num_elem` 的循环、动态 mask、动态向量初始化；OPIVI 原始实现中的 `sign_extend(simm)` 依赖上下文推导目标宽度，符号 SEW 下不稳定。新增 helper 把结果选择逻辑和立即数扩展具体化，减少 Isla IR 中的动态宽度和动态循环。

### 改动部分语义

非 SYMBOLIC 分支保持原代码。SYMBOLIC 分支中的 `vmerge.vvm`、`vmerge.vxm`、`vmerge.vim` 在 extra 模式下将“prestart/tail/body mask 的选择结果”交给 Isla primitive；`vmv.v.v` 用 `isla_vector_select` 做按 mask 选择；`vmv.v.x` extra 分支把 `num_elem` 具体化后再执行原逻辑。

需要重点 review：`MOVETYPEX` extra 分支当前硬编码了 `SEW`/`LMUL_pow_reg` 到 `num_elem` 的表，例如 SEW=8、LMUL=1 时使用 32 个元素。这与 VLEN=256 的配置一致；如果同一模型要支持其他 VLEN，应该确认该分发表是否需要改成由 `vlen / SEW` 推导，或者增加更多 VLEN 组合。

## 7. `model/extensions/V/vext_vm_insts.sail`

### 改动代码

本文件的改动都集中在 OPIVI mask/carry/compare 指令中，将 `sign_extend(simm)` 改为 `sign_extend_simm_to_sew(simm, SEW)`。原始代码保留在 `$ifndef SYMBOLIC` 分支。

```sail
let vm_val  : bits('n)             = read_vmask_carry(num_elem, 0b0, zvreg);
let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);
let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
let vd_val  : bits('n)             = read_vmask(num_elem, 0b0, vd);

VIM_VMADC    => unsigned(vs2_val[i]) + unsigned(imm_val) + (if vm_val[i] == 0b1 then 1 else 0) > 2 ^ SEW - 1
```

```sail
let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);

VIMC_VMADC    => unsigned(vs2_val[i]) + unsigned(imm_val) > 2 ^ SEW - 1
```

```sail
let vm_val  : bits('n)             = read_vmask_carry(num_elem, 0b0, zvreg);
let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);

VIMS_VADC     => to_bits_unsafe(SEW, unsigned(vs2_val[i]) + unsigned(imm_val) + (if vm_val[i] == 0b1 then 1 else 0))
```

```sail
let vm_val  : bits('n)             = read_vmask(num_elem, vm, zvreg);
let imm_val : bits('m)             = sign_extend_simm_to_sew(simm, SEW);
let vs2_val : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
let vd_val  : bits('n)             = read_vmask(num_elem, 0b0, vd);

VICMP_VMSEQ    => vs2_val[i] == imm_val,
VICMP_VMSNE    => vs2_val[i] != imm_val,
VICMP_VMSLEU   => unsigned(vs2_val[i]) <= unsigned(imm_val),
VICMP_VMSLE    => signed(vs2_val[i]) <= signed(imm_val),
VICMP_VMSGTU   => unsigned(vs2_val[i]) > unsigned(imm_val),
VICMP_VMSGT    => signed(vs2_val[i]) > signed(imm_val)
```

### 指令语义和用法

`vmadc.vim vd, vs2, simm, v0`：对每个 active 元素计算 `vs2[i] + imm + carry_in` 是否产生进位，结果写入 mask 寄存器 `vd`。

`vmadc.vi vd, vs2, simm`：不使用 carry-in，只判断 `vs2[i] + imm` 是否产生进位。

`vadc.vim vd, vs2, simm, v0`：对每个 active 元素计算 `vs2[i] + imm + carry_in` 的 SEW 位和，结果写向量寄存器。

`vmseq.vi` / `vmsne.vi`：比较 `vs2[i]` 与 sign-extended immediate 是否相等/不等，结果写 mask。

`vmsleu.vi` / `vmsle.vi`：比较 `vs2[i] <= imm`，分别按无符号/有符号解释。

`vmsgtu.vi` / `vmsgt.vi`：比较 `vs2[i] > imm`，分别按无符号/有符号解释。

### 改动理由

这些指令共享 5-bit signed immediate。原始 `sign_extend(simm)` 依赖目标类型推导为 `bits('m)`，但在 SYMBOLIC 分支中 `SEW` 会参与类型/宽度约束，容易触发动态宽度问题。`sign_extend_simm_to_sew` 通过 SEW=8/16/32/64 显式分支让宽度固定。

### 改动部分语义

只有 immediate 扩展方式被替换，算术、比较、mask 写回逻辑保持原有结构。review 重点是确认 `sign_extend_simm_to_sew` 与原先 `let imm_val : bits('m) = sign_extend(simm)` 在所有 SEW 上等价。

## 8. 新增空文件 `.codex`

### 改动代码

暂存区新增 `.codex`，文件大小为 0：

```text
diff --git a/.codex b/.codex
new file mode 100644
index 00000000..e69de29b
```

### 语义和理由

这是空文件，对 Sail 模型、指令语义和编译行为没有影响。从 review 角度看，它更像工具标记或误暂存文件；如果没有明确用途，建议从暂存区移除，避免提交无语义文件。

## 9. 新增文本文件 `diff`

### 改动代码

暂存区新增了一个名为 `diff` 的普通文本文件，内容是一段没有应用到源码的补丁。该补丁目标是 `model/core/regs.sail`，核心片段如下：

```diff
+$ifdef SYMBOLIC
+register x0 : regtype
+
+let GPRs : vector(32, dec, register(xlenbits)) = [
+	ref x31,
+    ref x30,
+    ref x29,
+    ref x28,
+    ref x27,
+    ref x26,
+    ref x25,
+    ref x24,
+    ref x23,
+    ref x22,
+    ref x21,
+    ref x20,
+    ref x19,
+    ref x18,
+    ref x17,
+    ref x16,
+    ref x15,
+    ref x14,
+    ref x13,
+    ref x12,
+    ref x11,
+    ref x10,
+    ref x9,
+    ref x8,
+    ref x7,
+    ref x6,
+    ref x5,
+    ref x4,
+    ref x3,
+    ref x2,
+    ref x1,
+    ref x0
+]
+
+register __isla_vector_gpr: bool = false
+
+val rX_from_vector = monadic "read_register_from_vector" : forall 'n, 0 <= 'n <= 31. (int('n), vector(32, dec, register(xlenbits))) -> xlenbits
+
+function get_X_bits(Regidx(i) : regidx) = if __isla_vector_gpr then rX_from_vector(unsigned(i), GPRs) else rX_bits(Regidx(i))
+
+val wX_from_vector = monadic "write_register_from_vector" : forall 'n, 0 <= 'n <= 31. (int('n), xlenbits, vector(32, dec, register(xlenbits))) -> unit
+
+function set_X_bits(Regidx(i) : regidx, data : xlenbits) = {
+    if __isla_vector_gpr then wX_from_vector(unsigned(i), data, GPRs) else wX_bits(Regidx(i), data)
+}
+$endif
+
+overload X = {get_X_bits, set_X_bits, get_X, set_X}
```

### 涉及语义

由于这只是一个名为 `diff` 的新增文本文件，不是对 `model/core/regs.sail` 的实际修改，所以当前暂存区对模型没有这部分语义影响。

如果这段补丁未来被真正应用，它的意图是为 SYMBOLIC 模式增加基于寄存器引用向量的 GPR 读写路径：

`__isla_vector_gpr == false` 时仍使用原 `rX_bits` / `wX_bits` / `rX` / `wX`。

`__isla_vector_gpr == true` 时用 `read_register_from_vector` / `write_register_from_vector` 从 `GPRs` 向量读写寄存器，意图是减少对 32 个 GPR 的分支选择展开。

### review 结论

这个文件目前是暂存 artifact，不是源码改动。若目标是提交 Sail 模型修复，应确认是否误暂存；若目标是保留设计记录，应改名放到报告目录或文档目录，并说明它不是已应用补丁。

## 8. 补充测试：`VLSEGTYPE` / `VSSEGTYPE` 的 assert 与 match 对比

### 背景

本报告原始内容针对 `../sail-riscv` 暂存区中的 `match` 具体化实现。后续为了验证“只用 `assert` 限制符号值域是否足够让 Isla 枚举”，worktree 中曾把若干薄分派 `match` 改为 `assert(...)` 限域后继续调用泛型实现，例如：

```sail
function read_vreg_seg_nf(num_elem, SEW, LMUL_pow, nf, vrid) = {
  assert(nf == 1 | nf == 2 | nf == 3 | nf == 4 | nf == 5 | nf == 6 | nf == 7 | nf == 8);
  read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, nf, vrid)
}
```

对照的暂存区 `match` 版本为：

```sail
function read_vreg_seg_nf(num_elem, SEW, LMUL_pow, nf, vrid) = {
  match nf {
    1 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 1, vrid),
    2 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 2, vrid),
    3 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 3, vrid),
    4 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 4, vrid),
    5 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 5, vrid),
    6 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 6, vrid),
    7 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 7, vrid),
    8 => read_vreg_seg_num_elem(num_elem, SEW, LMUL_pow, 8, vrid),
  }
}
```

`match` 与 `assert` 的关键区别是：`match` 在每个 arm 中把实参替换成字面量常量，例如 `nf = 1`；`assert` 只给当前路径增加约束，变量本身仍以符号值形式传入后续函数。因此二者都会触发枚举，但后续常量传播效果不同。

### 测试方法

为了不修改两个仓库的 git 状态，本次测试使用两套 IR：

1. `assert` 版本：直接使用当前 worktree 已生成的 `./rv64d.ir`。
2. `match` 版本：复制 `../sail-riscv` 到 `/tmp/sail-riscv-match`，再用 `git -C ../sail-riscv show :<path>` 将暂存区中的 `model/` 文件覆盖到 `/tmp` 副本，重新配置并编译 `/tmp/sail-riscv-match/build/model/rv64d.ir`。

运行命令等价于：

```sh
timeout 120 ./target/release/isarch \
  -A <rv64d.ir> \
  -C ./configs/riscv64_difftest.toml \
  --verbose --debug=fmlgcsra --probe-all --trace-all \
  --itrace=<trace-file> \
  solve-state --clause=<VLSEGTYPE|VSSEGTYPE>
```

日志写入 `/tmp/isla-vlseg-compare/assert/` 和 `/tmp/isla-vlseg-compare/match/`，没有写入 git 索引。

### 测试结果

| 版本 | Clause | 结果 | elapsed | maxrss | 超时前已完成路径 |
| --- | --- | --- | --- | --- | --- |
| assert | `VLSEGTYPE` | timeout，退出码 124 | `2:00.04` | `636628KB` | 3 |
| assert | `VSSEGTYPE` | timeout，退出码 124 | `2:00.04` | `685056KB` | 5 |
| match | `VLSEGTYPE` | timeout，退出码 124 | `2:00.03` | `446872KB` | 3 |
| match | `VSSEGTYPE` | timeout，退出码 124 | `2:00.02` | `441340KB` | 3 |

四组运行都没有在 120 秒内完成。日志中没有 `ExecError`、panic 或 Rust/Sail 异常；只有既有的 `No primop parse_hex_bits`、`emulator_write_tag`、`emulator_read_tag`、`valid_reservation` 提示。

### 行为差异

`assert` 版本和 `match` 版本的最终状态都是 timeout，但超时前探索到的位置不同。

`assert` 版 `VLSEGTYPE` 已经进入 `process_vlseg` 的 active segment 分支：

```text
[FORK]: extensions/V/vext_mem_insts.sail 67:4 - 81:5
[FORK]: Symbol 738 taints: ["vstart", "vl", "vtype"]
[FORK]: core/regs.sail 281:61 - 284:3
```

`match` 版 `VLSEGTYPE` 在 120 秒结束前主要停在 `read_vreg_seg_nf` 的 `match nf` 以及后续向量寄存器读取路径：

```text
[FORK]: extensions/V/vext_utils_insts.sail 775:2 - 784:3
[FORK]: Symbol 94 taints: []
[FORK]: extensions/V/vext_control.sail 103:4 - 103:56
```

`assert` 版 `VSSEGTYPE` 在超时前已经出现 `Retire_Success` 路径：

```text
[PATH_RESULT]: 当前汇编：Some("vse64.v v17, (x0)")
[PATH_RESULT]: 当前汇编：Some("vse64.v v21, (x0)")
```

`match` 版 `VSSEGTYPE` 在超时前只看到 `Illegal_Instruction` 路径，尚未跑到同样的成功路径。

### 结论

`VLSEGTYPE` / `VSSEGTYPE` 的 timeout 不能归因于 `assert` 枚举失败。`assert` 日志中已经能看到 `read_vreg_seg_nf` 的域约束 fork，说明枚举确实发生了。真正的问题是段访存路径规模：

```sail
foreach (i from 0 to (num_elem - 1)) {
  if mask[i] == 0b1 then {
    foreach (j from 0 to (nf - 1)) {
      ...
      vmem_read(...) / vmem_write(...)
    }
  }
}
```

其中 `num_elem`、`nf`、`mask[i]`、`vstart`、`vl`、`vtype` 和访存地址/寄存器读取都会继续制造路径和表达式。`match` 可以在某些局部给后续函数更强的常量传播，但并没有消除 `num_elem * nf` 的段访存执行规模；本次实测中 `match` 和 `assert` 都 timeout。

因此，若后续要真正解决 `VLSEGTYPE` / `VSSEGTYPE`，仅在 `read_vreg_seg_nf` 上选择 `match` 或 `assert` 不够。需要单独 review 是否要对段访存 mask 生成、active element 选择、或者整段 load/store 结果构造做 SYMBOLIC + `__isla_use_extra_ops` 保护下的更高层抽象。

## 重点 review 风险

1. Isla primitive 等价性：`isla_brev8`、`isla_rev8`、`isla_carryless_mul`、`isla_carryless_mulr`、`isla_count_ones`、`isla_xperm8`、`isla_xperm4`、`isla_read_vreg`、`isla_pack_vreg`、`isla_init_mask`、`isla_vector_select`、`isla_masktypei_result`、`isla_masktypev_result`、`isla_vector_rev8` 必须与默认 Sail 语义逐 bit 一致。

2. `MOVETYPEX` extra 分支 hardcode 了 SEW/LMUL 到 num_elem 的表。当前表看起来针对 VLEN=256；如果 `../sail-riscv` 还要支持其他 VLEN 配置，建议把这个表改成可随 `vlen` 推导或增加配置保护。

3. `init_masked_result*` extra 分支当前依赖“tail/mask agnostic 仍保持 `vd_val`”的现有 TODO 行为。若未来实现真正 agnostic 值，必须同步更新 `isla_init_mask` 或 extra 结果初始化策略。

4. `ZIP` / `UNZIP` 的 extra 分支把非 RV32 路径从 assert 改成 `Illegal_Instruction()`。这对符号执行更稳，但 review 时要确认与 decode 约束和测试预期一致。

5. `.codex` 和 `diff` 不是 Sail 源码语义改动。尤其 `diff` 是未应用补丁文本，建议确认是否应该在同一提交中出现。

## 建议验证

1. 编译非 SYMBOLIC 目标，确认 `$ifndef SYMBOLIC` 原始路径未被破坏。

2. 编译 SYMBOLIC/Isla 目标，确认所有新增 `pure "isla_*"` 和 `monadic` 名称都能被 Isla 侧解析。

3. 针对 K/B 扩展做指令级 solve：`CLMUL` / `CLMULH` / `CLMULR`、`XPERM8`、`XPERM4`、`ZIP`、`UNZIP`、`BREV8`、`REV8`、`CPOP`。

4. 针对 V 扩展做最小覆盖：`vmerge.vvm`、`vmv.v.v`、`vmerge.vxm`、`vmv.v.x`、`vmerge.vim`、`vmv.v.i`、`vadd.vi`、`vmadc.vim`、`vmadc.vi`、`vadc.vim`、`vmseq.vi`、`vmsgt.vi`。

5. 对 `__isla_use_extra_ops=false` 和 `true` 分别跑同一组用例，确认默认路径和 extra 路径结果一致。
