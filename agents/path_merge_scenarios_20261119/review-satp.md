# SATP 模式映射的路径合并验收

六个场景的每个输入都得到预期结果，六个场景都未达到一条完成路径的目标。E2 复现了真实模型中的整数冲突。关闭 `merge_concrete_values` 时，57 和 48 在映射返回处被判为不兼容；开启时，映射可以把四个整数合成一个带守卫的值，但调用方第一次检查位宽取值范围就又拆成四条。E5 中，开启开关还使最终路径从两条增加到五条。

## 完成路径与语义

每组三个数依次为 **off / recursive / flat** 的可满足正常完成路径数。off 关闭路径合并；列标题中的开关只控制具体值合并。B64 与 B129 逐格相同。六项均保留合并期望 1，并在场景元数据中标为 `xfail`。

| 场景 | 期望 off → 合并 | 具体值合并关 | 具体值合并开 | 期望一条的依据 |
| --- | --- | --- | --- | --- |
| E1 直接返回 match 的整数 | 4 → 1 | 4 / 4 / 4 | 4 / 4 / 4 | 四个整数共用一个返回槽，每个值有唯一的模式守卫。 |
| E2 返回 mapping 的正向结果 | 4 → 1 | 4 / 4 / 4 | 4 / 4 / 4 | 正向映射覆盖四个模式，每个输入恰有一个整数结果。 |
| E3 按宽度切片并比较两种扩展 | 4 → 1 | 4 / 4 / 4 | 4 / 4 / 4 | 临时切片有四种位宽，零扩展和符号扩展后均为 64 位，最终两个布尔值可以按守卫选择。 |
| E4 选择 VPN 每级位数再取下标 | 4 → 1 | 4 / 4 / 4 | 4 / 4 / 4 | 切片只用 10 或 9 两种位宽，最终下标统一为 10 位。 |
| E5 Bare、地址检查和翻译结果 | 5 → 1 | 5 / 2 / 2 | 5 / 5 / 5 | Bare 与翻译的三个出口都是正常返回，断言对全部输入成立，标签和负载可由输入决定。 |
| E6 两个消费者使用同一宽度 | 4 → 1 | 4 / 4 / 4 | 4 / 4 / 4 | 切片符号位和宽度比较都取自同一个模式，两个输出可以共用守卫。 |

两种开关 × 两种位向量实现 × 三种策略 × 六个场景，共 **24 PASS、48 XFAIL**。24 个 off 基线全部通过；48 个合并配置只有路径数偏离期望。两轮运行器均退出 0。另用同一 Z3 重放所有完成路径，按模式检查每个输入恰落入一个守卫，全部 336 个「输入、配置」组合覆盖完整且互斥。两种实现的输出一致。[关的逐格结果](../../output/false.md) · [开的逐格结果](../../output/true.md) · [逐路径守卫覆盖](../../output/domain.log)

### 逐输入可核对的结果

- **E1、E2** 的模式 0、1、2、3 依次返回整数 32、39、48、57。映射函数直接返回整数。测试外层将结果无损投影为 6 位，与独立字节表核对。直接把带守卫的整数写作观测寄存器会得到运行器无法重放的复合表达式，6 位覆盖所有合法返回值。
- **E3** 的地址只有第 47 位为 1。按「零扩展等于原地址，符号扩展等于原地址」排列，宽度 32、39、48、57 分别得到 `(假,假)、(假,假)、(真,假)、(真,真)`。宽度 48 时该位正好是符号位，两个比较确实能区分。
- **E4** 的 Sv32 取 `vpn[19..10]`，得到 687；其余取 `vpn[17..9]`，得到 350。具体值合并开启时，首次区域外重试发生在 `prop@8`，对应计算 `w == 32` 之前的 `isla_type_assume`。三次二元拆分产生四个具体宽度，三个使用 9 位下标的模式也分别完成。切片后未合回一条。
- **E5** 用最高位表示 Bare。输入 4–7 均返回 `Ok(0)`。输入 0、1 的地址非规范，均返回 `Err(1)`；输入 2 经辅助函数返回并调整为 `Err(3)`；输入 3 得到 `Ok(1)`。关闭具体值合并时，最终两条守卫分别覆盖 Err 的 `{0,1,2}` 和 Ok 的 `{3,4,5,6,7}`。开启后，守卫变为 `{0}、{1}、{2}、{3}、{4,5,6,7}`。
- **E6** 的「切片符号位，宽度至少为 48」依次为 `(1,假)、(0,假)、(1,真)、(0,真)`。两种具体值配置下，四条完成路径各覆盖一个模式；独立规格同时检查两个输出。开启时只在第一次使用宽度前的类型约束处观测到三次区域外重试，第二个消费者没有再把每条路径分成四条。

## 为什么会留下多条路径

**关闭具体值合并时，拒绝发生在整数返回槽。** E2 的 IR 调用 `mode_width_forwards : (%bv2) -> %i64`。在 B64 recursive 上跟踪不等具体值的拒绝分支，先看到 `I64(57)/I64(48)`，随后还有 `57/39` 等组合，拒绝原因为 `IncompatibleState`。真实 LOAD 的同类日志位于 `satp_mode_width_forwards@1/6/11`；最小模型重新编译后的 PC 不同。`merge_states` 在此配置调用严格值合并，对不等 I64 返回 `IncompatibleMerge`。分组可以把失败成员分别保留，无法消除返回槽自身的限制。这对应分组审查中的同桶试合失败，也对应原则审计中的“具体 I64、字符串及复合值”。[本轮 E2 严格模式跟踪](../../output/diagnosis/E2-mapping-width/strict.log) · [分组审查](../../../../agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/groupmerge-review.md) · [原则审计](../../../../agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/merge-principle-audit.md)

**开启时可以合并映射，能否保持到出口取决于第一次消费。** `merge_val_inner_mode` 可将不同 I64 构造成 `Val::Guarded`。读取需要确定具体值的操作数时，`resolve_value` 要求选定守卫；若当前区域外有两个可行选择，`retry` 为二者分别继续执行。E1、E2、E3、E6 在 `prop@6`，E4 在 `prop@8`，B64 recursive 均观测到三次区域外重试，对应编译器插入的取值范围检查。以 E2 为例，开启时每条完成路径保留三条合并记录。这解释了为何四个返回值能在内部合并，最终仍数到四条。[严格值与带守卫值的构造](../../isla-lib/src/primop_util.rs#L864) · [区域合并的配置选择](../../isla-lib/src/executor/region_engine.rs#L779) · [具体值消费和重试](../../isla-lib/src/executor/concrete_values.rs#L31) · [本轮位置跟踪](../../output/diagnosis/)

**E5 有两处不同的拒绝。** 严格模式在映射内部保留不同 I64，外层仍能把返回值合并为按标签取负载的结果。最后 `prop@6` 按 Ok/Err 投影，跟踪中两臂的 `MixedBits` 合并报 `IncompatibleState`，留下上表的两个标签组。开启后，外层区域在 `translate@37/51/62` 分别为宽度约束、断言中的整数转换、切片上界计算重试。随后 `translate@72` 的 `subrange_bits` 报 `RetryOperand`，区域推演退出；区域外在 `translate@37` 再按宽度重试，最终留下 Bare 加四个宽度。这里还涉及原则审计记录的操作数重试限制。所有这些 PC 均来自本轮 IR，定位实验使用同一 debug B64 和 recursive 配置。[严格模式跟踪](../../output/diagnosis/E5-translate-result/strict.log) · [开启时的重试与拒绝](../../output/diagnosis/E5-translate-result/trace.log) · [E5 IR](../../output/true/E5-translate-result/B64/model.ir)

## 版本与复现

本机 Isla 基线 `dc9e539626c3fa2e073d9961da102d21839282fc`，分支 `test/merge-satp-20261119`。Sail 0.20.1（446fb477）和该工作树的 Isla 插件生成 IR。debug B64/B129 的 `ldd` 均解析到官方 `libz3.so.5.4`，Z3 命令行版本为 5.4.0（d6c9b4fbb）。property 固定 `-T 2`，运行器给每条编译、执行、重放命令 30 秒外限。只运行 E 组。E1–E4、E6 用 2 位模式编码；E5 用 3 位，最高位覆盖 Bare 提前返回。场景独立于 RISC-V 模型。涉及的真实 Sail 位置为父仓库 `sail-riscv/model/sys/vmem.sail` 的 `pt_walk`、`satp_mode_width` 和 `translateAddrWithPBMT`。[构建日志](../../output/build.log) · [本轮生成的 IR 哈希](../../output/ir.sha256)

在指定 Isla 工作树根目录运行以下命令。运行器的编号校验从 A–D 扩到 A–E。该版本的 property 和运行器都没有具体值合并的命令行开关；下面的启动脚本在运行器刚生成的 TOML 的 `[execution_limits.path_merge]` 表内追加显式值，随后原样调用所选位向量实现。每次配置、IR、路径 JSON 和运行日志均位于各自的输出目录。

```sh
set -eu
scenario_z3="$HOME/.local/opt/z3-official-d6c9b4fbb"
export LD_LIBRARY_PATH="$scenario_z3/lib" LIBRARY_PATH="$scenario_z3/lib"
export PATH="$scenario_z3/bin:$PATH"
export CARGO_TARGET_DIR="$PWD/output/target"
export PROPERTY_DEBUG_BIN="$CARGO_TARGET_DIR/debug"
make -C isla-sail
cargo build --locked -j 4 --bin isla-property --bin isla-property129

mkdir -p output/config-bin
cat > output/config-bin/isla-property <<'SH'
#!/bin/sh
set -eu
test "$3" = -C
case "$MERGE_CONCRETE_VALUES" in true|false) ;; *) exit 64 ;; esac
printf 'merge_concrete_values = %s\n' "$MERGE_CONCRETE_VALUES" >> "$4"
exec "$PROPERTY_DEBUG_BIN/${0##*/}" "$@"
SH
chmod +x output/config-bin/isla-property
ln -sf isla-property output/config-bin/isla-property129
for setting in false true; do
  MERGE_CONCRETE_VALUES="$setting" python3 test/path-merge/run_scenarios.py \
    --path-merge-filter '^E' --bitvector both --property-bin-dir output/config-bin \
    --output-dir "output/$setting" --markdown "output/$setting.md"
done
```

## 场景源码

### E1 直接返回 match 选出的整数

[E1-match-width.sail](../../test/path-merge/scenarios/E1-match-width.sail)

```sail
default Order dec
$include <prelude.sail>
function mode_width(m : bits(2)) -> {32, 39, 48, 57} =
  match m { 0b00 => 32, 0b01 => 39, 0b10 => 48, _ => 57 }
register path_mode : bits(2)
register out_value : bits(6)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  out_value = get_slice_int(6, w, 0);
  let table = sail_shiftright(0x39302720, 8 * unsigned(m));
  out_value == table[5 .. 0]
}
```

### E2 直接返回 mapping 正向映射的整数

[E2-mapping-width.sail](../../test/path-merge/scenarios/E2-mapping-width.sail)

```sail
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register out_value : bits(6)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  out_value = get_slice_int(6, w, 0);
  let table = sail_shiftright(0x39302720, 8 * unsigned(m));
  out_value == table[5 .. 0]
}
```

### E3 按映射位宽切片并比较两种扩展

[E3-extend-width.sail](../../test/path-merge/scenarios/E3-extend-width.sail)

```sail
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register zero_match : bool
register out_value : bool
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let 'w = mode_width(m);
  let addr = 0x0000800000000000;
  let low = addr[w - 1 .. 0];
  let z : bits(64) = sail_zero_extend(low, 64);
  let s : bits(64) = sail_sign_extend(low, 64);
  zero_match = z == addr;
  out_value = s == addr;
  (zero_match == (m[1 .. 1] == 0b1)) & (out_value == (m == 0b11))
}
```

### E4 按模式选择 VPN 每级位数后切片

[E4-vpn-index.sail](../../test/path-merge/scenarios/E4-vpn-index.sail)

```sail
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register out_value : bits(10)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let w = mode_width(m);
  let 'n = if w == 32 then 10 else 9;
  let vpn = 0x000abc00;
  out_value = sail_zero_extend(vpn[2 * n - 1 .. n], 10);
  let table = sail_shiftright(0x015e015e015e02af, 16 * unsigned(m));
  out_value == table[9 .. 0]
}
```

### E5 从 Bare 提前返回到翻译结果

[E5-translate-result.sail](../../test/path-merge/scenarios/E5-translate-result.sail)

```sail
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
union Walk = { Ok : bits(2), Err : bits(2) }
function walk(w : {32, 39, 48, 57}) -> Walk = if w == 48 then Err(0b10) else Ok(0b11)
function translate(m : bits(3)) -> Walk = {
  if m[2 .. 2] == 0b1 then return Ok(0b00);
  let 'w = mode_width(m[1 .. 0]);
  let addr = 0x0000004000000000;
  assert(w <= length(addr));
  let low = addr[w - 1 .. 0];
  if sail_sign_extend(low, 64) != addr then Err(0b01) else
    match walk(w) { Ok(p) => Ok(xor_vec(p, 0b10)), Err(e) => Err(xor_vec(e, 0b01)) }
}
register path_mode : bits(3)
register out_value : bits(3)
function prop(m : bits(3)) -> bool = {
  path_mode = m;
  out_value = match translate(m) { Ok(p) => 0b0 @ p, Err(e) => 0b1 @ e };
  let table = sail_shiftright(0x0000000001070505, 8 * unsigned(m));
  out_value == table[2 .. 0]
}
```

### E6 同一个宽度同时用于切片和整数比较

[E6-two-consumers.sail](../../test/path-merge/scenarios/E6-two-consumers.sail)

```sail
default Order dec
$include <prelude.sail>
mapping mode_width : bits(2) <-> {32, 39, 48, 57} = {
  0b00 <-> 32, 0b01 <-> 39, 0b10 <-> 48, 0b11 <-> 57,
}
register path_mode : bits(2)
register wide : bool
register out_value : bits(1)
function prop(m : bits(2)) -> bool = {
  path_mode = m;
  let 'w = mode_width(m);
  let addr = 0x0000800080000000;
  let s : bits(64) = sail_sign_extend(addr[w - 1 .. 0], 64);
  out_value = s[63 .. 63];
  wide = w >= 48;
  (out_value == not_vec(m[0 .. 0])) & (wide == (m[1 .. 1] == 0b1))
}
```
