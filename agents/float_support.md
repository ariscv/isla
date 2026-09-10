# 浮点支持设计（feat/float-support）

## 背景

rv64d.ir（Sail RISC-V 模型）的浮点路径调用 67 个无函数体的 `val riscv_*` 外部函数
（Berkeley SoftFloat 包装，如 `riscv_f32Add`、`riscv_f32ToI32`、`riscv_f32Lt_quiet`），
形如：

```
val zriscv_f32Add : (%bv3, %bv32, %bv32) -> %struct ztuplez3z5bv5_z5bv32
```

即 `(舍入模式, IEEE 位, IEEE 位) -> (fflags, 结果位)`。IR 加载时
`insert_instr_primops`（isla-lib/src/ir.rs）只在 `Def::Extern`（带 ext 绑定字符串）
里查 primops 表，这批 `Def::Val` 查不到，`Instr::Call` 原样保留，运行时
`functions.get` 失败 → `ExecError::NoFunction`，浮点指令全部阻断。

## 方案

不重新生成 IR（需要改外部 sail-riscv），在 isla 侧把 helper 绑定到 z3 浮点理论：

1. **SMT 层**（`smt/smtlib.rs` + `smt.rs` + `simplify.rs`）：
   - 新增 `FPUnary::ToIEEE(ebits, sbits)`（FP → IEEE 位向量，`Z3_mk_fpa_to_ieee_bv`），
     与已有 `FromIEEE` 互逆，用于把浮点运算结果写回寄存器位。
   - 修复 `FPUnary::result_ty` 中 `FromIEEE` 字段序解构错误（潜在 sort 错配 bug）。
2. **primop 层**（`primop/float.rs` 新增 softfloat 段）：
   - `softfloat_dispatch(name)` 解码名 → `SfOp`（Bin/MulAdd/Sqrt/Cmp/RoundToInt/
     FpToI/IFp/FpToFp/ToBF16 × f16/f32/f64）。
   - `softfloat_call(op, args, flags_field, result_field, solver)` 构造符号表达式并
     返回 `Val::Struct{flags: bv5, result}`，字段 Name 由调用方从 IR struct 定义查出。
   - 修复既有 `fp32/64/128_from_signed/from_unsigned` 目标宽度全用 fp16 的 bug。
3. **执行器**（`executor.rs` `run_special_primop` 末分支）：解码名命中 softfloat 注册表
   → 求值实参 → 从 `shared_state.typedefs().structs` 解析返回 struct 的两个字段名
   （`ztuplez3z5bv5_z5bv<w>0/1`、比较为 `ztuplez3z5bv5_z5bool0/1`）→ 调用 → assign。
4. **配置与运行**（`configs/riscv64_difftest_fd.toml` + `scripts/run.mk`）：
   - fd 配置启用 `sys_enable_fdext` 并置 mstatus FS=Dirty。
   - `solve-%` 的 `-C` 改为 `ISA_CONFIG` 变量（默认通用配置），FD_FLOAT 目标组
     target-specific 覆盖为 fd 配置；入口 `make solve-fd-float`。

## 语义精确度（重要）

| 项 | 精确度 | 手段 |
|---|---|---|
| 数值结果 | 精确 | z3 FPA 遵循 IEEE 754；NaN/无效场景强制规范 NaN（与 SoftFloat defaultNaN 构建一致） |
| NV（无效） | 精确 | 位级判定：sNaN（静默位=0）、∞−∞、0×∞、0/0、√负数、转换越界（宽格式界常数逐舍入模式比较，界为 ±(2^a±2^b) 可精确表示） |
| DZ（除零） | 精确 | 除数为 0 且被除数有限非零非 NaN |
| Add/Sub 的 NX | 精确 | 宽格式（f32→f64，f64→fp128）重算：指数差 ≤ 阈值时宽格式和精确，往返比较；超阈值时结果为较大操作数，仅当另一操作数非零时不精确（无偏指数差按位提取，subnormal 用偏置平移正确处理） |
| Mul 的 NX | 精确 | 乘积在宽格式恒精确（2p ≤ 宽格式尾数），往返比较 |
| Sqrt 的 NX | 精确 | 结果平方与原值比较（平方在宽格式恒精确） |
| 转换的 NX | 精确 | FpToI：范围内整数值有效位数 ≤ 源格式精度 p，FromSigned/FromUnsigned 往返无损；IFp：RTZ 与 RUP 两种极端舍入结果相同 ⇔ 可精确表示 |
| FpToI/IFp 的 OF/越界 | 精确 | 逐舍入模式边界（RNE 平局靠偶、RNA 平局离零、RTZ/RDN/RUP 方向性），宽格式界常数 |
| 二元算术 OF | 近似 | `isinf(res) 且输入有限`：RNE/RMM 精确；定向舍入饱和到最大有限数时漏报（数值结果本身仍精确） |
| UF（下溢） | 近似 | `issubnormal(res) 且非零`：漏报舍入到零的极小值；subnormal 恰好精确时误报 |
| Div/FMA 的 NX | 近似 | 仅 OF\|UF。SMT 浮点理论无精确不精确谓词；Div 的宽格式商、FMA 的三输入重算均不可证精确 |

rm 参数：模型侧 checkrm（Option None 检查）保证到达 helper 的 rm ∈ 0..4（DYN 已被
frm 解析），实现中具体值直接映射、符号值显式断言该不变式后用 ite 链表达。

## 已知特征

- z3 FP theory 求解显著慢于纯位向量：F_BIN_RM_TYPE_S 这类路径量大的 clause 单机
  8 分钟 ~91 条路径；FLEQ_S 等小 clause 可正常 intime 完成。若需要全量
  `solve-fd-float`，建议调大 OUTER_TIMEOUT/SOLVE_TIMEOUT 或分批跑。
- 主机负载高时多线程 FP 求解可能触发 OOM（SIGKILL），按负载降 THREADS。

## 测试

`isla-lib/src/primop/float.rs` 的 `softfloat_tests`：21 个用例全部经真实 z3 求解
验证（数值结果、NV/DZ/OF/UF/NX 边界、NaN 传播、sNaN/qNaN 区分、信铃/静默比较、
roundToInt 的 exact 抑制、BF16 转换、dispatch 解析）。运行：`cargo test -p isla-lib
--lib softfloat`。

冒烟：`rm -rf output/ && make solve-FLEQ_S THREADS=4`（intime；日志可见
`extensions/FD/fdext_regs.sail` 激活、浮点指令具体化、f 寄存器物化）。
