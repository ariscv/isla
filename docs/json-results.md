# JSON求解产物与验收

`summary.status=partial`表示存在路径采样、错误、未完成终态、用例裁剪、终值查询超时或尚未完成的批次。`finished`只表示没有观察到这些遗漏；`model-coverage=not-measured`明确不宣称全模型覆盖。`sampled-paths`统计继承采样状态的回调路径，不是被省略分支数；`omitted-cases`统计已收集用例在整理阶段被过滤或配额裁剪的数量。断言过滤单独计数，保持原来的输入合法域语义。`encoding-filtered-paths`是编码守卫拒绝的非法编码域路径。

`path-signature`用于同次运行的轨迹关联，不是跨IR稳定的源码分支ID。`provenance`记录实际命令行及显式IR、ISA配置、执行限制配置文件的SHA256。IR生成来源见`ir/provenance/manifest.json`。初态、常量primop与执行限制仍定义受测域；这些统计不证明SMT表达式中的数据条件全部被见证。

完成路径在同一个最终SMT模型中取得机器编码、三种指令表示、返回值、寄存器初态及后态（包括FPR/fcsr）、`memory-events`、`pre-memory`和`post-memory`。任一必需字段求值失败，整例不进入可重放`gen`，并记录`status=incomplete`诊断；`summary.status`为`partial`。`pre-memory`中首次触碰为写入且此前未观测的旧字节允许为`null`，这是自由初态，不表示求值失败。无访存事件时三个内存字段分别为空数组。

终值查询超时同样进入`diagnostics`，不产生不完整`gen`。增量产物尚有`pending-batches`时标为partial。外部直接杀进程不能保证正在运行的批次生成JSON，必须同时检查进程退出状态。

汇编验收要求GCC与Clang驱动均通过，且逐条`.text`字节等于JSON机器编码：

```sh
python3 test/assembly_roundtrip.py output/rv64_zFLI_S.json --report assembly-check.json
```

GCC14不识别全部BF16扩展名称，所以驱动使用其已识别的架构选项，并通过`-Wa,-march=...`把实际扩展传给支持BF16的GNU汇编器。Clang使用集成汇编器。报告记录版本、命令和每条编码；工具缺失、汇编失败、编码不一致均返回非零，不允许用`.4byte`代替文本检查。

memory的`configs/riscv64_memory_coverage.toml`在原PMA配置基础上将`match_reservation`设为符号布尔值，探索SC成功/失败。原平台配置的reservation域保持。

## 重新生成IR

`ir/provenance/`保存当前各IR的配置、模型文件哈希、模型提交、实际Sail二进制与插件哈希。工具链为带浮点IR支持的Sail0.20.1快照，版本字符串报告f4f8e458但快照无.git、未核验源码树，不能冒充普通同版本发行版；复现时须核对二进制/插件哈希。

使用新输出目录执行：

```sh
python3 scripts/regenerate_ir.py --model ../sail-riscv --sail SAIL --plugin PLUGIN --config ir/provenance/rv64d.json --output NEW_OUTPUT
```

按`manifest.json`的哈希与配置分别生成RV32、RV64/V128/V256/V512。默认`rv64d.ir`与`ir/rv64d_v128_e64.ir`内容相同。生成脚本保留必要F/V寄存器接口、转换helper及压缩编码接口，不手工修改生成IR。源码位置预算由模型仓`configs/isla/workarounds/`统一维护；代码变化时迁移坐标，IR哈希变化本身不要求改源码坐标。

## NaN-boxing控制流（2026-10-31）

`nan_unbox`恢复原Sail显式if，保留boxing高位检查的两个分支。该处不再以未经整Clause性能对照证实的收益合并为ITE。`test/float_ir/check_nan_unbox_branches.py`检查全部受支持IR；可用`--fleq-json`额外核对实际两侧见证。

这只恢复boxing有效/无效判断；有效boxing的低位仍可能是普通数、NaN、无穷等。其余ITE及数值分类条件、非法布局双工具链表示、ExecuteAs等独立review项不能据此算作已修复。恢复分支后需重新验证产物，历史样本数与性能记录仅适用于原版本。
