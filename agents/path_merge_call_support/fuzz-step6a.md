# fuzz 第 6a 步：枚举符号前态配置

**结论：四场景 E2 已完整导出，5000 个 corpus entry 的第 0 步认证和独立检查全部通过。** Sv39 LOAD 为 **1359/200/26**，与历史 E2 实验一致，形状键与路径号集合也完全一致。完整 corpus 中未发现违反本轮前态域的组合；122 条 DAG 写出后重读一致。

## 配置与实现

```toml
[symbolic_registers]
cur_privilege = { allowed = ["User", "Supervisor"] }

[symbolic_registers.mstatus]
pin_mask = "0xfffffffffff3ffff"
pin_value = "0x0000000a00000000"
```

仅放开 U/S、SUM[18] 和 MXR[19]，mstatus 其余位钉回原值。也支持 `[symbolic_registers.cur_privilege]` 子表。成员名与 Sail 名称完全一致；空集合、重复、拼错成员、跨枚举成员、目标不是枚举或与位约束混用均报错。与 `--prestate`、`registers.defaults` 的同名冲突仍硬失败。

- [配置解析](../../isla-lib/src/config.rs)：`SymbolicRegisterConfig.allowed` 与现有位约束并列，由 `get_symbolic_registers` 解析。
- [初态约束](../../src/isarch/target.rs)：`apply_symbolic_csrs_to_registers` 在 `setup_pre_state` 之后、checkpoint 之前核对寄存器枚举类型，复用 `EnumMember::from_name`、`smt_value`、`symbolic`；断言成员等式的“或”。复用已有初态符号，执行寄存器和输出记录使用同一个值。不在 `reg_list` 中的声明沿用现有符号化方式建立。
- [固定编码译码](../../src/isarch/exec.rs)：独立译码使用允许集合首项作为具体上下文，避免跨求解器复用执行符号。执行仍保留完整集合；用户需选择能译出目标指令的首项。没有配置该选项时沿用原译码环境。

帮助、[README](../../README.md) 和 [CLI 规范](../../specs/isarch-cli.md) 已同步。没有改 IR、Sail、fuzz 判定或变异算法。

## 版本、边界与验证

基于 `feat/isla-sym-config` 的 `2afac05816815eb1bdceffee393bed6d6157e93c` 加本轮未提交修改。只写本工作树，不做 git 写操作；`replay-p0`、`isla-sym-prestate`、`isla-fuzz` 均只读。构建、输出、临时文件均在本工作树，没有手工计算或以哈希判断有效性。

只读来源为 `../replay-p0/output/ecfg4b/`：使用原 `rv64d.ir`、`config-xs.toml` 基础和 `enumeration.toml`，不是实验的 `rv64d-us.ir`。PMA/PMP、设备排除区、其余前态、SATP、固定机器字、指令、`class_cap=1`、`path_cap=1000000`、`sample_stride=1` 全部沿用。配置只删 mstatus 默认值并加上述两项；命令只移除 cur_privilege、mstatus 的具体前态并换本轮二进制和配置。见 [逐字段对照](../../output/fuzz-step6a/input-comparison.json)。

TDD 先验证原解析器拒绝 `allowed`、原注入拒绝枚举，译码支持缺失时测试编译失败。最终完整工作区 **1148 通过、0 失败、6 项既有忽略**，保留原 1142 项并新增 6 项；覆盖解析、非法配置、枚举五成员的 SAT/UNSAT、初态符号复用、模型输出、非 reg_list 寄存器及译码环境隔离。格式和 diff 检查通过。见 [测试汇总](../../output/fuzz-step6a/test-summary.json)、`test-workspace-official.log` 和 `test-red-*.log`。

系统默认 Z3 4.13.3 的初次全量测试在既有 `smt_init` 失败；仅改 `LD_LIBRARY_PATH` 因 SONAME 不同仍失败。最终用与历史相同的官方 Z3 库重新链接，完整构建和全部测试通过，没有修改测试或降低要求。四个真实 CLI 负例（空集合、拼错成员、跨枚举成员、同名具体前态）全部退出 1 并给出预期错误，没有 panic，见 [负例](../../output/fuzz-step6a/negative/results.json)。

E0 Sv39 LOAD：新构建 **728/136/26**，samples 与原分支二进制、ecfg4b 均逐字节相同；26 条路径的守卫位置和父关系、类号、规范向量、计数和分区逐字段一致。原分支和新构建耗时分别 369.121、395.790 秒。见 [E0 比较](../../output/fuzz-step6a/E0-canonical-comparison.json)、[完整汇总](../../output/fuzz-step6a/analysis.json)。

**原始诊断 JSON 整文件不逐字节相同。** 差异涉及运行内守卫/符号编号、未固定选择的代表值及文本结构字段顺序。这里只签收 corpus 文件逐字节一致与类目录语义一致，不能宣称所有诊断文件都稳定，见 `E0-json-differences.json`。

额外 make 冒烟：`TASTIC=default` 时新版退出 0、4 条结果，保留 `partial/unfinished-paths=1`；旧版相同。make 默认 `qfaufbv` 在旧版和新版均为 3 条结果及 Poison/退出 1，不能称该策略下通过。首次手工对照漏了策略参数，修正后旧新一致；另一次采用 ecfg4b IR 的同策略失败也保留。证据为 `mret-*.json`、`mret-parent*/`，没有为此修改代码或 IR。

## 四场景数量与耗时

数量顺序为“类数/形状数/路径数”；E0 为 ecfg4b 历史同场景数据。耗时为共享机器单次观测，线程及并发不同，不作为稳定性能比。

| 场景 | E0 | E0 秒 | E2 | E2 秒 | 线程 |
| --- | ---: | ---: | ---: | ---: | ---: |
| sv39-load | 728/136/26 | 326.386 | 1359/200/26 | 640.878 | 32 |
| sv39-store | 380/120/26 | 179.553 | 609/160/26 | 358.148 | 32 |
| sv48-load | 1122/174/35 | 472.918 | 2074/254/35 | 820.681 | 64 |
| sv48-store | 606/154/35 | 321.710 | 958/204/35 | 748.784 | 32 |

Sv39 LOAD 与实验 E2 的 1359/200/26、200 个形状键及 26 个路径号均一致，见 [实验对照](../../output/fuzz-step6a/experiment-comparison.json)。完整 E2 均保留原 E0 全部形状，没有形状消失。

首轮批量各 `-T 32`，最多同时 4 个模型进程。Sv48 LOAD 于 900 秒触发外限（含终止收尾墙钟 900.359 秒），退出 -9，保留 997 行未完成数据，没有完整结果 JSON，未签收为完整 corpus。其他模型进程全部结束后，单独 `-T 64`、同样外限 900 秒再试，墙钟 820.681 秒，超时标志为 false。未加大时限、改 class_cap 或抽样跳过类。

完整 corpus：Sv39 LOAD/STORE、Sv48 STORE 位于 `output/fuzz-step6a/<场景>-export/samples.jsonl`；Sv48 LOAD 位于 `output/fuzz-step6a/serial64/sv48-load-export/samples.jsonl`。配置分别是同组 `E2.toml`，两份配置逐字段相同。不要把首轮超时目录当作完整导出入口。

## 第 0 步、独立检查与 DAG

第 0 步扫描全部完成路径，逐个确认唯一接纳、路径号相同、结果和前后寄存器/内存相同、返回值及 isa_state 相同、守卫与后态唯一；按规范向量排序后的名次必须等于 `class_id`。独立 `--check-samples` 再要求每条 `(accepted_paths, consistent_paths, inconsistent_paths)=(1,1,0)`，完整核对 sample_id 集合与分母。

| 场景 | 第 0 步 | judge-only 总秒 | 独立检查 | 检查总秒 | DAG 路径 |
| --- | ---: | ---: | ---: | ---: | ---: |
| sv39-load | 1359/1359 | 267.930 | 1359/1359 | 210.164 | 26 |
| sv39-store | 609/609 | 167.641 | 609/609 | 49.877 | 26 |
| sv48-load | 2074/2074 | 730.998 | 2074/2074 | 487.767 | 35 |
| sv48-store | 958/958 | 350.561 | 958/958 | 206.352 | 35 |

第 0 步通过数取 `reconfirm.json`；上表耗时为完整命令墙钟，judge-only 还包含探索、建索引及后续 inputs 判定，不是纯第 0 步耗时。

全部 5000 个完整 corpus entry 通过。DAG 写出后由现有 Rust 导出器逐字段重读比对；再由独立 Python 读取 manifest 和各路径 JSON，核对路径号、守卫数与定义数，122 条全部一致。见各 `*-judge/fuzz/reconfirm.json`、`dag-manifest.json` 和 `*-check/check.json`。

**保留原始全局状态。** 完整导出与检查仍退出 1、`status=partial`，Sv39 errors=5、Sv48 errors=7；`--check-samples` 的全局 `completed=false` 也保留。执行/SMT/终值查询超时、未完成路径、待处理批次均为 0，枚举未按路径预算截断。这些与逐条 corpus 检查通过分开记录。错误日志为既有 excluded memory region 终止；本轮没有为每次错误重新逐查询出具排除域证明，不宣称域外模型全集无错误。

## 新增行为与前态合法性

形状键沿用既有解码器：访问类型、页表模式、逐级 PTE 类型与 R/W/X/U、叶级别、结果和失败原因；不直接把特权级或 SUM/MXR 放进键。只列相对 E0 新增的形状数：

| 场景 | U 访问 U=0 页被拒绝 | S 在 SUM=0 时访问 U=1 页被拒绝 | MXR 允许 X-only 后成功 | 权限通过后 A=0 异常 | 权限通过后 PMA 异常 |
| --- | ---: | ---: | ---: | ---: | ---: |
| sv39-load | 20 | 20 | 8 | 8 | 8 |
| sv39-store | 20 | 20 | 0 | 0 | 0 |
| sv48-load | 25 | 25 | 10 | 10 | 10 |
| sv48-store | 25 | 25 | 0 | 0 | 0 |

Sv39 LOAD 新增 631 类、64 个形状；Sv39 STORE 新增 229 类、40 个形状；Sv48 STORE 新增 352 类、50 个形状。STORE 的 MXR 不改变写权限，新增形状来自 U/S 和 SUM。Sv48 LOAD 新增 952 类、80 个形状；同样出现 MXR 允许读取只有执行权限的页后，成功、A=0 页异常或数据 PMA 访问异常的行为。页表多一级，新增形状数量增加，行为类别相同。

已完成的全部 5000 条前态逐项核对：`cur_privilege∈{User,Supervisor}`，`mstatus & 0xfffffffffff3ffff == 0x0000000a00000000`，违反数为 0。MPRV=0、MPP=U、SXL/UXL 编码均为 2（64 位）、FS/VS/XS/SD 及其余位保持原值，没有 E3 的 MPRV 非正常入口组合。实际 PTE/数据访问地址均在 DRAM 并避开 harness 和设备排除区。完整解码记录见各导出的 `decoded.json`、`new-shapes.json`。

这是本轮模型直接前态和具体输入的验证，不是从复位可达性证明或硬件回放。`class_cap=1` 也不意味着每个类的全部 U/S、SUM/MXR 位组合都已见证；同类中无关位常只出现一个代表值。

## 复现

从本工作树根目录执行；运行目录必须不存在，已有结果拒绝覆盖。支持脚本为 [run.py](fuzz-step6a-tools/run.py)、[analyze.py](fuzz-step6a-tools/analyze.py)。下面先完成 32 线程的三个场景，再单独跑 64 线程 Sv48 LOAD；原始各次精确 argv、环境、开始时间、退出码与墙钟在对应 `done.json`。

```sh
export GIT_OPTIONAL_LOCKS=0
export PYTHONDONTWRITEBYTECODE=1
export FUZZ_Z3_LIB="$HOME/.local/opt/z3-official-1fd1d3613/lib"
export RUSTFLAGS="-L native=$FUZZ_Z3_LIB -C link-arg=-Wl,-rpath,$FUZZ_Z3_LIB"
cargo build --release --offline --bin isarch -j 8
cargo test --workspace --offline -j 8
cargo fmt --all -- --check
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py prepare
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py baseline
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py E0
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py export sv39-load sv39-store sv48-store
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py judge sv39-load sv39-store sv48-store
python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py check sv39-load sv39-store sv48-store
# 至此其他模型进程均已结束，再单独运行 64 线程。
FUZZ_STEP6A_GROUP=serial64 python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py prepare
FUZZ_STEP6A_GROUP=serial64 FUZZ_STEP6A_THREADS=64 python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py export sv48-load
# 导出未超时时才执行以下两个检查。
FUZZ_STEP6A_GROUP=serial64 FUZZ_STEP6A_THREADS=64 python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py judge sv48-load
FUZZ_STEP6A_GROUP=serial64 FUZZ_STEP6A_THREADS=64 python3 agents/path_merge_call_support/fuzz-step6a-tools/run.py check sv48-load
python3 agents/path_merge_call_support/fuzz-step6a-tools/analyze.py --serial64-sv48-load
```

本轮没有触发“单步 40 分钟无进展”停止条件；两个 Sv48 LOAD 尝试都受同一个 900 秒上限约束。没有扩展到硬件、NEMU、真 U 入口恢复或 MPRV/MPP 的新场景。
