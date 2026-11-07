# judge 模式（2026-11-07）

## 目标与范围

给定具体前态，输出接纳路径、规范守卫向量、执行结果和后态，并检查守卫与后态是否唯一。它是 J1 `--check-samples` 的附加功能，输入期望仍按 J1 核对。

实施基线为 `ae1a33550c6d06ecbf85ac2e2daa85d196bd3e53`，工作分支为 `feat/isla-judge`。不修改 IR、配置或其他工作树，不做 git 写操作。

## 已定设计与步骤

1. 先写失败测试：区分类、活动守卫不唯一、缺前态寄存器；同时覆盖非活动自由守卫和后态不唯一。
2. 将 J1 前半段抽为私有 `bind()`，保持等式、读取绑定、可满足性和报告行为。
3. 在同一事务和同一模型中调用既有 `materialize()`，由 isarch 回调填充 `isa_state`，读取规范守卫向量。
4. DFS 与 judge 共用守卫归一化：按父链顺序，`value = active && raw`。只对当前活动守卫构造取反析取，要求 UNSAT。
5. 回滚事务后，将生成的完整样本交给原 `check()`，要求 `Some(true)`。该检查沿用 J1 的结果、寄存器、内存值和触碰范围取反查询。
6. 运行格式化、release 构建、工作区测试，以及 ecfg4b 四场景和三个负对照。

热点文件为 `isla-lib/src/executor/samples.rs`、`merge_enumeration.rs`，以及 `src/isarch/samples.rs`、`exec.rs`、`src/isarch_main.rs`。`merge_record.rs` 只添加一行内部重导出，使相邻 samples 模块可复用私有枚举模块的辅助函数。

## 用法

在原 J1 命令的 `solve-state` 之前追加：

```sh
--check-samples in.jsonl \
--check-samples-report check.json \
--check-samples-judge judged.jsonl
```

`--check-samples-judge` 必须与 `--check-samples` 一起使用。judge 输出不得覆盖输入、检查报告或枚举输出。输出文件每次新建并清空；每个（样本，接纳路径）一行，多线程下行序不固定。

## 输出格式

```json
{"schema_version":1,"sample_id":0,"path_signature":123,"guard_order":[12,13],"guard_vector":"01","guard_assignment":{"12":false,"13":true},"guard_unique":true,"post_unique":true,"sample":{"schema_version":1,"sample_id":0,"mode":"merge","path_signature":123,"class_id":null,"truncated":false,"pre_registers":{},"post_registers":{},"isa_state":{},"pre_memory":[],"post_memory":[],"result":{"unit":true},"ret_val":"()"}}
```

`sample` 使用原 samples v1 的全部字段，指令在 `pre_registers["$instruction"]` 中。上面的空映射只为展示结构；真实输出包含路径的完整输入与后态，可以直接提取后重新喂给 J1。

`guard_order` 保存合并记录编号的父链前序；`guard_vector` 逐位对应此顺序。`guard_assignment` 按记录编号映射到布尔值，与枚举类头形状相同。非活动守卫统一为 false。

类号不从输入标签复制，输出 `sample.class_id=null`。使用方应对同一路径的全部可行规范向量排序（false 在前），用其名次反查种子表中的 `class_id`。

## 验证结果

受测版本为基线 ae1a335 加本次未提交改动；rustc/Cargo 为 1.93.1。正式构建使用默认 direct 后端，链接已有官方 Z3 `1fd1d3613`。未修改 IR、Sail 或配置。

- TDD 红测：`output/judge/tdd-red.log`，新增测试因缺少 `judge()` 而编译失败；实现后 `tdd-green.log` 中三个新增核心测试通过。
- `cargo fmt --check`、`cargo build --release --offline -j 8`：通过，最终构建日志 `output/judge/build-final2.log`。
- `cargo test --workspace --offline -j 8`：1108 通过、0 失败、6 项既有忽略；其中 isla-lib 786 通过。日志 `output/judge/test-final.log`，计数见 `test-summary.json`。没有新增忽略项。
- J1 回归覆盖相同输入的接纳／错误期望、开启 judge 前后完整报告一致，以及重新计算出的正确结果再交给 J1。活动自由守卫拒绝、非活动自由守卫通过、缺寄存器拒绝和后态不唯一拒绝均通过。
- `make solve-MRET`：退出 0、4 条用例；保留既有 `partial / unfinished-paths=1`，不作为全路径完成的证据。日志 `output/judge/make-mret.log`、`output/log/MRET.log`。

只读输入沿用 `../replay-p0/output/ecfg4b/` 的新 IR、`config-xs.toml` 与四场景原始种子。没有重新生成 IR、重设参数或计算新哈希；比较直接使用 JSON 字段。

| 场景 | 种子 | 接纳路径 | judge 秒 | 关闭 judge 的 J1 秒 | 五项验证 |
| --- | ---: | ---: | ---: | ---: | --- |
| sv39-load | 728 | 26 | 216.89 | 86.85 | PASS |
| sv39-store | 380 | 26 | 89.30 | 36.57 | PASS |
| sv48-load | 1122 | 35 | 579.12 | 290.61 | PASS |
| sv48-store | 606 | 35 | 205.09 | 118.28 | PASS |
| 合计 | 2836 | 122 | — | — | PASS |

1. 2836/2836 个种子恰好被一条路径接纳，路径号全部等于原种子的 `path_signature`。
2. 2836/2836 行的 `result`、`pre_registers`、`post_registers`、`post_memory` 与种子逐字段相同；差异 0。
3. 2836/2836 行的 `guard_unique`、`post_unique` 全部为 true。
4. 全部 122 条路径中，规范守卫向量无重复，排序名次全部等于原种子的 `class_id`，差异 0。
5. 开启和关闭 judge 的完整 J1 报告均与 ecfg4b 改动前记录相同；accepted=2836、consistent=2836、inconsistent=0。原 `completed=false` 也保持不变。

生成的完整 samples v1 共 2836 行，外部再喂入 J1 全部通过，完整报告仍与基线一致；四场景分别耗时 102.99/40.36/294.51/106.15 秒。全部行也已在 judge 内部回滚后通过原 `check()`。综合记录见 `output/judge/verification.json`，前四项及开启 judge 的报告比较另见 `judge-verification.json`。

三个负对照均为 PASS：以 Sv39 LOAD 的成功种子 38 为基础，翻转前态 x1 最低位、删除已读地址 `0x80100800` 的一个字节、将根 PTE 改为 `0x08000001` 指向排除区 `0x20000000`，并将原下级 PTE 的 8 字节同时补到新读取地址 `0x20000800`；各接纳路径数 0，judge 文件为空。输入、具体修改及完整报告分别见 `output/judge/negative-input.jsonl`、`negative-description.json`、`negative-results.json`。

四场景 judge、J1 的原始退出码均为 1、status=partial；errors 仍为 5/5/7/7，与 ecfg4b 历史排除域记录一致。执行超时、SMT 超时、终值查询超时、未完成路径和待处理批次均为 0。这些状态没有重写为 finished；本轮没有重新执行旧观察器的逐查询排除证明。

## 复现命令

从本工作树根目录执行；构建和临时目录均在本工作树。Z3 目录只读使用既有安装。

```sh
mkdir -p output/judge/tmp
export TMPDIR="$PWD/output/judge/tmp"
export RUSTFLAGS="-L native=$HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
cargo fmt --check
cargo build --release --offline -j 8
cargo test --workspace --offline -j 8
python3 output/judge/validate.py judge
python3 output/judge/validate.py j1
python3 output/judge/validate.py roundtrip
python3 output/judge/validate.py negative
python3 output/judge/validate.py verify
```

本轮验证脚本、逐字段比较结果及全部命令保存在 `output/judge/`（按仓库规则忽略）。`validate.py` 读取只读来源 `../replay-p0/output/ecfg4b/<场景>-j1/done.json` 的实际 argv，仅替换程序、输出路径和新增 judge 选项；IR、`config-xs.toml`、前态、指令、合并选项及超时参数保持相同。每场景 `-T 32`、最多四个进程，三个负对照单独用 `-T 64`；原 `--smt-timeout 5 --timeout 890` 和 900 秒外限保持不变。每次实际 argv、cwd、耗时与退出码见 `output/judge/{judge,j1,roundtrip,negative}/<场景>/done.json`。

Make 入口冒烟命令：

```sh
make -f scripts/run.mk -o build-isarch solve-MRET THREADS=64 \
  IR_FILE=../replay-p0/output/ecfg4b/rv64d.ir \
  SOLVE_CONFIG=../replay-p0/output/ecfg4b/config-xs.toml TASTIC=default
```

## 已知限制

- 缺少路径前态中的任何寄存器会报错；不会默认填值。内部不变量违反直接 panic。
- 活动守卫或后态不唯一会报错退出，不输出伪造的唯一结果。输入期望错误仍在原 J1 报告中计为不一致；judge 的后态由模型重新计算。
- 保留原 samples v1 的初始内存协议及“写后读不同值”限制；不恢复合并主迹的精确访存顺序。
- judge 不枚举完整类目录；类号反查需要同一路径的完整种子表。跨路径唯一性由使用方汇总每个输入的接纳行数判断。
- ecfg4b 已记录的排除域执行终止、原始 partial 和退出 1 仍需单列，不能写成整个符号执行无错误。
