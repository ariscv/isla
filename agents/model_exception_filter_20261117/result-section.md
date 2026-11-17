

---

# 模型异常终态过滤

**结论（2026-11-17）**：已在指定独立工作树实现默认关闭的 TOML／CLI 开关。开启后，在见证求解和终态保存前，按配置中的 Sail 异常构造子精确过滤；被排除的终态不进入 DAG、样本或 judge。summary 与 stderr 按“构造子＋完整消息”累计次数，保留消息中的源码位置。定向回归通过；未提交、合并或 push。真实 PMP=2 缓存读回也确认四份异常被过滤，`sys/vmem.sail:214` 计数为 4；原有 41 条执行超时及 partial 状态保留。

## 交付与使用

- 工作树：`.worktree/isla-model-exc-filter-20261117`，分支 `fix/model-exception-filter-20261117`，基线 `96c41a826c02937cd11973d734af0fcba053b86b` 加本轮未提交增量。debug CLI 为该工作树的 `target/debug/isarch`，不是 release 构建。
- TOML 可放基础配置或 `--execution-limits-config` 读取的既有 `[execution_limits]` 表；未修改任何基础配置。CLI 出现时整体覆盖 TOML 集合。选择显式构造子集合，是为了保持 Isla 与具体模型无关，并允许明确排除其它异常。

```toml
[execution_limits]
filter_model_exceptions = ["Error_internal_error", "Error_reserved_behavior"]
```

对应 CLI：

```sh
--filter-model-exception Error_internal_error \
--filter-model-exception Error_reserved_behavior
```

默认集合为空；`Error_not_implemented` 只在显式列入时过滤。没有新增环境变量。用法与边界见 [CLI 说明](../../specs/isarch-cli.md)。

## 实现与计数口径

1. 仅检查 `Ok(Run::Finished)` 的 `frame.get_exception()`，匹配解码后的完整构造子名；不检查模型名、函数名、源码位置或消息关键词。Sail 模型、isla-lib 区域合并与求解逻辑均未修改。
2. 现场路径在求见证、枚举、保存 `ResidentPath`、样本检查及正常终态记账之前排除。`ExecError::*`、超时、未知 Poison、panic 保持原有失败处理；`AssertionFailure` 继续单独计数。
3. 缓存先完成原有 DTO 验证与双编码交叉核对，再按 `Terminal::SailException` 和异常值应用同一匹配函数。保留路径、facts 和当前签名同步筛选；原始 manifest 保留来源记录。旧 schema=3 不带新字段时仍可读取；没有增加哈希有效性门槛。
4. `filtered-model-exception-paths` 是过滤总数；`filtered-model-exception-sites` 是“构造子＋完整载荷消息”到次数的映射。`[MODEL_EXCEPTION_FILTER]` 输出同一统计；批次合并与缓存保存／重载保留计数。计数表示到达收集器的终态次数，过滤之前不额外证明 SAT，也不展开合并守卫类。因此 `finished` 只针对过滤后的终态域。

## 验证证据

先补最小 IR／配置失败测试，再实现过滤。最小 IR 同时含正常、internal、reserved、not-implemented 与 AssertionFailure 路径。

| 场景 | 结果 |
| --- | --- |
| 默认空集合 | 正常 1、异常 3、断言过滤 1、模型异常过滤 0 |
| 集合为 internal＋reserved | 正常 1、异常 1、断言过滤 1、模型异常过滤 2；`fixture.sail:42`／`:57` 各计 1 |
| 仅显式过滤 not-implemented | 模型异常过滤 1，其它两类异常保留 |
| 旧 schema=3 双编码缓存 | 两个同站点 internal 异常聚合为 2；正常终态即使返回值构造子同名仍保留；路径签名／facts 保持对应 |
| 已过滤缓存再次保存／读取 | 保留计数，不重复累加已经剪掉的路径 |

本工作树内执行的关键命令（测试使用 `output/model-exception-filter/z3-runner.sh`，通过系统 loader 加载仓库既有 official Z3 d6c9b4fbb／5.4）：

```sh
CARGO_TARGET_DIR=target cargo test -p isla-lib --lib model_exception_filter_config
CARGO_TARGET_DIR=target cargo test -p isla --lib isarch::exec::tests
CARGO_TARGET_DIR=target cargo test -p isla --lib isarch::path_cache::tests
CARGO_TARGET_DIR=target cargo test -p isla --bin isarch --no-run
CARGO_TARGET_DIR=target cargo build -p isla --bin isarch
cargo fmt
cargo fmt --check
git diff --check
```

测试运行时设置 `CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER=output/model-exception-filter/z3-runner.sh`；直接执行测试二进制也使用该 runner。相关日志都在该工作树 `output/model-exception-filter/`：

- 配置 1 项；exec 首轮 76 项通过、7 项因缺 IR 失败，链接已有 `agents/fuzz_strategy_20261112/exp/cache/inputs/rv64d.ir` 后仅补跑这 7 项，全部通过。未修改 IR／模型／配置。对应 `regression-exec.log`、`regression-real-ir.log`。
- samples 8 项＋缓存导出／检查 1 项，path_cache 7 项，通用匹配 1 项，summary 2 项，CLI 27 项通过。对应 `regression-samples.log`、`regression-cache-export-check.log`、`regression-path_cache-fixed.log`、`regression-model_exception.log`、`regression-solve_summary.log`、`regression-cli.log`。
- debug CLI 构建、重复两次 CLI 参数的 `--help` 解析、fmt 和 diff 检查通过。[机器汇总](../../output/model-exception-filter/final-check.json)；[本轮增量审查](review.md)。
- 初次运行误用系统 Z3 4.13.3，切换既有 Z3 后取得真正失败测试证据；新缓存测试缺 SMT 初始化也已修复并补跑。原失败日志保留，未把环境错误或历史失败改写为 PASS。

## 真实 PMP=2 缓存读回

使用指定 `agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/raw/pmp-small-count-20261117/pmpcount-20261117-n2-store-baseline-30s-r1/cache/STORE/`，原有正常 31／SailException 4／41 条执行超时。

新 debug CLI 冻结到本工作树输出目录，经共享 daemon 的 `append_queue` 提交到 `nodes:["public-4090server"]`，T32，程序 `--timeout 30s`／包装墙钟上限 35s（TERM 后 5s 强制收尾）／scheduler 外限 1m。只读回缓存并双编码交叉核对，未重新探索或枚举样本。

实际 14.6835s，退出 0；summary 的 `model-exception-paths=0`、`filtered-model-exception-paths=4`，唯一分项 `Error_internal_error: "sys/vmem.sail:214: invalid translation mode in satp"` 计 4。`errors=execution-timeouts=41` 和 `status=partial` 保留，未被开关隐藏。见 [真实缓存审计](../../output/model-exception-filter/probe-audit.json)、[scheduler 结果](../../output/model-exception-filter/probe-scheduler-result.json)、[实际 summary](../../output/model-exception-filter/pmp2-cli-on-30s-r1/output/rv64_zSTORE.json)。初次检索曾误判缓存缺失，直接读取 `manifest.json` 后已纠正，未据此跳过补验。

## 未验证项与操作边界

- 未运行完整 clause、`make solve`／MRET smoke、性能对照、release 构建或真实 DUT；真实缓存读回未验证其余 31 个正常终态的样本 judge／完整 DAG 导出，定向测试不代表这些项目通过。
- fuzz 仍要求至少一个保留终态，外部 corpus 仍须完整认证。若过滤后无路径，或旧 corpus entry 被排除，原有显式拒绝／认证失败保留；本轮没有自动迁移外部 corpus，也没有回退到被过滤的终态。读缓存自动生成的初始 corpus 只取保留路径。
- scheduler 提交 1 项，`execution_confirmed=true`、`retrieval=complete`、`remaining_group_cleanup=false`，scope OOM=false；已显式取回现有 attempt 的输出。构建、测试与该任务均已结束，无遗留计算任务。只修改指定工作树，并向本共享报告追加本章节；没有修改其他工作树、基础配置、Sail 或执行 Git 写操作。
