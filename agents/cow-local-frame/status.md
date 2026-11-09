# 执行帧 CoW 合入结果（2026-11-09）

实现完成，限定验证通过。此候选基于 `849900a6247bed81dc79a4c26af648ebea2f5b5f`，分支 `feat/cow-local-frame`。原仓库 Git 元数据只读，实际主线引用尚未更新；不能把候选完成写成主线已合入。

## 实现与兼容性

LocalFrame 的局部状态、内存、调用栈、回溯、函数假设、PC 计数、interrupt、执行限制和可选 trace 容器使用 Arc。纯读取容器冻结／恢复只克隆引用，写入口用 `Arc::make_mut` 分离。已适配当前区域路径合并、重试操作数和合并记录代码，未用旧 executor 覆盖新功能。

CustomRegion／MemoryCallbacks 新增 `is_pure_reader()`。为保护未适配的第三方扩展，默认 false；只有已核实的 SeqMemory 与 ImmutablePageTables 显式返回 true。默认 true 无法自动识别旧扩展中的 Atomic／Mutex，因此不能满足兼容性目标。共享观察可以改变传入的路径私有 solver，不能改变影响执行结果的内部状态。Clone 不得有执行副作用。

`Memory::fork_for_frame` 统一供 freeze、unfreeze、LocalFrame::clone 和 new_call 使用。有任一未知／有状态回调就克隆整个 Memory；纯读取才共享。Constrained 任意闭包缺少纯读取声明，保守地维持原帧复制行为。直接 LocalFrame Clone 保留原 `B: Clone` 的泛型边界。

第三方 Clone／clone_dyn 必须独立复制路径私有状态。若 Clone 仍共享 Arc<Atomic/Mutex>，或错误声明纯读取，普通 trait 无法自动检测；不能承诺不受契约约束的扩展“100% 健壮”。这也是旧深拷贝实现本来就依赖的边界。

## 测试与审查

TDD：移植共享测试后，原容器类型产生 24 个类型错误；移植 CoW 后，有状态读测试实际失败：子路径预期计数 1，实际 2。接入隔离策略后通过。最初一次测试缺少 SMT 初始化，修正测试后才得到上述语义红例，未把初始化失败当作隔离证据。

| 命令（统一带 `--offline -j 8`） | 结果 | 测试耗时 |
| --- | --- | ---: |
| `cargo test -p isla-lib --lib executor::frame` | 6 通过，0 失败 | 0.11s |
| `cargo test -p isla-lib --lib --features tracetool executor::` | 498 通过，0 失败，5 项既有忽略；其中执行帧 11 项 | 10.38s |
| `cargo test -p isla --lib isarch::memory_model::tests` | 34 通过，0 失败；含新增实际 SeqMemory 帧共享／写后隔离测试 | 0.13s |
| `cargo check -p isla-axiomatic` | 通过；保留既有编译警告 | 24.40s（含编译） |
| `cargo fmt --all -- --check`、`git diff --check` | 通过 | — |

在候选根目录运行，设置 `CARGO_TARGET_DIR` 为独立临时构建目录；链接环境为：

```sh
export RUSTFLAGS="-L native=$HOME/.local/opt/z3-official-1fd1d3613/lib -C link-arg=-Wl,-rpath,$HOME/.local/opt/z3-official-1fd1d3613/lib"
```

自查仅覆盖本次增量：检查共享状态的所有可变入口、真实调用栈恢复、分叉预算推进、区域事务和合并、符号宽度重试、trace 输出值类型，以及内存的四个复制入口。没有发现本次范围内的未关闭阻塞项。旧候选的独立审查仅作历史依据；本轮未新增独立 agent 评审。

## 保留的局限

这是容器级 CoW，首次可变访问仍可能复制整个容器。表达式求值和执行循环清理缓存本来就需要可变访问，因此 LocalState 可能在恢复后很快分离。纯内存的冻结仍需扫描区域判定共享资格；有状态内存沿用深拷贝。

SMT 统计、区域历史等其他字段仍有值复制，路径计时仍使用既有锁，不能把整个 freeze/unfreeze 称为严格 O(1) 或完全无锁。没有新的端到端性能测量、make solve、全量库回归或硬件验收，不继承旧 MRET 或旧版本的 PASS。本次未生成／修改 IR。
