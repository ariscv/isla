# 通用函数线性化三策略系统

目标函数和策略由 ISA 配置中的 TOML 声明。函数名使用原始 Sail 名称，加载时进行一次 zencode；重复目标、未知字段、未知函数、非法策略和无效阈值均会导致加载失败。

```toml
[linearize]
verify = true

[[linearize.targets]]
function = "pure_func_name"
strategy = "full"

[[linearize.targets]]
function = "bounded_func"
strategy = "bounded"
max_branches = 4
max_instructions = 50

[[linearize.targets]]
function = "native_func"
strategy = "none"
```

- `none`：保留原 IR，使用原生路径分叉。
- `full`：通过安全资格门后改写，不检查成本；资格不通过则在加载期报错退出。
- `bounded`：安全资格门和成本门均通过才改写；否则输出原因，并在改写前决定保留原 IR。阈值包含边界值，允许为零。

安全资格门要求入参、返回值和全部局部变量类型仅为 `Bool` 或固定位宽的 `Bits`，控制流无环，变量读写封闭。全局寄存器访问、内存访问、活动断言、复合表达式、未解析调用和未获准的 primop 均被拒绝。调度器在副本中复用标准外部调用解析接口，将已知 primop 转为 `Primop` 指令，再检查经过审核的纯标量 primop 白名单；普通函数调用不做跨函数纯净度推断。

成本根据改写前的 CFG 统计：每条条件跳转计一个分支；指令数包含声明、计算和显式终结指令，不包含人为添加的块间继续边。

`-P/--partial-linearize` 和 `-L/--linearize` 均选择 `full`，覆盖同名 TOML 目标，统一调用 `partial_linearize`。不会删除断言；`--fork-assertions` 在资格检查和改写完成后处理其余断言。

`verify` 默认为 `true`；显式设置为 `false` 可以关闭自动等价验证，`--test-linearize` 始终强制验证。验证须至少有一条可满足且正常完成的路径。正常结果必须为布尔真，或符号布尔结果的否定经 SMT 证明不可满足。全死路径、退出、挂起、非预期结果、反例及 SMT 错误或未知结果都不能通过验证。改写和证明过程中不捕获内部错误，也不会因失败而恢复旧 IR。

验证命令：

```sh
cargo test -p isla-lib
cargo fmt --check
cargo build --bin isla-preprocess
python3 test/linearize/test_pipeline.py
make solve-MRET -j4 THREADS=8
make solve -j4 THREADS=8
```
