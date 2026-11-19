# 通用函数线性化三策略系统

目标函数和策略由 ISA 配置中的 TOML 声明。函数名使用原始 Sail 名称，加载时编码一次。重复目标、未知字段、未知函数、非法策略和无效阈值均会导致加载失败。

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

- `none` 保留原 IR 和原生路径分叉。
- `full` 在通过安全资格检查后改写。资格不通过会使加载失败。
- `bounded` 在同时满足安全资格和成本阈值时改写。任一检查失败时保留原 IR 并输出原因。阈值包含边界值，允许为零。

安全资格要求入参、返回值和全部局部变量为 `Bool` 或固定位宽的 `Bits`，控制流无环，变量读写封闭。全局寄存器访问、内存访问、活动断言、复合位置写入、未解析调用和未获准的原语均被拒绝。资格检查在副本中复用标准外部调用解析，把已知原语解析为 `Primop` 指令，再逐条核对纯标量原语白名单。

成本根据改写前的 CFG 计算。每条条件跳转计一个分支。指令数包含声明、计算和显式终结指令，略过 CFG 添加的块间继续边。

TOML 配置选中的函数使用 `partial_linearize` 改写。TOML 目标先做安全资格检查，再处理 `--fork-assertions`。显式的 `-P/--partial-linearize` 或 `-L/--linearize` 覆盖同名 TOML 目标，继续使用各自已有的改写方式。

`verify` 默认为 `true`。设置为 `false` 会关闭 TOML 目标的自动等价验证，`--test-linearize` 可强制验证。验证须至少有一条可满足且正常完成的路径。正常结果必须为布尔真，或符号布尔结果的否定经 SMT 证明不可满足。全死路径、退出、挂起、非预期结果、反例及 SMT 错误或未知结果都不能通过验证。等价验证失败会立即结束加载。

在 Isla 根目录运行以下命令验证配置入口。

```sh
cargo test -p isla-lib linearize_policy
cargo build --bin isla-preprocess
python3 test/linearize/test_pipeline.py
```
