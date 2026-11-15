# 普通非对齐访问定向回归

此夹具直接调用 Rust isarch 的 `solve_state_main`，共用生产求解、samples 和 judge。
它给内存装入具体 Sv39 页表，以便稳定检查 PBMT；不修改生产命令行或全符号前态配置。

先准备带有 `test_misaligned_access_policy` 的严格 IR 和定向配置，然后编译：

```sh
cargo build -p isla --release --example misaligned-access
```

在数据盘的新目录里运行，IR 和配置使用实际路径：

```sh
misaligned-access MODEL.ir CONFIG.toml nc LOAD 8 export
misaligned-access MODEL.ir CONFIG.toml nc LOAD 8 judge
```

实际程序为构建目录下的 `release/examples/misaligned-access`。
场景支持 `dram`、`device`、`nc`、`io`、`pma-page`、`nc-hit`、`io-hit`。
访问选择 `LOAD`／`STORE`，宽度选择 2／4／8 字节，地址均为区域起点加 1。
`pma-page` 是分页且 PBMT=00 的成功对照；`-hit` 使用预置 TLB，其余分页场景走页表遍历。

`export` 写 `samples.jsonl`，`judge` 写 `check.json` 和 `judged.jsonl`。
judge 必须逐样本恰好接纳一次、后态一致，且生成结果还须与场景预期核对。
最后一个参数为 `policy` 时直接执行 Sail 区域策略单测，其余场景参数不参与该项检查。

定向配置须启用非对齐并配置香山 PMA。夹具关闭 PMP 以分开检查 PMA／PBMT，
不代表已覆盖 PMP、多错误优先级、向量或硬件差分测试。
