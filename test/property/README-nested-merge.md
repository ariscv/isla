# Sail 内层合并失败验收

每个性质比较 [共用 Sail 模型](include/nested_merge.sail)的返回值与独立位向量规格。形状检查使用完成路径的守卫。S1 的 c2 和 c3 写入不同的等宽位向量，可用 ITE 合并成 c。b1 写入的具体字符串与 c 不同。期望外层 a 的三个取值分别在 b1 和 c 两组内合并。

| 场景 | 关闭合并 | 递归与平铺预期 | 路径形状 |
| --- | ---: | ---: | --- |
| S1 | 9 | 2 | 一条覆盖任意合法 a 与 z=1，另一条覆盖任意合法 a 与 z∈{2,3} |
| S2 | 9 | 1 | 三个 z 取值的字符串均为 b，整域可合并 |
| S3 | 9 | 3 | 三个字符串两两不同，每个 z 一条，a 取遍 |
| S4 | 12 | 2 | 两个独立二路外层，按 z=1 与 z∈{2,3} 分组 |
| S5 | 9 | 2 | 三路调用方，内层分叉位于被调函数，形状同 S1 |
| S6 边界 | 4 | 2 | 内层 z 可合并，中层自身的汇合点按 m 保留两条 |
| S6 | 8 | 2 | 外层 w 的两个取值进入每个 m 分组 |
| S1 控制 | 9 | 1 | 仅将 b1 的字符串改为 c，三个 z 取值可全部合并 |
| 错误规格 | — | — | 故意把 z=1 的标签写错，框架期望找到反例 |

`ruby test/run_tests.rb --property-filter '^nested_merge_'` 按 B64 和 B129 分别运行每个文件的递归、平铺及关闭合并配置。可用 `--property-bin-dir <目录>` 指定预先编译的两个 property 程序。需要 Sail、Isla Sail 插件和 PATH 中的 Z3。

`<basename>.<variant>.opts` 为每次执行提供独立 CLI 参数，`<basename>` 包含 `.sat` 或 `.unsat` 后缀。参数可用 `-C <配置>` 指定继承 `configs/plain.toml` 的 TOML 文件。旧有用例仍可使用 `<basename>.opts`。

`--expect-paths N` 核对可满足的最终完成路径数，计数失败退出 2 并列出路径。`--print-paths` 打印路径摘要。`--dump-paths <文件>` 导出 JSON，包含求解器声明与守卫断言 `guard_smtlib`、`return_value`、`merge_records` 和整寄存器写入 `register_writes`。形状文件开头声明观测寄存器和有限位宽，接着每行一个期望守卫。框架调用 Z3 核对每条路径可满足的输入集合，并比较完整集合列表。配置专用的 `.shape` 优先于同名公共文件，也可用 `ruby test/property/include/check_paths.rb <JSON> <shape>` 单独核对。
