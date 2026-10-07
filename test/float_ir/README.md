# 浮点 IR 兼容性与状态回归

`helpers.tsv` 保存独立 Berkeley SoftFloat 预期值，共327例、67个迁移helper，包括三格式NaN/正负零、五种舍入、整数与格式转换、ROD和BF16。预期生成工具与oracle哈希见根工作区 `agents/float_only_review/evidence/generate_extra.py`、`extra-oracle.json`；不从受测模型计算预期。

从Isla仓库根目录运行：

```sh
python3 test/float_ir/run.py --output /tmp/float-ir-regression
python3 test/float_ir/run.py --mode helpers --output /tmp/float-ir-helpers
python3 test/float_ir/run.py --mode state --output /tmp/float-ir-state
```

runner复用`test/softfloat_legacy`的普通调用包装器与数值检查，每个实际声明接口都要求普通函数体、单条SAT完成路径，以及完整结果/五flags差异UNSAT。默认及三个RV64产物各327例，RV32按实际63个接口筛选为307例；不因RV64清单给RV32添加原来没有的接口。

状态探针直接运行真实IR的getter、setter和FADD.S，覆盖快速/普通路径、FS Initial/Clean/Dirty、同值/异值写，核对目标值、其余31个FPR哨兵、完整fcsr/mstatus，读取IR实际xlen决定SD31或SD63。getter必须无写回副作用。

`guard`是隔离断言域测试：F能力在这些生成IR中已经折叠为true，只在测试副本将`hartSupports(Ext_F)`的静态常量臂改为false，检查四个快速/普通getter/setter均AssertionFailure。它不伪称运行态TOML关闭了静态F能力，也不代表完整无F架构的指令验收。

输出目录保存命令、退出码、fixture和原始日志；任一失败使脚本非零退出。RV32通过的是helper和直接FADD执行，不代表公共RV32 solve-state入口已经支持。

IR修复采用冻结生成组件装配：`scripts/migrate_float_ir.py`补齐缺体接口，检查同名类型/extern/复用函数并重映射`files`与SourceLoc；状态模式仅允许替换`get_F_bits/set_F_bits`，调用目标原有架构专属Dirty函数，保留其余定义。输入已经完成相同装配时显式拒绝重复。具体提供方来源、生成配置及哈希在根工作区修复记录，不把组件装配称为全模型重生。

`ir/rv64d_v512_e64.ir`历史文件名对应的实际VLEN仍为256；本修复保留原宽度与初始化。其他旧IR的BF16 execute历史语义未在此次兼容性修复中迁移。
