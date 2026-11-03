# 浮点 IR 兼容性与状态回归

`helpers.tsv` 保存独立 Berkeley SoftFloat 预期值，共327例、67个迁移helper，包括三格式NaN/正负零、五种舍入、整数与格式转换、ROD和BF16。预期生成工具与oracle哈希见根工作区 `agents/float_only_review/evidence/generate_extra.py`、`extra-oracle.json`；不从受测模型计算预期。

从Isla仓库根目录运行：

```sh
python3 test/float_ir/run.py --output /tmp/float-ir-regression
python3 test/float_ir/run.py --mode helpers --output /tmp/float-ir-helpers
python3 test/float_ir/run.py --mode state --output /tmp/float-ir-state
```

runner复用`test/softfloat_legacy`的普通调用包装器与数值检查，每个实际声明接口都要求普通函数体、单条SAT完成路径，以及完整结果/五flags差异UNSAT。默认及三个RV64产物各327例，RV32按实际63个接口筛选为307例；不因RV64清单给RV32添加原来没有的接口。

RV32使用`rv32_fd.toml`，其CLINT地址/大小按该IR的34位物理地址类型给定；运行器仍从实际IR读取xlen核对SD位。状态探针直接运行真实IR的getter、setter和FADD.S，覆盖快速/普通路径、FS Initial/Clean/Dirty、同值/异值写，核对目标值、其余31个FPR哨兵、完整fcsr/mstatus，读取IR实际xlen决定SD31或SD63。getter必须无写回副作用。

`guard`是隔离断言域测试：F能力在这些生成IR中已经折叠为true，只在测试副本将`hartSupports(Ext_F)`的静态常量臂改为false，检查四个快速/普通getter/setter均AssertionFailure。它不伪称运行态TOML关闭了静态F能力，也不代表完整无F架构的指令验收。

输出目录保存命令、退出码、fixture和原始日志；任一失败使脚本非零退出。RV32通过的是helper和直接FADD执行，不代表公共RV32 solve-state入口已经支持。

历史兼容性修复曾采用冻结生成组件装配：`scripts/migrate_float_ir.py`补齐缺体接口，检查同名类型/extern/复用函数并重映射`files`与SourceLoc；状态模式仅允许替换`get_F_bits/set_F_bits`，调用目标原有架构专属Dirty函数，保留其余定义。输入已经完成相同装配时显式拒绝重复。具体提供方来源、生成配置及哈希在根工作区修复记录，不把组件装配称为全模型重生。

上述装配说明适用于旧兼容性修复版本。当前全部IR由固定模型完整重生，生成入口为`scripts/regenerate_ir.py`，配置和来源见`ir/provenance/manifest.json`。当前V128/V256/V512分别使用对应配置，不再沿用旧V512文件实际VLEN=256的历史情况。

`check_nan_unbox_branches.py`检查全部IR保留等宽判断及boxing有效/无效的显式分支，已接入`run.py`。另可传入实际FLEQ.S的JSON核对两侧见证：

```sh
python3 test/float_ir/check_nan_unbox_branches.py --fleq-json output/rv64_zFLEQ_S.json
```

恢复该判断不能代表其余浮点数据条件已全部覆盖；本回归不以路径数量或执行耗时下降作为通过条件。

`check_float_closure_branches.py` 检查收敛模型的浮点控制与值来源，并已接入 `run.py`。五份IR保留 `accrue_fflags` changed/Ext_F 写回控制、f16→i16 的旧溢出Jump、18个异常helper的 finite/valid gate、ROD模式与finite gate，以及跨格式/BF16转换finite gate。其余五个窄转换用同一overflow值选择NV/原flags及端点/原低位；18个异常helper在两出口保留同一NV/DZ表达式，只在有限真臂计算舍入事实，并对H/S/D代表位模式逐项核NV/DZ与gate；12个整数包装用invalid/NaN/符号值选择饱和结果，仍核候选转换值和flags来源。rounded、exact_threshold、fp_to_int_core、round与ROD jam的纯数据出口核字段来源；`ieee_mask_exact_exceptions`已删除。`check_special_semantic_branches.py`继续核源分类及20个活动lane gate。

可对单份尚未安装的生成 IR 先核 CFG：

```sh
python3 test/float_ir/check_float_closure_branches.py --ir <生成IR路径>
python3 test/float_ir/check_special_semantic_branches.py --ir <生成IR路径>
```

这些检查验证静态控制关系，不代替具体值/flags/后态的 oracle 或整 Clause 完整域求解预算。源码、IR、配置或生成器变化后，应在新五 IR 上重跑；旧版本的绿测不迁移。
