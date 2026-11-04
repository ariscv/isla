# Review 37 修复计划

目标：修复审查 F1～F4，保留区域优先级、Constrained 整区域读取合同、原始事件地址及设备副作用。基线为 `c6de9354945c0accfdc7da624618a5fd568901b2`，开始时目标工作树干净；父仓库已有修改不动。

范围：`src/isarch/memory_model.rs`、`isla-lib/src/memory.rs`、`isla-lib/src/primop.rs`、`isla-lib/src/primop/float.rs` 与相关回归测试。复用初始数组、Select／Store、区域遍历及地址拆分接口，不加入静默替代结果。

步骤：应用完整复现补丁并运行失败基线；统一 Constrained 初始约束与数组读写；让预检查按实际区域优先级判断；修复整数绝对值和六个浮点转换入口；补充遮蔽设备与生成器边界测试；执行 Review 37、Review 36、工作区全量及格式检查，同步代码发现和验证记录。

验证：Review 37 必须 8/8；Review 36 与工作区全量不得失败。局部规则要求额外执行 MRET smoke，保留既有 output。记录实际命令、配置、版本及日志；未执行项目不记 PASS。未决问题：新数组读取必须兼容既有整区域读取合同，不能通过放松旧测试掩盖回归。
