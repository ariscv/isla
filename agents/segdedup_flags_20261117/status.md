# 分段去重线开关迁移状态（2026-11-18收尾）

16项功能／诊断已改为TOML＋CLI，默认不变，无环境兼容；4项测试通信保留。工作目录已整合isarch@dbfc6e70，HEAD仍a286b00c。未提交、未Git merge、未push。

区域111通过5忽略／去重义务14／查询32／配置3／CLI2／release／fmt通过；isarch exec76通过7项缺IR失败（原75／7）、samples8、path_cache7（原6）。冻结默认样本逐字节相同；主JSON仅继承过滤计数与程序名provenance差异。

唯一scheduler本机T32、64GiB、逐路径30秒／墙钟310秒：探索未清空，judge124、输出0行；sample0拒绝／sample1接纳及历史后态一致未复验。315秒左右全部退出确认，未观察OOM，无本路在途。

待办：PMP=2语义验收缺口、Claude执行正式Git整合；本轮没有整体合入PASS。

[计划](plan.md) · [清点](inventory.md) · [验证数据](verification.json) · [审阅](review.md) · [Git整合后可用迁移补丁](migration.patch)。完整原始命令、日志、冻结程序在工作树output/segdedup-flags/，不纳入归档。
