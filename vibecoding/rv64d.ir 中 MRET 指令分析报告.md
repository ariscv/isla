# rv64d.ir 中 MRET 指令分析报告
1. 指令定义
zMRET 类型定义（第 2835 行）：


zMRET: %unit
2. 指令编码信息
在 zencdec_forwards 函数中（第 91124 行附近），MRET 的编码为：

opcode: 0b1110011 (0x73)
funct3: 0b000
funct7: 0b00000
rd: 0b00000 (x0/zero)
rs1: 0b00000 (x0/zero)
完整 32 位编码：0b0000000_00000_000_00000_1110011 = 0x30200073

3. 汇编名称映射
在 zassembly_forwards 函数中（第 297417 行）：


jump zargz3 is zMRET goto 590
zz40 = "mret"
MRET 的汇编助记符为 "mret"。

4. 执行语义（zexecute 函数）
主要执行流程（第 252492 行开始）：


jump zmergez3var is zMRET goto 1358
权限检查：

当前特权级检查（第 252494 行）：


zz4539 = zneq_anythingzIEPrivilegez5zK(zcur_privilege, zMachine)
如果当前特权级不是 Machine 级别，则执行非法指令处理。

扩展权限检查（第 252498 行）：


zz4541 = zext_check_xret_priv(zMachine)
zz4540 = znot(zz4541)
检查 MRET 扩展权限是否允许。

异常处理分支：

权限不满足 → zIllegal_Instruction() （第 252511 行）
扩展检查失败 → zExt_XRET_Priv_Failure() （第 252509 行）
正常执行路径（第 252503-252507 行）：


zz4543 = zCTL_MRET(())
zz4542 = zexception_handler(zcur_privilege, zz4543, zPC)
zz4544 = zset_next_pc(zz4542)
zz40 = zRETIRE_SUCCESS
5. 控制流调用
调用 zCTL_MRET(()) 原语操作（第 252503 行），该原语：

从机器模式 CSR（mstatus, mepc, mtval 等）恢复上下文
更新特权级
返回新的 PC 值
6. 相关引用位置
行号	上下文	说明
2835	类型定义	zMRET: %unit
3340	类型定义	zCTL_MRET: %unit
91124	编码函数	指令编码生成
120620	编码函数	指令编码生成（备用路径）
151859	解码函数	zz41293 = zMRET(())
197382	解码函数	zz41293 = zMRET(())（备用路径）
252492	执行函数	jump zmergez3var is zMRET goto 1358
252503	执行函数	调用 zCTL_MRET(())
297417	汇编函数	返回 "mret" 字符串
308871	汇编匹配函数	汇编名称匹配检查
319954	汇编匹配函数	汇编名称匹配检查（备用路径）
7. 源码位置引用
所有 MRET 相关操作都引用源文件 "extensions/I/base_insts.sail"，行号范围 558-572。

总结：MRET 是 RISC-V 的机器模式异常返回指令，只能在 Machine 特权级执行，用于从异常处理返回，恢复之前保存的执行上下文（PC、特权级等）。