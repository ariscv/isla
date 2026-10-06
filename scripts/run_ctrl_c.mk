# 每条 solve recipe 已 exec 独立监督器，INT/TERM 只清理其 timeout 的专属进程组。
# 原 timeout argv、外限和 kill-after 保留；监督器记录实际 wait status 与收到的信号。
# 手动停止必须明确提供监督器 PID：make solve-kill SOLVE_PID=<pid>。
# 入口核对 PID 的 cwd、解释器和脚本命令，再用 pidfd 发 TERM；无法确认即拒绝。
# 不按名字扫描清理，不影响 make -j 兄弟任务或其它 stage 的同名 isarch。
.PHONY: kill-isarch solve-kill
kill-isarch solve-kill:
	@/usr/bin/python3 scripts/solve_process.py kill $(if $(SOLVE_PID),--pid $(SOLVE_PID),)
