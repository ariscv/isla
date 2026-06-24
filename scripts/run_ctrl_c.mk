# run_ctrl_c.mk —— Ctrl-C 清理机制（可选插件，被 run.mk 顶部 -include 引入）
#
# 这是一个【可选插件】，两种清理方式：
#   1) 自动：给每个 solve-% recipe 注入 trap（通过 override SOLVE_TRAP 变量），Ctrl-C 时
#      自动 pkill 掉后台 isarch；
#   2) 手动：提供 `make kill-isarch` 目标，一键强杀所有 ./target/release/isarch 进程。
# 本文件缺失时，run.mk 的 SOLVE_TRAP 为空（recipe 正常跑，只是 Ctrl-C 不自动清后台），
# 可手动 `pkill -KILL -f isarch` 兜底。插件只 override 变量 + 加新目标，不重定义 solve，
# 故【零 warning】。
#
# 为什么需要 Ctrl-C 清理：
#   make -j 给每个 job 的 timeout/isarch 放进【独立进程组】（与 make 的前台进程组不同），
#   用户 Ctrl-C 时 SIGINT 只发给 make 的前台进程组，打不到独立 job 组里的 isarch，于是
#   ./target/release/isarch 被 init 收养、继续跑到 60s 超时——这正是“Ctrl-C 后后台还一堆
#   isarch”的根因。这里用按命令名的 pkill 绕过进程组，Ctrl-C 时统一清掉。
#     * make -j 下 job 的 shell 收到 INT（make 转发）→ job shell 的 trap 触发 → pkill isarch。
#     * 用 SIGKILL(9)：isarch 可能正在做 SMT 求解、不响应 TERM，直接 KILL 最稳。
#     * `pkill -f target/release/isarch` 精确匹配，不误伤其他进程。
#
# 注意：solve-% 的 job 用 bash 才能让 trap 在 INT 下可靠触发（dash 可能来不及）。下面把
# solve-% 也切到 bash（仅 pattern rule，不影响其他目标）。
SHELL_BASH := /bin/bash
solve-%: SHELL := $(SHELL_BASH)

# 注入到每个 solve-% recipe 开头：注册 trap，收到 INT/TERM 时 pkill 掉所有 isarch。
# 末尾保留 "; " 以便和 run.mk 里紧跟其后的 n=$(flock ...) 拼成合法的连续命令。
override SOLVE_TRAP := trap 'pkill -KILL -f target/release/isarch 2>/dev/null' INT TERM; \

# 手动兜底：一键强杀所有 isarch 进程。用法 make kill-isarch
.PHONY: kill-isarch
kill-isarch:
	@pkill -KILL -f target/release/isarch 2>/dev/null && echo "已清理所有 isarch 进程" || echo "没有运行中的 isarch 进程"
