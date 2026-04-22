# CLAUDE.md

所有的回答都使用中文

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## 索引
- `agents/`: 记录目录下仓库中与agent写作的相关文档

## Rules
- `agents/overview.md`中查看仓库代码的概览，和代码有关的活动看这个目录
- `agents/<本次规划的主题和目标>/`: 记录目录下当前主题的仓库中代码相关的工作文件，如plan.md、status.md
  - `agents/<本次规划的主题和目标>/plan.md`: 存放规划的plan文件，在plan后写入文件，等待用户修改plan并确认
  - `agents/<本次规划的主题和目标>/status.md`: 当前工作的状态，包含不限于：当前修改的热点文件、关注的部分、进展情况等
- `agents/findings.md`: 记录目录下仓库中代码相关的逻辑，所有的对代码的发现、对代码逻辑的理解都必须写到本文件中，在涉及代码工作的时候必须先加载本文件再做代码分析