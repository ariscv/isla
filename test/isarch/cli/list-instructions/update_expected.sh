#!/bin/bash
# 更新 isarch CLI 测试的预期结果文件
#
# 用法: ./update_expected.sh [sail_riscv_dir]
#   指定 sail_riscv_dir 时，先从源码重新生成 expected_data/，再生成 expected/*.txt
#   不指定时，仅从现有 expected_data/ 生成 expected/*.txt
#
# 环境变量:
#   SAIL_RISCV_DIR - sail-riscv 目录路径（优先级低于命令行参数）

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# 确定 sail-riscv 目录
SAIL_DIR=""
if [ $# -ge 1 ]; then
    SAIL_DIR="$1"
elif [ -n "${SAIL_RISCV_DIR:-}" ]; then
    SAIL_DIR="$SAIL_RISCV_DIR"
else
    # 向上逐级搜索含 sail-riscv 同级目录的祖先
    cur="$(cd "$SCRIPT_DIR/../.." && pwd)"
    while [ "$cur" != "/" ]; do
        if [ -d "$cur/../sail-riscv/model" ]; then
            SAIL_DIR="$(cd "$cur/../sail-riscv" && pwd)"
            break
        fi
        cur="$(cd "$cur/.." && pwd)"
    done
fi

# 如果指定了 sail-riscv 目录，先更新 expected_data/
if [ -n "$SAIL_DIR" ]; then
    if [ ! -d "$SAIL_DIR/model" ]; then
        echo "错误: $SAIL_DIR/model 不存在，请确认 sail-riscv 目录路径"
        exit 1
    fi

    echo "步骤 1: 从 sail-riscv 源码重新生成 expected_data/ Python 模块..."
    echo "  源目录: $SAIL_DIR"
    echo ""

    python3 "$SCRIPT_DIR/extract_sail_clauses.py" update-from-sail "$SAIL_DIR"
    echo ""
fi

echo "从 expected_data/ 生成 expected/*.txt 文件..."
echo ""

python3 "$SCRIPT_DIR/extract_sail_clauses.py" generate

echo ""
echo "预期结果文件已更新。"
echo "请运行测试验证: bash $(cd "$SCRIPT_DIR/../.." && pwd)/test_isarch_cli.sh"
