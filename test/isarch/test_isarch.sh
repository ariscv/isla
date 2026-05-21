#!/bin/bash
# isarch 测试入口
# 递归查找 test/isarch/ 下所有 test*.sh 并依次运行，默认传入 all 参数
#
# 用法: ./test_isarch.sh [参数...]
#   不带参数时对所有子测试脚本传入 all

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ARGS=("${@:-all}")

PASS=0
FAIL=0
SKIP=0

echo "=== isarch 测试 ==="
echo ""

found=0
for f in $(find "$SCRIPT_DIR" -name 'test*.sh' -not -path "$SCRIPT_DIR/test_isarch.sh" | sort); do
    found=1
    echo "--- $(basename "$f") ---"
    if bash "$f" "${ARGS[@]}"; then
        PASS=$((PASS + 1))
    else
        FAIL=$((FAIL + 1))
    fi
    echo ""
done

if [ "$found" -eq 0 ]; then
    echo "未找到任何 test*.sh 测试脚本"
    exit 1
fi

echo "=== 汇总 ==="
echo "  通过: $PASS  失败: $FAIL"

if [ "$FAIL" -gt 0 ]; then exit 1; fi
