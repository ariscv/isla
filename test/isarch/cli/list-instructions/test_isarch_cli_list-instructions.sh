#!/bin/bash
# list-instructions CLI 测试编排脚本
#
# 被 test_isarch.sh 自动发现并执行。
# 封装 test_isarch_cli.sh 的 list-instructions 相关测试项。
#
# 用法: ./test_isarch_cli_list-instructions.sh [quick | all | 测试名...]
#   quick  - 仅运行快速测试（跳过符号执行等耗时项）
#   all    - 运行全部测试（默认）
#   测试名 - 按名称子串过滤

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLI_TEST="$SCRIPT_DIR/../test_isarch_cli.sh"

if [ ! -f "$CLI_TEST" ]; then
    echo "SKIP list-instructions — test_isarch_cli.sh 不存在"
    exit 0
fi

MODE="${1:-all}"

# 从 test_isarch_cli.sh 中筛选 list-instructions 相关的测试
LIST_INST_TESTS=(
    t_list_instructions
    t_list_instructions_clause_count
    t_list_instructions_key_clauses
    t_list_instructions_assembly_names
    t_expected_files_fresh
)

if [ "$MODE" = "quick" ]; then
    # quick 模式跳过符号执行相关的耗时测试
    QUICK_ONLY=(
        t_list_instructions
        t_list_instructions_clause_count
        t_list_instructions_key_clauses
        t_expected_files_fresh
    )
    echo "=== list-instructions 测试 (quick) ==="
    bash "$CLI_TEST" "${QUICK_ONLY[@]}"
else
    echo "=== list-instructions 测试 ==="
    bash "$CLI_TEST" "${LIST_INST_TESTS[@]}"
fi
