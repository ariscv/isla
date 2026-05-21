#!/bin/bash
# isarch CLI solve-state 子命令集成测试
#
# 测试关注点：路径爆炸是否导致超时
# 每个 clause 使用 timeout 30 秒，超时则视为路径爆炸失控
#
# 用法: ./test_isarch_cli_solve-state.sh [all | 测试名...]
#   all 或不带参数运行全部，指定名称子串过滤
#
# 环境变量:
#   ISARCH_BIN       - isarch 可执行文件（默认 target/release/isarch）
#   IR_FILE          - 架构 IR 文件（如 rv64d.ir）
#   CONFIG_FILE      - 配置文件（如 configs/riscv64_difftest.toml）
#   CLAUSE_TIMEOUT   - 单 clause 超时秒数（默认 30）

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"

ISARCH_BIN="${ISARCH_BIN:-${REPO_ROOT}/target/release/isarch}"
IR_FILE="${IR_FILE:-${REPO_ROOT}/rv64d.ir}"
CONFIG_FILE="${CONFIG_FILE:-${REPO_ROOT}/configs/riscv64_difftest.toml}"
CLAUSE_TIMEOUT="${CLAUSE_TIMEOUT:-30}"

# Phase 5 builtin summary gates（路径爆炸控制）
RUN_ACCESS_ENV="
ISLA_RISCV_ASSUME_PMP_OFF=1
ISLA_RISCV_BUILTIN_PMP_CHECK=1
ISLA_RISCV_BUILTIN_PMA_CHECK=1
ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK=1
ISLA_RISCV_ASSUME_CLINT_OFF=1
ISLA_RISCV_BUILTIN_WITHIN_MMIO=1
ISLA_RISCV_BUILTIN_PMP_RANGE_MATCH=1
ISLA_RISCV_BUILTIN_RANGE_SUBSET=1
ISLA_RISCV_BUILTIN_SPLIT_MISALIGNED=1
"

# ========== 基础设施 ==========

PASS=0
FAIL=0
SKIP=0
RESULTS=()
_CUR=""

pass() { RESULTS+=("PASS $_CUR"); PASS=$((PASS + 1)); }
fail() { RESULTS+=("FAIL $_CUR — $*"); FAIL=$((FAIL + 1)); }
skip() { RESULTS+=("SKIP $_CUR — $*"); SKIP=$((SKIP + 1)); }

need_bin()  { [ -f "$ISARCH_BIN" ] || { skip "binary not found: $ISARCH_BIN"; return 1; }; }
need_ir()   { [ -f "$IR_FILE" ]   || { skip "IR not found: $IR_FILE";       return 1; }; }
need_all()  { need_bin && need_ir; }

# 运行 solve-state 并捕获结果
# 用法: run_solve_state <clause_name> <env_overrides>
#   返回: 0=正常完成, 124=timeout超时, 其他=错误
#   在 OUTPUT_DIR 下生成 JSON 和日志
run_solve_state() {
    local clause="$1"
    local env_overrides="${2:-}"
    local output_dir="${REPO_ROOT}/output/solve-state/${clause}"
    mkdir -p "$output_dir"

    local rc=0
    eval "${env_overrides} ${RUN_ACCESS_ENV} \
        timeout ${CLAUSE_TIMEOUT} ${ISARCH_BIN} \
        -A ${IR_FILE} -C ${CONFIG_FILE} --verbose --probe-all --trace-all \
        solve-state --clause ${clause} \
        >${output_dir}/log 2>&1" || rc=$?

    echo "$rc"
}

# 从 JSON 输出提取 gen 数量
json_gen_count() {
    local json_file="$1"
    if [ ! -f "$json_file" ]; then
        echo "-1"
        return
    fi
    python3 -c "import json; d=json.load(open('$json_file')); print(len(d.get('gen',[])))" 2>/dev/null || echo "-1"
}

# ========== 参数校验 ==========

t_solve_state_no_filter() {
    need_all || return
    local rc; rc=$(run_solve_state "zNONE_XYZ" "")
    # 不存在的 clause 应正常退出（可能报错但不超时）
    if [ "$rc" -eq 124 ]; then
        fail "不存在的 clause 也超时了"
        return
    fi
    pass
}

t_solve_state_help() {
    need_all || return
    local out; out=$(${ISARCH_BIN} -A ${IR_FILE} -C ${CONFIG_FILE} 2>&1 || true)
    if echo "$out" | grep -qi "solve-state"; then
        pass
    else
        fail "用法信息不包含 solve-state"
    fi
}

# ========== LOAD 路径爆炸测试 ==========

# LOAD 无 gates：预期超时（路径爆炸）
t_load_no_gates_timeout() {
    need_all || return
    local env_overrides="
        ISLA_RISCV_ASSUME_PMP_OFF=0
        ISLA_RISCV_BUILTIN_PMP_CHECK=0
        ISLA_RISCV_BUILTIN_PMA_CHECK=0
        ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK=0
        ISLA_RISCV_ASSUME_CLINT_OFF=0
        ISLA_RISCV_BUILTIN_WITHIN_MMIO=0
        ISLA_RISCV_BUILTIN_PMP_RANGE_MATCH=0
        ISLA_RISCV_BUILTIN_RANGE_SUBSET=0
        ISLA_RISCV_BUILTIN_SPLIT_MISALIGNED=0
    "
    local rc; rc=$(run_solve_state "zLOAD" "$env_overrides")
    if [ "$rc" -eq 124 ]; then
        pass  # 预期：无 gates 时路径爆炸导致超时
    elif [ "$rc" -eq 0 ]; then
        local json="${REPO_ROOT}/output/solve-state/zLOAD/rv64_zLOAD.json"
        local count; count=$(json_gen_count "$json")
        if [ "$count" -gt 0 ]; then
            fail "无 gates 下 ${CLAUSE_TIMEOUT}s 内完成 $count 条路径，路径爆炸未复现"
        else
            pass  # 完成但 0 路径，也算路径爆炸失控
        fi
    else
        fail "退出码 $rc，既不是超时(124)也不是正常(0)"
    fi
}

# LOAD 有 Phase5 gates：预期在超时内完成且有路径输出
t_load_with_gates() {
    need_all || return
    local rc; rc=$(run_solve_state "zLOAD" "")
    local json="${REPO_ROOT}/output/solve-state/zLOAD/rv64_zLOAD.json"
    if [ "$rc" -eq 124 ]; then
        fail "Phase5 gates 下 zLOAD 仍超时"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "Phase5 gates 下 zLOAD 退出码 $rc"
        return
    fi
    local count; count=$(json_gen_count "$json")
    if [ "$count" -le 0 ]; then
        fail "Phase5 gates 下 zLOAD gen_count=$count（无路径输出）"
        return
    fi
    pass  # Phase5 gates 下在超时内完成且有路径
}

# ========== STORE 路径爆炸测试 ==========

# STORE 无 gates：预期超时
t_store_no_gates_timeout() {
    need_all || return
    local env_overrides="
        ISLA_RISCV_ASSUME_PMP_OFF=0
        ISLA_RISCV_BUILTIN_PMP_CHECK=0
        ISLA_RISCV_BUILTIN_PMA_CHECK=0
        ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK=0
        ISLA_RISCV_ASSUME_CLINT_OFF=0
        ISLA_RISCV_BUILTIN_WITHIN_MMIO=0
        ISLA_RISCV_BUILTIN_PMP_RANGE_MATCH=0
        ISLA_RISCV_BUILTIN_RANGE_SUBSET=0
        ISLA_RISCV_BUILTIN_SPLIT_MISALIGNED=0
    "
    local rc; rc=$(run_solve_state "zSTORE" "$env_overrides")
    if [ "$rc" -eq 124 ]; then
        pass
    elif [ "$rc" -eq 0 ]; then
        local json="${REPO_ROOT}/output/solve-state/zSTORE/rv64_zSTORE.json"
        local count; count=$(json_gen_count "$json")
        if [ "$count" -gt 0 ]; then
            fail "无 gates 下 ${CLAUSE_TIMEOUT}s 内完成 $count 条路径"
        else
            pass
        fi
    else
        fail "退出码 $rc"
    fi
}

# STORE 有 Phase5 gates：预期在超时内完成
t_store_with_gates() {
    need_all || return
    local rc; rc=$(run_solve_state "zSTORE" "")
    local json="${REPO_ROOT}/output/solve-state/zSTORE/rv64_zSTORE.json"
    if [ "$rc" -eq 124 ]; then
        fail "Phase5 gates 下 zSTORE 仍超时"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "Phase5 gates 下 zSTORE 退出码 $rc"
        return
    fi
    local count; count=$(json_gen_count "$json")
    if [ "$count" -le 0 ]; then
        fail "Phase5 gates 下 zSTORE gen_count=$count"
        return
    fi
    pass
}

# ========== 注册表 ==========

ALL_TESTS=(
    t_solve_state_no_filter
    t_solve_state_help
    t_load_no_gates_timeout
    t_load_with_gates
    t_store_no_gates_timeout
    t_store_with_gates
)

# ========== main ==========

echo "=== solve-state 集成测试 ==="
echo "  binary:  $ISARCH_BIN"
echo "  IR:      $IR_FILE"
echo "  config:  $CONFIG_FILE"
echo "  timeout: ${CLAUSE_TIMEOUT}s/clause"
echo ""

for t in "${ALL_TESTS[@]}"; do
    if [ $# -gt 0 ] && [ "$1" != "all" ]; then
        match=false
        for pattern in "$@"; do
            [[ "$t" == *"$pattern"* ]] && match=true && break
        done
        [ "$match" = false ] && continue
    fi

    _CUR="$t"
    echo "--- $t ---"
    $t
done

echo ""
echo "=== 结果 ==="
for r in "${RESULTS[@]}"; do echo "  $r"; done
echo ""
echo "  通过: $PASS  失败: $FAIL  跳过: $SKIP"

if [ "$FAIL" -gt 0 ]; then exit 1; fi