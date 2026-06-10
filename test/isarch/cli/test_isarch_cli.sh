#!/bin/bash
# isarch CLI 集成测试
#
# 用法: ./cli_test.sh [all | 测试名...]
#   all 或不带参数运行全部，指定名称子串过滤
#
# 环境变量:
#   ISARCH_BIN  - isarch 可执行文件（默认 target/debug/isarch）
#   IR_FILE     - 架构 IR 文件（如 rv64d.ir）
#   CONFIG_FILE - 配置文件（如 configs/riscv64.toml）

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

EXPECTED_DIR="$SCRIPT_DIR/list-instructions/expected"
LIST_INST_DIR="$SCRIPT_DIR/list-instructions"

ISARCH_BIN="${ISARCH_BIN:-${REPO_ROOT}/target/debug/isarch}"
IR_FILE="${IR_FILE:-${REPO_ROOT}/../rv64d.ir}"
CONFIG_FILE="${CONFIG_FILE:-${REPO_ROOT}/configs/riscv64.toml}"

# ========== 基础设施 ==========

PASS=0
FAIL=0
SKIP=0
RESULTS=()
_CUR=""

pass() { RESULTS+=("PASS $_CUR"); PASS=$((PASS + 1)); }
fail() { RESULTS+=("FAIL $_CUR — $*"); FAIL=$((FAIL + 1)); }
skip() { RESULTS+=("SKIP $_CUR — $*"); SKIP=$((SKIP + 1)); }

# 检查退出码，不匹配则 fail 并返回 1
# 用法: check_exit [-t <timeout_sec>] <expected_exit> <command...>
check_exit() {
    local timeout_sec=0
    if [ "$1" = "-t" ]; then
        timeout_sec="$2"; shift 2
    fi
    local want=$1 rc=0; shift
    if [ "$timeout_sec" -gt 0 ]; then
        timeout "$timeout_sec" "$@" >/dev/null 2>&1 || rc=$?
    else
        "$@" >/dev/null 2>&1 || rc=$?
    fi
    if [ "$rc" -ne "$want" ]; then
        fail "退出码 期望=$want 实际=$rc"
        return 1
    fi
    return 0
}

# 检查 stderr/stdout 合并输出包含指定模式
check_output() {
    local pattern=$1; shift
    local out; out=$("$@" 2>&1 || true)
    if ! echo "$out" | grep -qi "$pattern"; then
        fail "输出不包含 '$pattern'"
        return 1
    fi
    return 0
}

# 在临时目录中运行 isarch，返回 tmpdir 路径（调用者负责清理）
# 用法: in_tmpdir <timeout_sec> <command...>
#   timeout_sec=0 表示不限时
in_tmpdir() {
    local timeout_sec="$1"; shift
    local tmpdir; tmpdir="$(mktemp -d)"
    mkdir -p "$tmpdir/profiles/riscv"
    if [ "$timeout_sec" -gt 0 ]; then
        ( cd "$tmpdir" && timeout "$timeout_sec" "$@" ) || true
    else
        ( cd "$tmpdir" && "$@" ) || true
    fi
    echo "$tmpdir"
}

# 前置检查
need_bin()  { [ -f "$ISARCH_BIN" ] || { skip "binary not found: $ISARCH_BIN"; return 1; }; }
need_ir()   { [ -f "$IR_FILE" ]   || { skip "IR not found: $IR_FILE";       return 1; }; }
need_all()  { need_bin && need_ir; }

isarch() { "$ISARCH_BIN" "$@"; }

# 从预期结果文件读取 clause 名称列表（跳过注释和空行）
expected_clause_names() {
    local f="$EXPECTED_DIR/clause_names.txt"
    if [ ! -f "$f" ]; then
        echo ""
        return
    fi
    grep -v '^#' "$f" | grep -v '^$' | sort
}

# 从 isarch list-instructions 输出提取 clause 名称
actual_clause_names() {
    "$@" 2>/dev/null | grep -oP '\[\K[^\]]+' | sort
}

# ========== 参数校验 ==========

t_no_args() {
    need_bin || return
    check_exit 1 isarch && pass
}

t_unknown_command() {
    need_all || return
    check_exit 1 isarch -A "$IR_FILE" -C "$CONFIG_FILE" nonexistent-command &&
    check_output "unknown\|未知\|error" isarch -A "$IR_FILE" -C "$CONFIG_FILE" nonexistent-command &&
    pass
}

# ========== 基本子命令 ==========

t_list_instructions() {
    need_all || return
    check_exit 0 isarch -A "$IR_FILE" -C "$CONFIG_FILE" list-instructions && pass
}

t_tree_missing_arg() {
    need_all || return
    check_exit 1 isarch -A "$IR_FILE" -C "$CONFIG_FILE" tree && pass
}

# ========== 预期结果比较 ==========

# 将 isarch list-instructions 输出保存到临时文件，供 Python verify 子命令使用
_capture_list_instructions_output() {
    local tmpfile; tmpfile="$(mktemp)"
    isarch -A "$IR_FILE" -C "$CONFIG_FILE" list-instructions > "$tmpfile" 2>/dev/null || true
    echo "$tmpfile"
}

# 检查 list-instructions 输出的 clause 数量是否与预期一致
t_list_instructions_clause_count() {
    need_all || return
    local expected_file="$EXPECTED_DIR/clause_names.txt"
    if [ ! -f "$expected_file" ]; then
        skip "预期文件不存在: $expected_file"
        return
    fi
    local expected_count; expected_count=$(grep -cv '^#\|^$' "$expected_file")
    local tmpfile; tmpfile="$(_capture_list_instructions_output)"
    local actual_count; actual_count=$(grep -oP '\[\K[^\]]+' "$tmpfile" | wc -l)
    rm -f "$tmpfile"
    if [ "$actual_count" -lt "$expected_count" ]; then
        fail "clause 数量不足: 期望≥$expected_count 实际=$actual_count"
        return
    fi
    pass
}

# 检查关键 clause 是否在 list-instructions 输出中
t_list_instructions_key_clauses() {
    need_all || return
    local tmpfile; tmpfile="$(_capture_list_instructions_output)"
    local missing=0
    for clause in RTYPE ITYPE BTYPE UTYPE LOAD STORE JAL JALR; do
        if ! grep -qP "\[$clause\]" "$tmpfile"; then
            echo "  缺少 clause: $clause"
            missing=$((missing + 1))
        fi
    done
    rm -f "$tmpfile"
    [ "$missing" -eq 0 ] && pass || fail "缺少 $missing 个关键 clause"
}

# 集合级比较: 调用 Python verify 子命令对每个 clause 做预期与实际的交集检查
t_list_instructions_assembly_names() {
    need_all || return
    local tmpfile; tmpfile="$(_capture_list_instructions_output)"
    local rc=0
    python3 "$LIST_INST_DIR/extract_sail_clauses.py" verify "$tmpfile" || rc=$?
    rm -f "$tmpfile"
    if [ "$rc" -eq 0 ]; then
        pass
    else
        fail "集合级比较失败 (见上方详情)"
    fi
}

# 漂移检测: 重新 generate expected 文件，与已提交版本比较
t_expected_files_fresh() {
    local tmpdir; tmpdir="$(mktemp -d)"
    python3 "$LIST_INST_DIR/extract_sail_clauses.py" generate --outdir "$tmpdir" >/dev/null 2>&1
    local rc=0
    for f in clause_names.txt assembly_names.txt summary.txt; do
        if ! diff -q "$EXPECTED_DIR/$f" "$tmpdir/$f" >/dev/null 2>&1; then
            echo "  漂移: $f 与 generate 输出不一致"
            diff "$EXPECTED_DIR/$f" "$tmpdir/$f" | head -10
            rc=1
        fi
    done
    rm -rf "$tmpdir"
    [ "$rc" -eq 0 ] && pass || fail "expected/*.txt 与 generate 输出漂移，请运行 extract_sail_clauses.py generate"
}

# ========== debug-instruction ==========

t_debug_instruction_default() {
    need_all || return
    check_exit -t 360 0 isarch -A "$IR_FILE" -C "$CONFIG_FILE" debug-instruction && pass
}

t_debug_instruction_with_clause() {
    need_all || return
    check_exit -t 360 0 isarch -A "$IR_FILE" -C "$CONFIG_FILE" debug-instruction zRTYPE && pass
}

# ========== debug-clause-args ==========

t_debug_clause_args() {
    need_all || return
    check_exit 0 isarch -A "$IR_FILE" -C "$CONFIG_FILE" debug-clause-args && pass
}

# ========== debug-clause-args-yaml ==========

t_debug_clause_args_yaml() {
    need_all || return
    local tmpdir; tmpdir="$(in_tmpdir 120 isarch -A "$IR_FILE" -C "$CONFIG_FILE" debug-clause-args-yaml)"
    local n; n=$(find "$tmpdir" -name "args_*.yaml" | wc -l)
    rm -rf "$tmpdir"
    [ "$n" -gt 0 ] && pass || fail "未生成 args_*.yaml（共 $n 个）"
}

# ========== 注册表 ==========

ALL_TESTS=(
    t_no_args
    t_unknown_command
    t_list_instructions
    t_list_instructions_clause_count
    t_list_instructions_key_clauses
    t_list_instructions_assembly_names
    t_expected_files_fresh
    t_tree_missing_arg
    t_debug_instruction_default
    t_debug_instruction_with_clause
    t_debug_clause_args
    t_debug_clause_args_yaml
)

# 快速测试子集（不含耗时的符号执行测试）
QUICK_TESTS=(
    t_no_args
    t_unknown_command
    t_expected_files_fresh
    t_list_instructions
    t_list_instructions_clause_count
    t_list_instructions_key_clauses
    t_tree_missing_arg
)

# ========== main ==========

echo "=== isarch CLI 集成测试 ==="
echo "  binary: $ISARCH_BIN"
echo "  IR:     $IR_FILE"
echo "  config: $CONFIG_FILE"
echo ""

# quick 模式只跑快速测试子集
if [ $# -gt 0 ] && [ "$1" = "quick" ]; then
    TESTS=("${QUICK_TESTS[@]}")
    set --  # 清空参数，避免后续过滤逻辑干扰
else
    TESTS=("${ALL_TESTS[@]}")
fi

for t in "${TESTS[@]}"; do
    # all / 无参数 → 全跑；否则按名称子串过滤
    if [ $# -gt 0 ] && [ "$1" != "all" ]; then
        match=false
        for pattern in "$@"; do
            [[ "$t" == *"$pattern"* ]] && match=true && break
        done
        [ "$match" = false ] && continue
    fi

    _CUR="$t"
    $t
done

echo ""
echo "=== 结果 ==="
for r in "${RESULTS[@]}"; do echo "  $r"; done
echo ""
echo "  通过: $PASS  失败: $FAIL  跳过: $SKIP"

if [ "$FAIL" -gt 0 ]; then exit 1; fi
