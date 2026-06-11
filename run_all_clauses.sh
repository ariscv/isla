#!/usr/bin/env bash
# 并行批量运行 isarch 符号执行所有 clauses
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

ISARCH="./target/release/isarch"
IR_FILE="./rv64d.ir"
CONFIG="./configs/riscv64_difftest.toml"
OUTPUT_DIR="./output"
LOG_DIR="./logs_todo"

JOBS=${JOBS:-16}
TIMEOUT_SEC=${TIMEOUT_SEC:-120}

usage() {
    cat <<'EOF'
Usage: ./run_all_clauses.sh [-j JOBS] [-t TIMEOUT_SEC]
  -j JOBS        并行任务数 (默认 16)
  -t TIMEOUT     每条 clause 超时秒数 (默认 120)
  -h             显示帮助
EOF
}

while getopts "j:t:h" opt; do
    case "$opt" in
        j) JOBS="$OPTARG" ;;
        t) TIMEOUT_SEC="$OPTARG" ;;
        h) usage; exit 0 ;;
        *) usage; exit 1 ;;
    esac
done

if [ ! -x "$ISARCH" ]; then
    echo "错误: $ISARCH 不存在，请先运行 cargo build --release --bin isarch"
    exit 1
fi

ITRACE_DIR="$OUTPUT_DIR/itrace"

mkdir -p "$OUTPUT_DIR" "$LOG_DIR" "$ITRACE_DIR"

# 获取所有 clause 名称
echo "正在获取所有 clause 列表..."
mapfile -t CLAUSES < <($ISARCH -A "$IR_FILE" -C "$CONFIG" list-instructions 2>/dev/null \
    | grep '^\s*\[' \
    | sed 's/.*\[\(.*\)\].*/\1/')

TOTAL=${#CLAUSES[@]}
echo "共 $TOTAL 条 clause，使用 $JOBS 并行，每条超时 ${TIMEOUT_SEC}s"

run_clause() {
    local clause_raw="$1"
    local clause_z="z${clause_raw}"
    local log_file="$LOG_DIR/${clause_z}.log"

    local itrace_file="$ITRACE_DIR/${clause_z}.txt"

    echo "[START] $clause_z at $(date +%H:%M:%S)"

    timeout "${TIMEOUT_SEC}s" $ISARCH \
        -A "$IR_FILE" \
        -C "$CONFIG" \
        --verbose \
        --debug=fmlgcsra \
        --itrace="$itrace_file" \
        solve-state --clause="$clause_z" \
        > "$log_file" 2>&1

    local exit_code=$?
    if [ $exit_code -eq 124 ]; then
        echo "[TIMEOUT] $clause_z (${TIMEOUT_SEC}s)" >> "$log_file"
        echo "[TIMEOUT] $clause_z"
    elif [ $exit_code -ne 0 ]; then
        echo "[ERROR] $clause_z (exit $exit_code)" >> "$log_file"
        echo "[ERROR] $clause_z (exit $exit_code)"
    else
        echo "[DONE] $clause_z (exit 0)" >> "$log_file"
        echo "[DONE] $clause_z"
    fi
}

# 使用 GNU parallel 风格的 job control
RUNNING=0
for clause in "${CLAUSES[@]}"; do
    run_clause "$clause" &
    RUNNING=$((RUNNING + 1))

    if [ "$RUNNING" -ge "$JOBS" ]; then
        wait -n 2>/dev/null || true
        RUNNING=$((RUNNING - 1))
    fi
done

# 等待所有后台任务完成
wait

# 统计结果
echo ""
echo "========================================="
echo "执行完成，统计结果:"
echo "========================================="

DONE=$(grep -rl "\[DONE\]" "$LOG_DIR"/*.log 2>/dev/null | wc -l || echo 0)
TIMEOUT_COUNT=$(grep -rl "\[TIMEOUT\]" "$LOG_DIR"/*.log 2>/dev/null | wc -l || echo 0)
ERROR=$(grep -rl "\[ERROR\]" "$LOG_DIR"/*.log 2>/dev/null | wc -l || echo 0)
JSON_COUNT=$(find "$OUTPUT_DIR" -maxdepth 1 -name "rv64_z*.json" | wc -l)

echo "DONE: $DONE"
echo "TIMEOUT: $TIMEOUT_COUNT"
echo "ERROR: $ERROR"
echo "JSON 文件: $JSON_COUNT"
echo "总 clause: $TOTAL"
