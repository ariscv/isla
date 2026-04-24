#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
OUT_DIR="$ROOT_DIR/agents/start_multi_inline_spawn/out"
mkdir -p "$OUT_DIR"

RUN_LABEL="${1:-make_run}"
TIMEOUT_SECS="${TIMEOUT_SECS:-100}"
SAMPLE_INTERVAL="${SAMPLE_INTERVAL:-1}"
CPU_COUNT="$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc)"
STAMP="$(date +%Y%m%d_%H%M%S)"

RUN_LOG="$OUT_DIR/${RUN_LABEL}_${STAMP}.run.log"
SAMPLE_CSV="$OUT_DIR/${RUN_LABEL}_${STAMP}.cpu.csv"
SUMMARY_TXT="$OUT_DIR/${RUN_LABEL}_${STAMP}.summary.txt"

collect_descendants() {
    local pid="$1"
    local children
    printf '%s\n' "$pid"
    children="$(pgrep -P "$pid" || true)"
    if [[ -n "$children" ]]; then
        while IFS= read -r child; do
            [[ -n "$child" ]] || continue
            collect_descendants "$child"
        done <<< "$children"
    fi
}

sum_tree_cpu() {
    local root_pid="$1"
    local pid_list
    local cpu_sum

    pid_list="$(collect_descendants "$root_pid" | awk '!seen[$0]++' | paste -sd, -)"
    if [[ -z "$pid_list" ]]; then
        echo "0"
        return
    fi

    cpu_sum="$(ps -o %cpu= -p "$pid_list" 2>/dev/null | awk '{sum += $1} END {printf "%.2f", sum + 0}')"
    echo "${cpu_sum:-0}"
}

{
    echo "label=$RUN_LABEL"
    echo "timeout_secs=$TIMEOUT_SECS"
    echo "sample_interval=$SAMPLE_INTERVAL"
    echo "cpu_count=$CPU_COUNT"
    echo "command=timeout $TIMEOUT_SECS make run"
    echo "run_log=$RUN_LOG"
    echo "sample_csv=$SAMPLE_CSV"
} > "$SUMMARY_TXT"

cd "$ROOT_DIR"

echo "timestamp_sec,elapsed_sec,total_cpu_percent,normalized_cpu_percent,pid_count" > "$SAMPLE_CSV"

timeout "$TIMEOUT_SECS" make run >"$RUN_LOG" 2>&1 &
TARGET_PID=$!
START_TS="$(date +%s)"
RUN_EXIT_CODE=0

while kill -0 "$TARGET_PID" 2>/dev/null; do
    NOW_TS="$(date +%s)"
    ELAPSED="$((NOW_TS - START_TS))"
    PID_LIST="$(collect_descendants "$TARGET_PID" | awk '!seen[$0]++')"
    PID_COUNT="$(printf '%s\n' "$PID_LIST" | sed '/^$/d' | wc -l | tr -d ' ')"
    TOTAL_CPU="$(sum_tree_cpu "$TARGET_PID")"
    NORMALIZED_CPU="$(awk -v cpu="$TOTAL_CPU" -v cores="$CPU_COUNT" 'BEGIN { if (cores == 0) { printf "0.00" } else { printf "%.2f", cpu / cores } }')"
    echo "$NOW_TS,$ELAPSED,$TOTAL_CPU,$NORMALIZED_CPU,$PID_COUNT" >> "$SAMPLE_CSV"
    sleep "$SAMPLE_INTERVAL"
done

if wait "$TARGET_PID"; then
    RUN_EXIT_CODE=0
else
    RUN_EXIT_CODE=$?
fi

awk -F, -v run_exit_code="$RUN_EXIT_CODE" -v summary_file="$SUMMARY_TXT" '
NR == 1 { next }
{
    count += 1
    cpu = $3 + 0
    norm = $4 + 0
    if (count == 1 || cpu < min_cpu) min_cpu = cpu
    if (count == 1 || cpu > max_cpu) max_cpu = cpu
    if (count == 1 || norm < min_norm) min_norm = norm
    if (count == 1 || norm > max_norm) max_norm = norm
    sum_cpu += cpu
    sum_norm += norm
}
END {
    avg_cpu = (count == 0 ? 0 : sum_cpu / count)
    avg_norm = (count == 0 ? 0 : sum_norm / count)
    printf "run_exit_code=%d\n", run_exit_code >> summary_file
    printf "sample_count=%d\n", count >> summary_file
    printf "cpu_percent_min=%.2f\n", min_cpu + 0 >> summary_file
    printf "cpu_percent_avg=%.2f\n", avg_cpu >> summary_file
    printf "cpu_percent_max=%.2f\n", max_cpu + 0 >> summary_file
    printf "normalized_cpu_percent_min=%.2f\n", min_norm + 0 >> summary_file
    printf "normalized_cpu_percent_avg=%.2f\n", avg_norm >> summary_file
    printf "normalized_cpu_percent_max=%.2f\n", max_norm + 0 >> summary_file
}' "$SAMPLE_CSV"

cat "$SUMMARY_TXT"
