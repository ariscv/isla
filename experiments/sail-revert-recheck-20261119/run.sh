#!/usr/bin/env bash
set -euo pipefail

root=$1
data=$2
z3_root=$3
mode=$4
shift 4
binary="$data/target/release/isarch"
iter="$root/agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter"
judge_inputs="$iter/raw/lazy-pmp2-judge-20261117/inputs"
historical="$iter/raw/sail-revert-20261118"
loader=(/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2 --library-path "$z3_root/lib")
ulimit -s 65536
unset ISLA_EXPORT_SAMPLES

execute() (
    label=$1
    wall=$2
    path_time=$3
    shift 3
    mkdir -p "$data/runs"
    mkdir "$data/runs/$label"
    cd "$data/runs/$label"
    printf '%s %s\n' "$(date -Is)" "$label"
    printf 'program_wall_s=%s\nouter_wall_s=%s\nper_path_s=%s\n' "$wall" "$((wall + 10))" "$path_time" > budgets.txt
    printf '%q ' "${loader[@]}" "$binary" "$@" > argv.txt
    printf '\n' >> argv.txt
    "${loader[@]}" --list "$binary" > linked.txt
    {
        date -Is
        uptime
        free -m
    } > resources-start.txt
    status=0
    timeout --kill-after=2s "$((wall + 10))s" \
        /usr/bin/time -o measure.txt -f 'elapsed_s=%e\npeak_rss_kib=%M\nexit_status=%x' \
        timeout --foreground --kill-after=5s "${wall}s" "${loader[@]}" "$binary" "$@" > raw.log 2>&1 || status=$?
    printf '%s\n' "$status" > exit.txt
    {
        date -Is
        uptime
        free -m
    } > resources-end.txt
    cat measure.txt
    printf 'status=%s\n' "$status"
)

case "$mode" in
    probe)
        variant=$1
        clause=$2
        wall=$3
        execute "$variant-${clause,,}-$wall" "$wall" 1200 \
            -A "$data/$variant/rv64d.ir" -C "$data/probe.toml" -T 32 --tastic default \
            --path-merging --verbose -D s --merge-diagnostics detail --memory-stats \
            --path-cache-only --path-cache-write "cache/$clause" --path-cache-format both \
            solve-state "--clause=$clause" --timeout 1200s
        ;;
    judge)
        variant=$1
        wall=$2
        suffix=$3
        shift 3
        merge=--path-merging
        if [[ ${1:-} == --no-path-merging ]]; then
            merge=$1
            shift
        fi
        execute "$variant-judge$suffix" "$wall" 600 \
            -A "$data/$variant/rv64d.ir" -C "${SAIL_RECHECK_JUDGE_CONFIG:-$judge_inputs/pmp2.toml}" \
            -T 32 --tastic default --instruction-bits 0x00008103 \
            --judge-resident "$judge_inputs/judge-input-complete-r4.jsonl" --judge-resident-out judge.jsonl \
            "$merge" --merge-diagnostics "${SAIL_RECHECK_DIAGNOSTICS:-summary}" --memory-stats --region-defer-exit-check=true \
            --region-lazy-z3-scope=true --region-witness-eval=true --region-progress=true \
            --finite-domain-enumeration=true "$@" solve-state --clause=LOAD --timeout 600s
        ;;
    check)
        variant=$1
        clause=$2
        case_name=${clause,,}
        historical_case="$historical/cases/sailrevert_final_kept_fixed_$case_name"
        # 复用历史任务的固定编码及定向前态，仅替换输入 IR 并开启样本检查。
        mapfile -t fixed < <(jq -er '.argv | .[index("--instruction-bits"):index("solve-state")][]' "$historical_case/task.json")
        test "${fixed[0]}" = "--instruction-bits"
        execute "$variant-check-$case_name" 60 30 \
            -A "$data/$variant/rv64d.ir" -C "$historical/default.toml" -T 32 \
            "${fixed[@]}" --check-samples "$historical_case/samples.jsonl" --check-samples-report check.json \
            solve-state "--clause=$clause" --timeout 30s
        ;;
    *)
        printf '未知实验入口 %s\n' "$mode" >&2
        exit 2
        ;;
esac
