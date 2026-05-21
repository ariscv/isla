#!/bin/bash
#
# ExecutionLimits smoke test
# 验证符号执行路径爆炸限制机制在真实 IR 上的端到端行为
#
# 依赖: isarch 二进制已编译 (cargo build --release --bin isarch)
# 运行: bash test/execution-limits/run_tests.sh
#
# 参考: specs/path-explosion-limiting.md

set -euo pipefail

# ── 定位仓库根目录 ──
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$DIR"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

pass=0
fail=0

check() {
    local desc="$1"
    shift
    local expected_exit="$1"
    shift

    local tmpout
    tmpout=$(mktemp)
    local exit_code=0
    "$@" > "$tmpout" 2>&1 || exit_code=$?

    if [ "$exit_code" -eq "$expected_exit" ]; then
        printf "  ${GREEN}PASS${NC} %s (exit=%d)\n" "$desc" "$exit_code"
        pass=$((pass + 1))
    else
        printf "  ${RED}FAIL${NC} %s (expected exit=%d, got=%d)\n" "$desc" "$expected_exit" "$exit_code"
        printf "    --- output ---\n"
        head -20 "$tmpout" | sed 's/^/    /'
        printf "    --- end ---\n"
        fail=$((fail + 1))
    fi

    rm -f "$tmpout"
}

check_output_contains() {
    local desc="$1"
    local pattern="$2"
    shift 2
    local tmpout
    tmpout=$(mktemp)
    "$@" > "$tmpout" 2>&1 || true

    if grep -qE "$pattern" "$tmpout"; then
        printf "  ${GREEN}PASS${NC} %s\n" "$desc"
        pass=$((pass + 1))
    else
        printf "  ${RED}FAIL${NC} %s (pattern not found: %s)\n" "$desc" "$pattern"
        printf "    --- output (last 20 lines) ---\n"
        tail -20 "$tmpout" | sed 's/^/    /'
        printf "    --- end ---\n"
        fail=$((fail + 1))
    fi

    rm -f "$tmpout"
}

# ── 前置检查 ──

ISARCH="target/release/isarch"
IR="$DIR/rv64d.ir"
CONFIG="$DIR/configs/riscv64_difftest.toml"

if [ ! -x "$ISARCH" ]; then
    printf "${YELLOW}Building isarch...${NC}\n"
    cargo build --release --bin isarch
fi

if [ ! -f "$IR" ]; then
    printf "${RED}ERROR: rv64d.ir not found at %s${NC}\n" "$IR"
    exit 1
fi

if [ ! -f "$CONFIG" ]; then
    printf "${RED}ERROR: config not found at %s${NC}\n" "$CONFIG"
    exit 1
fi

printf "\n=== ExecutionLimits Smoke Tests ===\n\n"

# ── Test 1: list-instructions 基本流程能正常完成 ──
# 验证 isarch 加载 rv64d.ir 后执行 list-instructions 命令成功退出
# ExecutionLimits 配置为 Concretize 模式，所有路径应正常完成而非报错
check \
    "list-instructions completes successfully" \
    0 \
    "$ISARCH" -A "$IR" -C "$CONFIG" list-instructions

# ── Test 2: 带完整 trace 输出时也能正常完成 ──
# 验证 --verbose --probe-all --trace-all 模式下不崩溃
# 路径深度限制(max_path_depth=10000)和循环回边限制(max_backjumps=10)
# 不会导致正常指令分析中断
check \
    "list-instructions with full tracing completes" \
    0 \
    "$ISARCH" -A "$IR" -C "$CONFIG" --verbose --probe-all --trace-all list-instructions

# ── Test 3: 输出包含符号执行结果 ──
# 验证 isarch 确实执行了符号执行并产生了执行结果
# 至少应该看到 "ISA State" 输出（表示成功分析了一条指令的状态）
check_output_contains \
    "output contains ISA state (symbolic execution ran)" \
    "ISA State" \
    "$ISARCH" -A "$IR" -C "$CONFIG" --verbose list-instructions

# ── Test 4: 缺少 IR 文件时报错退出 ──
# 验证命令行参数校验
check \
    "fails with non-existent IR file" \
    1 \
    "$ISARCH" -A /nonexistent/path.ir -C "$CONFIG" list-instructions

# ── Test 5: 缺少子命令时报错退出 ──
check \
    "fails with no subcommand" \
    1 \
    "$ISARCH" -A "$IR" -C "$CONFIG"

# ── 汇总 ──
printf "\n=== Results: %d passed, %d failed ===\n" "$pass" "$fail"

if [ "$fail" -gt 0 ]; then
    exit 1
fi
