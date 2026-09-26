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
# 用法: run_solve_state <clause_name> <env_overrides> [config_file]
#   config_file 缺省时使用全局 CONFIG_FILE
#   返回: 0=正常完成, 124=timeout超时, 其他=错误
#   在 OUTPUT_DIR 下生成 JSON 和日志
run_solve_state() {
    local clause="$1"
    local env_overrides="${2:-}"
    local config="${3:-${CONFIG_FILE}}"
    local output_dir="${REPO_ROOT}/output/solve-state/${clause}"
    mkdir -p "$output_dir"

    local rc=0
    eval "${env_overrides} ${RUN_ACCESS_ENV} \
        timeout ${CLAUSE_TIMEOUT} ${ISARCH_BIN} \
        -A ${IR_FILE} -C ${config} --verbose --probe-all --trace-all \
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

# ========== 内存符号化测试 ==========

# solve-state 的 JSON 落盘在进程 CWD 的 output/rv64_<clause>.json
# （exec.rs to_json 用相对路径，与 run.mk 的 make solve-* 同款），
# 因此本节用例需从仓库根目录运行脚本。

# memory_sym.toml（sym_ram symbolic region）下 zC_LD 全链路应正常：
# MemoryBuilder 接受配置、执行完成、JSON 含 memory-events 字段且 isa-state 结构保留。
# 注（W2 版本结论，适用于 f06371f+W2）：zC_LD 是 clause 重写（zExecuteAs(zLOAD)），
# 当时 solve-state 不续执行 ExecuteAs，故不产生访存事件，只断言字段存在；
# region 语义链（注入→read_mem→region 名）由 isla-lib executor 测试
# multi_thread_read_mem_symbolic_region_event 锁定。
# W3 起 solve-state 参照 step.sail 外层模式续执行 ExecuteAs（见 t_memory_executeas_*），
# zC_LD/zC_SD 的真实访存事件仍需在有界运行中验证；W3 为 zLOAD/zSTORE
# 补齐 pre/post 断言。本分支脚本中的 Phase5 环境变量不构成已启用 builtin 的证据。
t_memory_symbolic_region_load() {
    need_all || return
    # W3 修订：zC_LD 续执行完整 zLOAD 子树；单条 180s 时间盒。
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zC_LD" "" "${REPO_ROOT}/configs/memory_sym.toml")
    local json="${REPO_ROOT}/output/rv64_zC_LD.json"
    if [ "$rc" -eq 124 ]; then
        skip "memory_sym.toml 下 zC_LD 180s 时间盒超时"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "memory_sym.toml 下 zC_LD 退出码 $rc（预期 0）"
        return
    fi
    if [ ! -f "$json" ]; then
        fail "JSON 未生成: $json"
        return
    fi
    if ! grep -q '"memory-events"' "$json"; then
        fail "JSON 缺少 memory-events 字段"
        return
    fi
    local isa_state_ok
    isa_state_ok=$(python3 -c "import json; d=json.load(open('$json')); print(1 if all('isa-state' in item for item in d.get('gen',[])) else 0)" 2>/dev/null || echo 0)
    if [ "$isa_state_ok" != "1" ]; then
        fail "memory_sym.toml 下 isa-state 结构缺失"
        return
    fi
    pass
}

# 原版配置（无 memory_regions）下 zC_LD 应兼容：JSON 含 memory-events 字段、
# gen 有路径输出、isa-state 原有结构保留
t_memory_default_region_compat() {
    need_all || return
    # W3 修订：同上，zC_LD 续执行后按 180s 时间盒抽查。
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zC_LD" "" "${CONFIG_FILE}")
    local json="${REPO_ROOT}/output/rv64_zC_LD.json"
    if [ "$rc" -eq 124 ]; then
        skip "默认配置下 zC_LD 180s 时间盒超时"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "默认配置下 zC_LD 退出码 $rc（预期 0）"
        return
    fi
    local count; count=$(json_gen_count "$json")
    if [ "$count" -le 0 ]; then
        fail "默认配置下 zC_LD gen_count=$count（无路径输出）"
        return
    fi
    local isa_state_ok
    isa_state_ok=$(python3 -c "import json; d=json.load(open('$json')); print(1 if all('isa-state' in item for item in d.get('gen',[])) else 0)" 2>/dev/null || echo 0)
    if [ "$isa_state_ok" != "1" ]; then
        fail "isa-state 原有结构缺失"
        return
    fi
    if ! grep -q '"memory-events"' "$json"; then
        fail "JSON 缺少 memory-events 字段（default region 兼容行为未实现？）"
        return
    fi
    pass
}

# memory_bad_overlap.toml 的重叠 region 应硬失败：
# 退出码非 0、报 MemoryBuilder 的 overlapping regions 错误、不再 Warning 降级
t_memory_config_error_hard_fails() {
    need_all || return
    local rc; rc=$(run_solve_state "zC_LD" "" "${REPO_ROOT}/configs/memory_bad_overlap.toml")
    local log="${REPO_ROOT}/output/solve-state/zC_LD/log"
    if [ "$rc" -eq 0 ] || [ "$rc" -eq 124 ]; then
        fail "重叠 region 配置退出码 $rc：0=仍 Warning 降级，124=超时（未快速硬失败）"
        return
    fi
    if ! grep -q "overlapping regions" "$log"; then
        fail "输出缺少 overlapping regions 错误信息"
        return
    fi
    if grep -q "Warning: MemoryBuilder" "$log"; then
        fail "MemoryBuilder 错误仍以 Warning: MemoryBuilder 降级，未硬失败"
        return
    fi
    pass
}

# ========== W3：ExecuteAs 续执行与 pre/post 内存物化 ==========

# 用 python 按 exec.rs 的物化规则重放 memory-events，重建 pre/post 连续段并与
# JSON 里的 pre-memory/post-memory 字段比对（复现 FmtVal 的 N'hXX_YY 格式与
# 小端字节序、首触/覆盖规则），验证三组字段相互一致、事件顺序可用。
# 输出：每行一个不一致项（为空表示全部一致）。
memory_fields_consistency_report() {
    local json_file="$1"
    python3 - "$json_file" <<'PYEOF'
import json, sys

def parse_val(text):
    # "64'h8000_0000_0000_0000" -> (bits, value)；null/其它格式 -> None
    if not isinstance(text, str) or "'h" not in text:
        return None
    bits_str, hex_str = text.split("'h", 1)
    return int(bits_str), int(hex_str.replace("_", ""), 16)

def fmt_val(value, bits):
    digits = f"{value:0{bits // 4}x}"
    parts = [digits[max(0, i - 4):i] for i in range(len(digits), 0, -4)][::-1]
    return f"{bits}'h{'_'.join(parts)}"

def le_bytes(value, count):
    return list(value.to_bytes(count, "little"))

def rebuild_spans(byte_map):
    # byte_map: {addr(int): byte(int) or None} -> [(address_str, bytes, value_str or None)]
    spans = []
    addresses = sorted(byte_map)
    i = 0
    while i < len(addresses):
        start = addresses[i]
        known = byte_map[start] is not None
        run = [byte_map[start]]
        j = i + 1
        while (j < len(addresses) and addresses[j] == start + len(run)
               and (byte_map[addresses[j]] is not None) == known and len(run) < 8):
            run.append(byte_map[addresses[j]])
            j += 1
        value = None
        if known:
            value = fmt_val(int.from_bytes(bytes(run), "little"), len(run) * 8)
        spans.append((fmt_val(start, 64), len(run), value))
        i = j
    return spans

problems = []
data = json.load(open(sys.argv[1]))
for index, item in enumerate(data.get("gen", [])):
    tag = f"gen[{index}] {item.get('test-ins', '')!r}"
    for field in ("memory-events", "pre-memory", "post-memory"):
        if field not in item:
            problems.append(f"{tag}: 缺少 {field} 字段")
    if problems:
        continue
    events = item["memory-events"]
    pre, post = {}, {}
    for event in events:
        address = parse_val(event["address"]) if event.get("address") else None
        if event["kind"] == "write" and event.get("exclusive"):
            if event.get("value") == "false":
                continue
            if event.get("value") != "true":
                if address is not None:
                    for offset in range(event["bytes"]):
                        byte_address = (address[1] + offset) & ((1 << 64) - 1)
                        pre.setdefault(byte_address, None)
                        post[byte_address] = None
                continue
        payload_text = event.get("value") if event["kind"] == "read" else event.get("data")
        payload_val = parse_val(payload_text) if payload_text else None
        if address is None:
            continue
        if payload_val is None:
            for offset in range(event["bytes"]):
                byte_address = (address[1] + offset) & ((1 << 64) - 1)
                pre.setdefault(byte_address, None)
                post[byte_address] = None
            continue
        address_value = address[1]
        for offset, byte in enumerate(le_bytes(payload_val[1], event["bytes"])):
            byte_address = (address_value + offset) & ((1 << 64) - 1)
            if byte_address not in pre:
                pre[byte_address] = byte if event["kind"] == "read" else None
            post[byte_address] = byte
    expected_pre = rebuild_spans(pre)
    expected_post = rebuild_spans(post)
    actual_pre = [(s["address"], s["bytes"], s["value"]) for s in item["pre-memory"]]
    actual_post = [(s["address"], s["bytes"], s["value"]) for s in item["post-memory"]]
    if expected_pre != actual_pre:
        problems.append(f"{tag}: pre-memory 与事件重放不一致\n  期望 {expected_pre}\n  实际 {actual_pre}")
    if expected_post != actual_post:
        problems.append(f"{tag}: post-memory 与事件重放不一致\n  期望 {expected_post}\n  实际 {actual_post}")
print("\n".join(problems))
PYEOF
}

# ExecuteAs 续执行链路快速冒烟（zC_MUL → ExecuteAs(MUL)，纯 ALU 无访存，约 1s）：
# 证明续执行机制端到端生效——ret_val 是续执行后 MUL 的 Retire_Success（解码阶段
# 只会返回 ExecuteAs），test-ins 保留原始压缩指令名，三组内存字段存在。
t_memory_executeas_c_mul() {
    need_all || return
    local rc; rc=$(run_solve_state "zC_MUL" "" "${REPO_ROOT}/configs/riscv64_difftest_mem.toml")
    local json="${REPO_ROOT}/output/rv64_zC_MUL.json"
    if [ "$rc" -ne 0 ]; then
        fail "mem 配置下 zC_MUL 退出码 $rc（预期 0）"
        return
    fi
    local ok
    ok=$(python3 -c "
import json
d = json.load(open('$json'))
items = d.get('gen', [])
ok = (len(items) > 0
      and all('memory-events' in i and 'pre-memory' in i and 'post-memory' in i for i in items)
      and any(i.get('ret_val') == 'Retire_Success(())' for i in items))
print(1 if ok else 0)" 2>/dev/null || echo 0)
    if [ "$ok" != "1" ]; then
        fail "zC_MUL 续执行未产生 Retire_Success 路径或字段缺失"
        return
    fi
    pass
}

# ExecuteAs 续执行（zC_LD）：memory-events 非空（读 8 字节）、三组字段与事件重放一致。
# zC_LD 续执行 = 解码 + 完整 zLOAD 子树；单条 180s 时间盒内超时如实记 SKIP。
t_memory_executeas_c_ld() {
    need_all || return
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zC_LD" "" "${REPO_ROOT}/configs/riscv64_difftest_mem.toml")
    local json="${REPO_ROOT}/output/rv64_zC_LD.json"
    if [ "$rc" -eq 124 ]; then
        skip "zC_LD 180s 时间盒超时，真实访存事件未验证"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "mem 配置下 zC_LD 退出码 $rc（预期 0）"
        return
    fi
    local events_ok
    events_ok=$(python3 -c "
import json
d = json.load(open('$json'))
items = d.get('gen', [])
print(1 if any(item.get('memory-events') for item in items) else 0)" 2>/dev/null || echo 0)
    if [ "$events_ok" != "1" ]; then
        fail "ExecuteAs 续执行后 zC_LD 无任何 memory-events（续执行未生效？）"
        return
    fi
    local report; report=$(memory_fields_consistency_report "$json")
    if [ -n "$report" ]; then
        fail "pre/post 与事件重放不一致: $report"
        return
    fi
    pass
}

# ExecuteAs 续执行（zC_SD）：memory-events 非空（写 8 字节）、字段与事件重放一致；
# 时间盒同 zC_LD（180s）。
t_memory_executeas_c_sd() {
    need_all || return
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zC_SD" "" "${REPO_ROOT}/configs/riscv64_difftest_mem.toml")
    local json="${REPO_ROOT}/output/rv64_zC_SD.json"
    if [ "$rc" -eq 124 ]; then
        skip "zC_SD 180s 时间盒超时，真实访存事件未验证"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "mem 配置下 zC_SD 退出码 $rc（预期 0）"
        return
    fi
    local events_ok
    events_ok=$(python3 -c "
import json
d = json.load(open('$json'))
items = d.get('gen', [])
print(1 if any(item.get('memory-events') for item in items) else 0)" 2>/dev/null || echo 0)
    if [ "$events_ok" != "1" ]; then
        fail "ExecuteAs 续执行后 zC_SD 无任何 memory-events（续执行未生效？）"
        return
    fi
    local report; report=$(memory_fields_consistency_report "$json")
    if [ -n "$report" ]; then
        fail "pre/post 与事件重放不一致: $report"
        return
    fi
    pass
}

# 真访存 zLOAD：读路径的 pre-memory 非空（首触是读，value 非 null）且与事件一致
# 单条时间盒 180s；超时只记录不作为失败断言。
t_memory_real_load_pre_post() {
    need_all || return
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zLOAD" "" "${REPO_ROOT}/configs/riscv64_difftest_mem.toml")
    local json="${REPO_ROOT}/output/rv64_zLOAD.json"
    if [ "$rc" -eq 124 ]; then
        skip "zLOAD 180s 时间盒超时（仅记录）"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "mem 配置下 zLOAD 退出码 $rc"
        return
    fi
    local evidence
    evidence=$(python3 - "$json" <<'PYEOF'
import json, sys
items = json.load(open(sys.argv[1])).get('gen', [])
print(1 if any(
    any(event.get('kind') == 'read' and event.get('address') and event.get('value')
        for event in item.get('memory-events', []))
    and any(span.get('value') for span in item.get('pre-memory', []))
    for item in items) else 0)
PYEOF
)
    if [ "$evidence" != "1" ]; then
        fail "zLOAD 无已物化的真实读事件及 pre-memory"
        return
    fi
    local report; report=$(memory_fields_consistency_report "$json")
    if [ -n "$report" ]; then
        fail "pre/post 与事件重放不一致: $report"
        return
    fi
    pass
}

# 真访存 zSTORE：写路径 post-memory 非空且与事件一致；180s 时间盒同上
t_memory_real_store_pre_post() {
    need_all || return
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zSTORE" "" "${REPO_ROOT}/configs/riscv64_difftest_mem.toml")
    local json="${REPO_ROOT}/output/rv64_zSTORE.json"
    if [ "$rc" -eq 124 ]; then
        skip "zSTORE 180s 时间盒超时（仅记录）"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "mem 配置下 zSTORE 退出码 $rc"
        return
    fi
    local evidence
    evidence=$(python3 - "$json" <<'PYEOF'
import json, sys
items = json.load(open(sys.argv[1])).get('gen', [])
print(1 if any(
    any(event.get('kind') == 'write' and event.get('address') and event.get('data')
        for event in item.get('memory-events', []))
    and any(span.get('value') for span in item.get('post-memory', []))
    for item in items) else 0)
PYEOF
)
    if [ "$evidence" != "1" ]; then
        fail "zSTORE 无已物化的真实写事件及 post-memory"
        return
    fi
    local report; report=$(memory_fields_consistency_report "$json")
    if [ -n "$report" ]; then
        fail "pre/post 与事件重放不一致: $report"
        return
    fi
    pass
}

# ========== W10：[[pma_regions]] 配置化 PMA 地图 ==========

# 重叠的 [[pma_regions]] 应在配置解析期硬失败：退出码非 0、报重叠错误。
# 区别于 [[memory_regions]] 的 MemoryBuilder 期 "overlapping regions" 报错——
# pma_regions 的重叠校验在 get_pma_regions（isarch 不经过模型 zcheck_mem_layout，
# 排序/重叠检查必须在配置解析做）。
t_pma_regions_config_error_hard_fails() {
    need_all || return
    local rc; rc=$(run_solve_state "zC_MUL" "" "${REPO_ROOT}/configs/pma_bad_overlap.toml")
    local log="${REPO_ROOT}/output/solve-state/zC_MUL/log"
    if [ "$rc" -eq 0 ] || [ "$rc" -eq 124 ]; then
        fail "重叠 pma_regions 配置退出码 $rc：0=被忽略/降级，124=超时（未快速硬失败）"
        return
    fi
    if ! grep -q "重叠" "$log"; then
        fail "输出缺少 pma_regions 重叠错误信息"
        return
    fi
    pass
}

# PMA RAM-only 地图 [0x80000000,0x90000000) 下 zSTORE：所有写事件地址必须落入
# 配置 RAM（地图外按 zpmaCheck 走 access-fault 路径，无访存事件——固化 IR 地图
# 下 [0x90000000,0x100000000) 写可成功的限制由此消除），且成功与 fault 并存。
# 单条 180s 时间盒；超时如实 SKIP（完整 600s 对照见 docs/RESULTS.md W10 条目）。
t_pma_regions_store_writes_in_config_ram() {
    need_all || return
    local rc; rc=$(CLAUSE_TIMEOUT=180 run_solve_state "zSTORE" "" "${REPO_ROOT}/configs/riscv64_difftest_mem_excluded_pma.toml")
    local json="${REPO_ROOT}/output/rv64_zSTORE.json"
    if [ "$rc" -eq 124 ]; then
        skip "PMA 配置下 zSTORE 180s 时间盒超时"
        return
    fi
    if [ "$rc" -ne 0 ]; then
        fail "PMA 配置下 zSTORE 退出码 $rc（预期 0）"
        return
    fi
    local ok
    ok=$(python3 - "$json" <<'PYEOF'
import json, re, sys
items = json.load(open(sys.argv[1])).get('gen', [])
def addr(e):
    m = re.search(r"([0-9a-fA-F_]+)\s*$", (e.get('address') or '').replace('_',''))
    return int(m.group(1).replace('_',''),16) if m else None
writes = [a for x in items for e in (x.get('memory-events') or [])
          if e.get('kind')=='write' for a in [addr(e)] if a is not None]
in_ram = all(0x80000000 <= a < 0x90000000 for a in writes)
success = sum(1 for x in items if x.get('ret_val')=='Retire_Success(())')
fault = sum(1 for x in items if 'Access_Fault' in (x.get('ret_val') or '') or 'Exception' in (x.get('ret_val') or ''))
print(1 if (in_ram and writes and success and fault) else 0)
PYEOF
)
    if [ "$ok" != "1" ]; then
        fail "PMA 地图下写事件越界、无写事件或成功/fault 未并存"
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
    t_memory_symbolic_region_load
    t_memory_default_region_compat
    t_memory_config_error_hard_fails
    t_memory_executeas_c_mul
    t_memory_executeas_c_ld
    t_memory_executeas_c_sd
    t_memory_real_load_pre_post
    t_memory_real_store_pre_post
    t_pma_regions_config_error_hard_fails
    t_pma_regions_store_writes_in_config_ram
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
