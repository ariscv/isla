#!/usr/bin/env python3
"""分析 trap 条目 DiffTest 的 results.ndjson 与 difftest.log，输出分类汇总。"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

ABORT_RE = re.compile(r"ABORT at pc")
DIFF_RE = re.compile(
    r"^\s*(\S+) different at pc = (\S+), right = (\S+), wrong = (\S+)", re.M
)
COMMIT_RE = re.compile(r"commit pc ([0-9a-f]+) inst ([0-9a-f]+)")


def hex_int(value: str) -> int | None:
    try:
        return int(value, 16)
    except (TypeError, ValueError):
        return None


def parse_isla_encoding(value: str) -> int | None:
    match = re.search(r"h([0-9a-fA-F_]+)", str(value))
    if match is None:
        return None
    return int(match.group(1).replace("_", ""), 16)


def parse_isla_bits(value) -> int | None:
    match = re.search(r"h([0-9a-fA-F_]+)", str(value))
    if match is None:
        return None
    return int(match.group(1).replace("_", ""), 16)


def vstart_exceeds_vlmax(state: dict, vlen_bits: int = 128) -> bool | None:
    """vstart 是否超出该 vtype 的 VLMAX（不可达 vstart，Sail 报 illegal 的典型原因）。"""
    vtype = parse_isla_bits(state.get("vtype"))
    vstart = parse_isla_bits(state.get("vstart"))
    if vtype is None or vstart is None:
        return None
    if vtype >> 63 or vtype & ~0xFF:
        return None  # VILL/保留位上下文，不以 vstart 判定
    vsew = (vtype >> 3) & 0b111
    vlmul = vtype & 0b111
    if vsew > 3 or vlmul == 0b100:
        return None
    sew = 1 << (vsew + 3)
    lmul_power = vlmul if vlmul < 4 else vlmul - 8
    numerator = vlen_bits * (1 << max(lmul_power, 0))
    denominator = sew * (1 << max(-lmul_power, 0))
    if numerator < denominator or numerator % denominator:
        return None
    return vstart > numerator // denominator


def classify_result(record: dict) -> dict:
    """单条结果分类：category + 细分 kind + 差异摘要。"""
    out = dict(record)
    state = record.get("isa-state") or {}
    out["vstart_exceeds_vlmax"] = vstart_exceeds_vlmax(state)
    if record["category"] == "success":
        out["kind"] = "success"
        return out
    log_path = record.get("log")
    text = Path(log_path).read_text(encoding="utf-8", errors="replace") if log_path else ""
    diffs = DIFF_RE.findall(text)
    out["diffs"] = [d[0] for d in diffs]
    if record.get("returncode") is None:
        out["kind"] = "timeout"
        commits = COMMIT_RE.findall(text)
        out["last_commit_pc"] = commits[-1][0] if commits else None
        out["commit_count"] = len(commits)
        encoding = parse_isla_encoding(record.get("encoding", ""))
        payload_committed = encoding is not None and any(
            inst == f"{encoding:08x}" for _, inst in commits
        )
        out["timeout_side"] = (
            "payload-executed-then-sentinel" if payload_committed else "no-payload-commit"
        )
        return out
    if ABORT_RE.search(text) or diffs:
        out["kind"] = "difftest-abort"
        diff_map = {d[0]: (d[2], d[3]) for d in diffs}
        right_mcause = hex_int(diff_map.get("mcause", ("", ""))[0])
        wrong_mcause = hex_int(diff_map.get("mcause", ("", ""))[1])
        if right_mcause and not wrong_mcause:
            out["abort_side"] = "nemu-traps-rtl-executes"
        elif wrong_mcause and not right_mcause:
            out["abort_side"] = "rtl-traps-nemu-executes"
        else:
            out["abort_side"] = "state-mismatch"
        return out
    out["kind"] = "other-failure"
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ndjson", required=True)
    parser.add_argument("--manifest", default=None)
    parser.add_argument("--output", default=None, help="把明细 JSON 写到该文件")
    args = parser.parse_args()

    records = [json.loads(line) for line in Path(args.ndjson).read_text(encoding="utf-8").splitlines() if line.strip()]
    classified = [classify_result(r) for r in records]

    kinds = Counter(r["kind"] for r in classified)
    print(f"总条数: {len(classified)}")
    for kind, count in kinds.most_common():
        print(f"  {kind}: {count}")

    print("\n== failure 细分 ==")
    for kind in ("difftest-abort", "timeout", "other-failure"):
        subset = [r for r in classified if r["kind"] == kind]
        if not subset:
            continue
        print(f"\n--- {kind} ({len(subset)}) ---")
        if kind == "difftest-abort":
            sides = Counter(r.get("abort_side") for r in subset)
            for side, count in sides.most_common():
                print(f"  {side}: {count}")
        if kind == "timeout":
            sides = Counter(r.get("timeout_side") for r in subset)
            for side, count in sides.most_common():
                print(f"  {side}: {count}")
            vstart_over = sum(1 for r in subset if r.get("vstart_exceeds_vlmax"))
            print(f"  其中 vstart>VLMAX(不可达 vstart): {vstart_over}/{len(subset)}")

    print("\n== failure 按指令助记符聚类(top 40) ==")
    mnemonic_fail: Counter = Counter()
    for r in classified:
        if r["kind"] == "success":
            continue
        mnemonic = str(r.get("instruction", "")).split()[0]
        mnemonic_fail[f"{mnemonic} [{r['kind']}]"] += 1
    for key, count in mnemonic_fail.most_common(40):
        print(f"  {count:5d}  {key}")

    print("\n== difftest-abort 差异字段频率 ==")
    diff_fields: Counter = Counter()
    for r in classified:
        if r["kind"] == "difftest-abort":
            for field in set(r["diffs"]):
                diff_fields[field] += 1
    for field, count in diff_fields.most_common():
        print(f"  {count:5d}  {field}")

    if args.output:
        Path(args.output).write_text(
            json.dumps(classified, ensure_ascii=False, indent=1), encoding="utf-8"
        )
        print(f"\n明细已写入 {args.output}")


if __name__ == "__main__":
    main()
