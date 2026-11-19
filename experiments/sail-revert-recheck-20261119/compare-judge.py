#!/usr/bin/env python3
"""比较已完成的常驻 judge，以及可受 IR 结构影响的守卫和路径签名。"""

import json
from pathlib import Path
import sys


def read_judge(directory):
    fields = {}
    files = {
        "report": "[JUDGE_RESIDENT_REPORT] ",
        "measurements": "[JUDGE_RESIDENT_MEASUREMENTS] ",
        "saved": "[JUDGE_RESIDENT_SAVED] ",
    }
    for line in (directory / "raw.log").open():
        for name, prefix in files.items():
            if line.startswith(prefix):
                fields[name] = json.loads(line[len(prefix):])
    product = directory / "judge.jsonl"
    rows = [json.loads(line) for line in product.read_text().splitlines() if line.strip()] if product.exists() else []
    return fields, {row["sample_id"]: row for row in rows}


def compare_registers(actual, reference):
    return {
        key: [actual.get(key), reference.get(key)]
        for key in sorted(actual.keys() | reference.keys())
        if actual.get(key) != reference.get(key)
    }


def compare_sample(actual, reference):
    actual_sample = actual["sample"]
    reference_sample = reference["sample"]
    architectural_keys = (
        "pre_registers", "post_registers", "pre_memory", "post_memory", "isa_state",
        "terminal", "result", "ret_val",
    )
    return {
        "architectural_fields_equal": {
            key: actual_sample[key] == reference_sample[key] for key in architectural_keys
        },
        "register_differences": {
            key: compare_registers(actual_sample[key], reference_sample[key])
            for key in ("pre_registers", "post_registers")
        },
        "sample_fields_differing": [
            key for key in sorted(actual_sample.keys() | reference_sample.keys())
            if actual_sample.get(key) != reference_sample.get(key)
        ],
        "guard_unique": [actual["guard_unique"], reference["guard_unique"]],
        "post_unique": [actual["post_unique"], reference["post_unique"]],
        "guard_counts": [len(row["guard_vector"]) for row in (actual, reference)],
        "ordered_guards_equal": actual["guard_vector"] == reference["guard_vector"],
        "path_signatures": [actual["path_signature"], reference["path_signature"]],
    }


actual_dir, reference_dir = map(Path, sys.argv[1:3])
actual, a_rows = read_judge(actual_dir)
reference, b_rows = read_judge(reference_dir)
summary = {
    "actual": actual,
    "reference": reference,
    "reports_equal": "report" in actual and actual["report"] == reference.get("report"),
    "actual_ids": sorted(a_rows),
    "reference_ids": sorted(b_rows),
    "samples": {key: compare_sample(a_rows[key], b_rows[key]) for key in sorted(a_rows.keys() & b_rows.keys())},
}
print(json.dumps(summary, ensure_ascii=False, indent=2))
