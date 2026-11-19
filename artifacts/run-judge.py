#!/usr/bin/env python3
"""用既有正常样本核对完整缓存。"""
import importlib.util
import json
import os
from pathlib import Path
import resource
import shlex
import subprocess
import sys
import time

spec = importlib.util.spec_from_file_location("run_long", Path(__file__).with_name("run-long.py"))
run_long = importlib.util.module_from_spec(spec)
spec.loader.exec_module(run_long)
ARTIFACTS, BINARY, IR, LOADER, ROOT, Z3 = (
    run_long.ARTIFACTS, run_long.BINARY, run_long.IR, run_long.LOADER, run_long.ROOT, run_long.Z3
)

clause = sys.argv[1]
assert clause in ("LOAD", "STORE")
directory = ARTIFACTS / clause.lower()
summary = json.loads((directory / "summary.json").read_text())
assert summary["complete"] and summary["stop"] is None
judge = directory / "judge"
judge.mkdir()
history = (ROOT / "agents/fuzz_strategy_20261112/exp/fullsym-timeout/iter/raw/solver-timeout-dead-20261118"
           / "group-merge-sync-20261119" / f"group-{clause.lower()}" / "judged.jsonl")
reference, = map(json.loads, history.read_text().splitlines())
sample = reference["sample"]
assert sample["terminal"] == "Normal" and reference["guard_unique"] and reference["post_unique"]
assert all(len(sample["pre_registers"][name]["vector"]) == 64 for name in ("pmpaddr_n", "pmpcfg_n"))
(judge / "input.jsonl").write_text(json.dumps(sample, ensure_ascii=False) + "\n")
(judge / "reference.txt").write_text(str(history.relative_to(ROOT)) + f" sample_id={reference['sample_id']}\n")
config = (ARTIFACTS / "scenario.toml").read_text()
assert "no_smt = true" not in config
(judge / "scenario.toml").write_text(config.replace("probe_query_timings = true", "probe_query_timings = false"))
argv = ["timeout", "--foreground", "1800s", LOADER, "--library-path", Z3, str(BINARY),
        "-A", str(IR), "-C", "scenario.toml", "-T", "1", "--tastic", "default", "--timeout", "120s",
        "--path-cache-read", str((directory / summary["manifest_path"]).parent),
        "--path-cache-encoding", "bin", "--check-samples", "input.jsonl", "--check-samples-report", "report.json",
        "--check-samples-judge", "judged.jsonl", "solve-state", f"--clause={clause}"]
(judge / "argv.txt").write_text(shlex.join(argv) + "\n")
resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024 * 1024, resource.getrlimit(resource.RLIMIT_STACK)[1]))
started = time.monotonic()
with (judge / "raw.log").open("wb") as log:
    run_long.SUPERVISOR_PID = os.getpid()
    with subprocess.Popen(argv[3:], cwd=judge, stdout=log, stderr=log,
                          preexec_fn=run_long.set_parent_death_signal) as child:
        try:
            returncode = child.wait(timeout=1800)
        except subprocess.TimeoutExpired:
            child.terminate()
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
            returncode = 124
details = {"returncode": returncode, "wall_seconds": round(time.monotonic() - started, 3), "pass": False}
report_path = judge / "report.json"
if report_path.is_file():
    report = json.loads(report_path.read_text())
    details["report"] = report
    judged_path = judge / "judged.jsonl"
    rows = [json.loads(line) for line in judged_path.read_text().splitlines()] if judged_path.is_file() else []
    if len(rows) == 1:
        observed = rows[0]
        fields = ("terminal", "pre_registers", "post_registers", "isa_state", "pre_memory", "post_memory", "result")
        details["field_comparison"] = {key: observed["sample"][key] == sample[key] for key in fields}
        details["ret_val_display_equal"] = observed["sample"]["ret_val"] == sample["ret_val"]
        for field in ("guard_unique", "post_unique"):
            details[field] = observed[field]
        details["pass"] = returncode == 0 and report["sample_total"] == 1 and all(
            row["accepted_paths"] == row["consistent_paths"] == 1 and row["inconsistent_paths"] == 0
            for row in report["samples"]
        ) and observed["guard_unique"] and observed["post_unique"] and all(details["field_comparison"].values())
(judge / "summary.json").write_text(json.dumps(details, ensure_ascii=False, indent=2) + "\n")
raise SystemExit(0 if details["pass"] else 1)
