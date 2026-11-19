#!/usr/bin/env python3
"""核对本轮退出及产物，汇总原生和内置计数差。"""
from pathlib import Path
from datetime import datetime
import csv
import json
import subprocess

artifacts = Path(__file__).resolve().parent
with (artifacts / "progress.tsv").open() as stream:
    rows = list(csv.DictReader(stream, delimiter="\t"))
known = {int((artifacts / clause / "pid.txt").read_text()) for clause in ("load", "store")}
processes = subprocess.check_output(["ps", "-eo", "pid,ppid,pgid,stat,args"], text=True).splitlines()[1:]
for row in processes:
    pid, _, pgid, _, command = row.split(None, 4)
    argv = command.split()
    assert int(pid) not in known and int(pgid) not in known, row
    assert not any(word == str(artifacts / "run-long.py") for word in argv[:3]), row
lines = [datetime.now().astimezone().isoformat(), f"进程组 {sorted(known)}，存活成员 0"]
for clause in ("LOAD", "STORE"):
    directory = artifacts / clause.lower()
    run = json.loads((directory / "summary.json").read_text())
    checkpoints = [row for row in rows if row["clause"] == clause]
    assert checkpoints[0]["event"] == "start" and checkpoints[-1]["event"] == "exit_last_live_rss"
    assert [round(float(row["elapsed_s"])) for row in checkpoints[1:-1]] == list(
        range(900, round(float(checkpoints[-2]["elapsed_s"])) + 1, 900)
    )
    if run["stop"] == "program_limit":
        assert round(float(checkpoints[-2]["elapsed_s"])) == 7200, checkpoints[-2]
    manifest_count = sum(1 for _ in directory.rglob("manifest.json"))
    judged = directory / "judge/summary.json"
    if run["complete"]:
        assert manifest_count and judged.exists()
    lines.append(f"{clause} 退出 {run['returncode']}，manifest {manifest_count}，judge 摘要 {int(judged.exists())}")
    native = [row for row in checkpoints[1:] if row["z3_native_checks"] != "NA"]
    if native:
        differences = [int(r["z3_checks"]) - int(r["z3_native_checks"]) for r in native]
        lines.append(f"{clause} 内置与独立已返回 check 计数差范围 {min(differences)} 至 {max(differences)}，末次 {differences[-1]}")
(artifacts / "exit-audit.txt").write_text("\n".join(lines) + "\n")
print("\n".join(lines))
