#!/usr/bin/env python3
"""汇总实测检查点和末次证据。"""
from collections import Counter
import csv
import json
from pathlib import Path
import re
import shlex

artifacts = Path(__file__).resolve().parent
worktrees = artifacts.parents[1]
previous = worktrees / "isla-nosmt-long3-20261119" / "artifacts"
first_smt = worktrees / "isla-smt-long-20261119" / "artifacts"
ir = artifacts / "rv64d.ir"

with ir.open() as stream:
    sources = next(shlex.split(line)[1:] for line in stream if line.startswith("files "))


def source_position(file, line, col):
    if not 0 <= file < len(sources):
        return f"IR file {file}:{line}:{col}"
    name = sources[file]
    if "/model/" in name:
        name = name.split("/model/", 1)[1]
    elif "/share/sail/lib/" in name:
        name = name.split("/share/sail/lib/", 1)[1]
    return f"{name}:{line}:{col}"


def rows(directory, clause, head):
    with (directory / "progress.tsv").open() as stream:
        return [row for row in csv.DictReader(stream, delimiter="\t")
                if row["clause"] == clause and row["isla_head"] == head]


def format_rss(value):
    return f"{int(value) / 1024**2:.2f}" if value != "NA" else "—"


def checkpoint(row):
    if not row:
        return "—"
    return f'{row["normal_terminals"] if "normal_terminals" in row else row["terminal_candidates"]}／{row["queued"]}／{format_rss(row["rss_kib"])}'

def solver_checkpoint(row):
    if not row:
        return "—"
    def rejected(scope):
        value = row[scope]
        if value == "NA":
            return "—／—"
        counts = json.loads(value)
        return f'{counts.get("solver_unknown", 0)}／{counts.get("timeout", 0)}'
    return f'{rejected("root_rejections")} · {rejected("all_rejections")} · {row["z3_check_timeouts_observed"]}'


def rejection_sites(run):
    for row in run["rejection_site_rows"]:
        origin = row["key"]["origin"]
        site = f'{origin["function"]}@{origin["pc"]}'
        yield (row["key"]["outcome"], site), (row["root"]["count"], row["inclusive"]["count"])


def print_site_comparison(current, baseline):
    present = dict(rejection_sites(current))
    previous = dict(rejection_sites(baseline))
    print("| 区域标签 | 站点 | 本轮根／含嵌套 | SMT 首轮根／含嵌套 |")
    print("| --- | --- | ---: | ---: |")
    for label in ("solver_unknown", "timeout", "smt_error"):
        common = sorted({site for outcome, site in present.keys() | previous.keys() if outcome == label})
        current_top = sorted(common, key=lambda site: -present.get((label, site), (0, 0))[1])[:10]
        previous_top = sorted(common, key=lambda site: -previous.get((label, site), (0, 0))[1])[:10]
        tracked = ["phys_access_check@5", "phys_access_check@9", "phys_access_check@15", "pmaCheck@3", "translationMode@56"]
        selected = dict.fromkeys((tracked if label == "solver_unknown" else []) + current_top + previous_top)
        for site in selected:
            key = label, site
            current_counts = "／".join(map(str, present.get(key, (0, 0))))
            baseline_counts = "／".join(map(str, previous.get(key, (0, 0))))
            print(f"| {label} | `{site}` | {current_counts} | {baseline_counts} |")


def log_evidence(path, resolve_sources=True):
    result = {"enum": None, "slow_checks": [], "solver_drops": [], "error_samples": [], "smt_reject_causes": {},
              "deferred_queries": [], "root_concretization": {}, "probe_exit_checks": {},
              "first_deferred_query": None, "probe_caps": {}, "first_invalid_enum_count": None,
              "concrete_candidates": {}, "path_timeout_sites": {}, "path_timeout_first_lines": {},
              "execution_errors": {}, "error_terminals": {}, "oom_lines": [], "cache_stage_lines": []}
    causes = Counter()
    query_scopes = Counter()
    query_scope_seconds = 0
    exit_checks = Counter()
    path_timeout_sites = Counter()
    execution_errors = Counter()
    slow = []
    with path.open("rb") as stream:
        for number, line in enumerate(stream, 1):
            def payload():
                return json.loads(line[line.index(b"{"):])

            if b'"kind":"symbolic_value_enumeration_summary"' in line:
                result["enum"] = payload()
                if result["enum"]["solver_checks"] > 2**63 and result["first_invalid_enum_count"] is None:
                    result["first_invalid_enum_count"] = {"line_in_log": number, **result["enum"]}
            elif b'"kind":"region_deferred_query_summary"' in line:
                result["deferred_queries"] = payload()["queries"]
            elif b'"kind":"merge_value_summary"' in line:
                result["concrete_candidates"] = payload().get("concrete_values", {})
            elif line.startswith(b'{"kind":"region_deferred_exit"'):
                if result["first_deferred_query"] is None:
                    result["first_deferred_query"] = {"line_in_log": number, **payload()}
            elif line.startswith(b'{"kind":"probe_query_event"'):
                event = payload()["event"]
                if event["type"] == "exit_check_end":
                    exit_checks[str(event["result"]).split(" {", 1)[0]] += 1
                elif event["type"] == "truncated":
                    result["probe_caps"][event["bucket"]] = number
                elif event["type"] == "check":
                    thresholds = result.setdefault("slow_check_thresholds", {60: 0, 300: 0, 600: 0, 900: 0})
                    for threshold in thresholds:
                        thresholds[threshold] += int(event["seconds"] >= threshold)
            elif b'SLOW_SMT {"' in line:
                event = payload()
                if event["operation"] in ("CheckSat", "CheckSatAssuming"):
                    source = event["source_loc"]
                    event["line_in_log"] = number
                    if resolve_sources:
                        event["location"] = source_position(source["file"], source["line1"], source["char1"])
                    slow.append(event)
            elif line.startswith(b"[REGION_SMT_REJECT] "):
                message = payload()["error"]
                cause = re.split(r" (?:at |after )|，位置", message, maxsplit=1)[0]
                result["smt_reject_causes"].setdefault(cause, {"first_line": number})
                causes[cause] += 1
            elif line.startswith(b"[SOLVER_PATH_DROP] "):
                result["solver_drops"].append({"line_in_log": number, **payload()})
            elif line.startswith(b"[PATH_CACHE_TERMINAL] ") and b" terminal=execution_error " in line:
                description = line.split(b" terminal=execution_error ", 1)[1].decode(errors="replace").strip()
                entry = result["error_terminals"].setdefault(description, {"first_line": number, "count": 0})
                entry["count"] += 1
            elif line.startswith(b'{"kind":"region_progress"'):
                scope = payload().get("query_phases", {}).get("concretization", {})
                query_scopes["regions"] += int(bool(scope))
                query_scopes["checks"] += scope.get("queries", 0)
                query_scope_seconds += scope.get("smt_seconds", 0)
            elif ("执行错误:".encode() in line or b"panicked at" in line or
                  line.startswith("错误:".encode()) or b"terminal=execution_error" in line):
                if "执行错误:".encode() in line:
                    message = line.decode(errors="replace").strip().split("执行错误:", 1)[1].strip()
                    execution_errors[message] += 1
                if len(result["error_samples"]) < 15:
                    result["error_samples"].append([number, line.decode(errors="replace").strip()[:600]])
            elif "路径超时:".encode() in line:
                site = line.decode(errors="replace").strip().rsplit("停在 ", 1)[-1]
                path_timeout_sites[site] += 1
                result["path_timeout_first_lines"].setdefault(site, number)
            elif b"memory allocation of" in line or b"out of memory" in line.lower():
                result["oom_lines"].append([number, line.decode(errors="replace").strip()[:600]])
            elif line.startswith((b"[PATH_CACHE_WRITE]", b"[ISARCH_STAGE]")):
                result["cache_stage_lines"].append([number, line.decode(errors="replace").strip()[:600]])
    result["slow_checks"] = sorted(slow, key=lambda row: row["wall_seconds"], reverse=True)[:10]
    for cause, count in causes.items():
        result["smt_reject_causes"][cause]["count"] = count
    result["root_concretization"] = dict(query_scopes, seconds=query_scope_seconds)
    result["probe_exit_checks"] = dict(exit_checks)
    result["path_timeout_sites"] = dict(path_timeout_sites.most_common())
    result["execution_errors"] = dict(execution_errors.most_common())
    return result


latest_head = (artifacts / "isla-version.txt").read_text().strip()[:8]
report = {}
for clause in ("LOAD", "STORE"):
    recent = rows(artifacts, clause, latest_head)
    old = rows(previous, clause, "4e0ad168")
    first = rows(first_smt, clause, "92945c96")
    old_checkpoints = {round(float(row["elapsed_s"]) / 900): row for row in old if row["event"] == "15min"}
    latest_checkpoints = {round(float(row["elapsed_s"]) / 900): row
                          for row in recent if row["event"] == "15min"}
    first_checkpoints = {round(float(row["elapsed_s"]) / 900): row
                         for row in first if row["event"] == "15min"}
    if clause == "STORE":
        print()
    print(f"### {clause}")
    print()
    print("求解栏依次为根区域 unknown／timeout、含嵌套区域 unknown／timeout、原生 Z3 check 超时。")
    print()
    print("| 分钟 | 本轮正常终态／队列／RSS GiB | 带 SMT 首轮终态／队列／RSS GiB | 无 SMT 第三轮终态／队列／RSS GiB | 本轮／首轮共享 load1 | 本轮求解栏 | 首轮求解栏 |")
    print("| ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for number in sorted(latest_checkpoints.keys() | old_checkpoints.keys() | first_checkpoints.keys()):
        current = latest_checkpoints.get(number)
        first_row = first_checkpoints.get(number)
        print(f"| {number * 15} | {checkpoint(current)} | {checkpoint(first_row)} "
              f"| {checkpoint(old_checkpoints.get(number))} "
              f'| {current["load1"] if current else "—"}／{first_row["load1"] if first_row else "—"} '
              f"| {solver_checkpoint(current)} | {solver_checkpoint(first_row)} |")
    print()
    run = json.loads((artifacts / clause.lower() / "summary.json").read_text())
    first_run = json.loads((first_smt / clause.lower() / "summary.json").read_text())
    print_site_comparison(run, first_run)
    detail = log_evidence(artifacts / clause.lower() / "raw.log")
    baseline = log_evidence(previous / clause.lower() / "raw.log", resolve_sources=False)
    z3_positions = []
    for row in run["z3_check_positions"][:20]:
        z3_positions.append({"location": source_position(row["file"], row["line"], row["column"]), **row})
    report[clause] = {"run_log": detail, "nosmt_long3_enum": baseline["enum"], "z3_positions": z3_positions,
                      "exit_progress": recent[-1], "nosmt_long3_exit": old[-1]}

(artifacts / "log-evidence.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
