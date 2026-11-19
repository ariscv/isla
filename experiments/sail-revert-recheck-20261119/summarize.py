#!/usr/bin/env python3
"""汇总最后一个完整的区域诊断快照。"""

import collections
import json
from pathlib import Path
import re
import sys


MERGE_KINDS = {
    "merge_value_summary", "merge_value_summary_key", "merge_timing_summary",
    "merge_timing_site", "merge_inflight", "filtered_model_exception_summary",
    "filtered_match_failure_summary",
}
FAILURE = re.compile(
    r"symbolic (?:\(bit\)vector )?length|消费者需要拆分具体候选值|symbolic (?:start|end|width)|cannot.*(?:concrete|symbolic)|"
    r"requires? (?:a )?concrete|needs? (?:a )?concrete|No possible value|"
    r"NoSmt|panicked at|Failed to|error with task|Execution failed", re.IGNORECASE,
)


def site(origin):
    return f"{origin['function']}@{origin['pc']}"


def summarize(directory):
    snapshots = collections.defaultdict(lambda: collections.defaultdict(list))
    finite_domain = []
    errors = collections.Counter()
    final_memory = {}
    no_smt_sites = []
    for line in (directory / "raw.log").open(errors="replace"):
        if line.startswith("[MEMORY_STATS] "):
            try:
                final_memory = json.loads(line.split(" ", 1)[1])
            except json.JSONDecodeError:
                continue
        elif line.startswith("{"):
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            kind = row.get("kind")
            if kind in MERGE_KINDS:
                snapshots[row["snapshot"]][kind].append(row)
            elif kind == "symbolic_value_enumeration_summary":
                finite_domain.append(row)
            elif kind == "no_smt_summary":
                no_smt_sites = row["sites"]
        elif FAILURE.search(line):
            errors[line.strip()] += 1

    measure = dict(line.split("=", 1) for line in (directory / "measure.txt").read_text().splitlines() if "=" in line)
    result = {"measure": measure, "exit": int((directory / "exit.txt").read_text()), "errors": dict(errors)}
    completed = [index for index, rows in snapshots.items() if rows["merge_value_summary"]]
    if not completed:
        return result
    snapshot = max(completed)
    rows = snapshots[snapshot]
    timing = rows["merge_timing_summary"][0]
    values = rows["merge_value_summary"][0]
    totals = {
        row["outcome"]: {
            "all": row["inclusive"]["count"],
            "root": row["root"]["count"],
        }
        for row in timing["outcomes"]
    }
    sites = rows["merge_timing_site"]
    inflight = rows["merge_inflight"]
    translation = {}
    for name in ("translateAddr@13", "translateAddrWithPBMT@13"):
        at_site = [row for row in sites if site(row["key"]["origin"]) == name]
        translation[name] = {
            "finished": sum(row["inclusive"]["count"] for row in at_site),
            "root_finished": sum(row["root"]["count"] for row in at_site),
            "success": sum(row["inclusive"]["count"] for row in at_site if row["key"]["outcome"] == "success"),
            "in_flight": sum(site(row["origin"]) == name for row in inflight),
            "rows": at_site,
        }
    result.update(
        translation=translation,
        snapshot=snapshot, trigger=timing["trigger"], started=timing["started"], finished=timing["finished"],
        in_flight=timing["in_flight"], roots_in_flight=sum(row["parent_attempt"] is None for row in inflight),
        root_success=totals.get("success", {}).get("root", 0), outcomes=totals,
        native_checks=timing["all_smt"]["queries"]["sum"],
        value_differences=values["differences"], concrete_values=values["concrete_values"],
        value_sites=rows["merge_value_summary_key"],
        rejection_sites=[
            {"origin": site(row["key"]["origin"]), "outcome": row["key"]["outcome"],
             "all": row["inclusive"]["count"], "root": row["root"]["count"]}
            for row in sites if row["key"]["outcome"] != "success"
        ],
        root_success_sites={
            site(row["key"]["origin"]): row["root"]
            for row in sites if row["key"]["outcome"] == "success" and row["root"]["count"]
        },
        memory={key: final_memory.get(key) for key in ("elapsed_seconds", "active_tasks", "queue", "process")},
        inflight_attempts=inflight,
        last_finite_domain=finite_domain[-1] if finite_domain else None,
        finite_domain_uses=[
            row for row in no_smt_sites
            if row["category"].startswith("finite_domain_") and row["category"] != "finite_domain_dead_condition"
        ],
    )
    return result


for argument in sys.argv[1:]:
    directory = Path(argument)
    summary = summarize(directory)
    (directory / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")
    keys = ("exit", "measure", "root_success", "in_flight", "outcomes", "value_differences", "native_checks")
    compact = {key: summary.get(key) for key in keys}
    compact["translation"] = {
        name: {key: value for key, value in counts.items() if key != "rows"}
        for name, counts in summary.get("translation", {}).items()
    }
    print(directory.name, json.dumps(compact, ensure_ascii=False))
