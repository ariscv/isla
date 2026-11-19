#!/usr/bin/env python3
"""并行运行两条指令，记录进度并回收本实验的进程组。"""
import collections
from contextlib import ExitStack
import ctypes
import csv
import json
import os
from pathlib import Path
import re
import resource
import shlex
import signal
import statistics
import subprocess
import time

ARTIFACTS = Path(__file__).resolve().parent
WORKTREE = ARTIFACTS.parent
ROOT = WORKTREE.parents[1]
BINARY = WORKTREE / "target/release/isarch"
IR = ARTIFACTS / "rv64d.ir"
Z3 = str(Path.home() / ".local/opt/z3-official-d6c9b4fbb/lib")
LOADER = "/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"
PROGRAM_LIMIT = 7200
OUTER_LIMIT = 7800
PATH_LIMIT = 1200
INTERVAL = 900
STALL_LIMIT = 1800
MIN_AVAILABLE_KIB = 16 * 1024**2
HEAD = (ARTIFACTS / "isla-version.txt").read_text().strip()[:8]
FIELDS = ("time", "clause", "event", "elapsed_s", "rss_kib", "root_success", "regions_in_flight",
          "regions_finished", "terminal_candidates", "queued", "active", "region_snapshot_age_s",
          "region_snapshot_trigger", "uncertified_terminals", "resident_paths", "root_rejections",
          "all_rejections", "isla_head", "load1", "host_available_kib", "checked_terminals",
          "normal_terminals", "rejection_top10_by_label", "z3_checks", "z3_seconds", "z3_p50_seconds",
          "z3_p95_seconds", "z3_max_seconds", "z3_sample_count", "z3_check_timeouts_observed",
          "z3_model_eval_timeouts_observed", "z3_trace_capped", "model_eval_calls", "enum_calls",
          "enum_completed", "enum_z3_checks", "enum_structural_candidates", "enum_model_candidates",
          "enum_z3_seconds", "smt_error_causes", "solver_active_samples", "solver_container_bytes",
          "z3_live_contexts", "z3_estimated_alloc_bytes", "queue_snapshot_age_s",
          "z3_native_snapshot_age_s", "z3_native_pending_checks", "z3_native_checks", "z3_stack_depth_limit_checks",
          "enum_z3_checks_observed", "enum_z3_seconds_observed", "candidate_z3_checks_observed",
          "candidate_z3_seconds_observed", "enum_candidate_overlap_checks", "enum_candidate_overlap_seconds",
          "solver_path_drops", "path_timeout_log_lines", "execution_error_log_lines", "panic_log_lines",
          "execution_error_terminals", "sail_exception_terminals")

def timestamp():
    return time.strftime("%Y-%m-%dT%H:%M:%S%z")

def host_snapshot():
    load1 = Path("/proc/loadavg").read_text().split()[0]
    available = next(int(line.split()[1]) for line in Path("/proc/meminfo").read_text().splitlines()
                     if line.startswith("MemAvailable:"))
    return load1, available

def compact(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))

def native_metrics(path):
    # 独立输出，小行一次写入。异常终止可能留下最后一行不全。
    try:
        with path.open("rb") as stream:
            stream.seek(max(0, path.stat().st_size - 1024))
            lines = stream.read().split(b"\n")
    except FileNotFoundError:
        return {}
    for line in reversed(lines[:-1]):
        values = line.split(b"\t")
        if len(values) == 13:
            at, contexts, memory, pending, shallow, other, _, enums, enum_ns, candidates, candidate_ns, both, both_ns = map(int, values)
            return {
                "z3_live_contexts": contexts, "z3_estimated_alloc_bytes": memory,
                "z3_native_snapshot_age_s": max(0, time.monotonic_ns() - at) / 1e9,
                "z3_native_pending_checks": pending, "z3_native_checks": other + enums + candidates + both,
                "z3_stack_depth_limit_checks": shallow,
                "enum_z3_checks_observed": enums + both, "enum_z3_seconds_observed": (enum_ns + both_ns) / 1e9,
                "candidate_z3_checks_observed": candidates + both,
                "candidate_z3_seconds_observed": (candidate_ns + both_ns) / 1e9,
                "enum_candidate_overlap_checks": both, "enum_candidate_overlap_seconds": both_ns / 1e9,
            }
    return {}

class Observation:
    def __init__(self):
        self.timing = {}
        self.memory = {}
        self.terminals = collections.Counter()
        self.errors = collections.Counter()
        self.pending = b""
        self.stages = 0
        self.updated = None
        self.site_snapshot = None
        self.pending_sites = []
        self.sites = []
        self.inflight = []
        self.pending_inflight = []
        self.enumeration = {}
        self.checks = []
        self.check_times_by_position = collections.defaultdict(lambda: [0, 0.0, 0])
        self.trace_capped = False
        self.timeouts_by_operation = collections.Counter()
        self.check_timeouts = 0
        self.smt_errors = collections.Counter()
        self.solver_drops = collections.Counter()
        self.memory_updated = None

    def read(self, reader, now):
        while chunk := reader.read(1024 * 1024):
            lines = (self.pending + chunk).split(b"\n")
            self.pending = lines.pop()
            for raw in lines:
                self.read_line(raw, now)

    def read_line(self, raw, now):
        self.read_diagnostic(raw, now)

    def read_diagnostic(self, raw, now):
        try:
            if raw.startswith(b'{"kind":"probe_query_event"'):
                event = json.loads(raw)["event"]
                if event["type"] == "check":
                    seconds = event["seconds"]
                    self.checks.append(seconds)
                    self.check_timeouts += int(event["timed_out"])
                    source = event["source"]
                    site = (source["file"], source["line1"], source["char1"])
                    stat = self.check_times_by_position[site]
                    stat[0] += 1
                    stat[1] += seconds
                    stat[2] = max(stat[2], seconds)
                elif event["type"] == "truncated" and event["bucket"] == 0:
                    self.trace_capped = True
            elif raw.startswith(b'[PATH_CACHE_TERMINAL]'):
                match = re.search(rb'\bterminal=(\S+) certification=(\S+)', raw)
                if match:
                    self.terminals[match[1].decode(), match[2].decode()] += 1
            elif b'"kind":"merge_timing_site"' in raw:
                row = json.loads(raw[raw.index(b"{"):])
                if row["snapshot"] != self.site_snapshot:
                    self.site_snapshot = row["snapshot"]
                    self.pending_sites = []
                    self.pending_inflight = []
                if row["key"]["outcome"] != "success":
                    self.pending_sites.append(row)
            elif b'"kind":"merge_inflight"' in raw:
                row = json.loads(raw[raw.index(b"{"):])
                if row["snapshot"] != self.site_snapshot:
                    self.site_snapshot = row["snapshot"]
                    self.pending_sites = []
                    self.pending_inflight = []
                self.pending_inflight.append(row)
            elif b'"kind":"merge_timing_summary"' in raw:
                self.timing = json.loads(raw[raw.index(b"{"):])
                self.updated = now
                self.sites = self.pending_sites if self.timing["snapshot"] == self.site_snapshot else []
                self.inflight = self.pending_inflight if self.timing["snapshot"] == self.site_snapshot else []
            elif b'"kind":"symbolic_value_enumeration_summary"' in raw:
                self.enumeration = json.loads(raw[raw.index(b"{"):])
            elif raw.startswith(b"[MEMORY_STATS] "):
                self.memory = json.loads(raw.removeprefix(b"[MEMORY_STATS] "))
                self.memory_updated = now
            elif raw.startswith(b"[REGION_SMT_REJECT] "):
                row = json.loads(raw.removeprefix(b"[REGION_SMT_REJECT] "))
                cause = re.split(r" (?:at |after )|，位置", row["error"], maxsplit=1)[0]
                self.smt_errors[cause] += 1
            elif raw.startswith(b"[SOLVER_PATH_DROP] "):
                row = json.loads(raw.removeprefix(b"[SOLVER_PATH_DROP] "))
                self.solver_drops[row["reason"]] += 1
            elif b"SLOW_SMT " in raw:
                row = json.loads(raw.split(b"SLOW_SMT ", 1)[1])
                if row["timed_out"]:
                    self.timeouts_by_operation[row["operation"]] += 1
            elif raw.startswith((b"[PATH_CACHE_WRITE]", b"[ISARCH_STAGE]")):
                self.stages += 1
            elif b"panicked at" in raw or b"fatal runtime error" in raw:
                self.errors["panic"] += 1
            elif "执行错误:".encode() in raw:
                self.errors["execution_error_log_lines"] += 1
            elif raw.startswith("错误:".encode()):
                self.errors["error_log_lines"] += 1
            if "路径超时:".encode() in raw:
                self.errors["path_timeout_log_lines"] += 1
        except (ValueError, KeyError, IndexError):
            self.errors["unparsed_diagnostic_lines"] += 1

    def outcomes(self, scope):
        return {
            row["outcome"]: row[scope]["count"]
            for row in self.timing.get("outcomes", []) if row[scope]["count"]
        }

    def top_rejections(self):
        groups = collections.defaultdict(list)
        for row in self.sites:
            key = row["key"]
            groups[key["outcome"]].append(row)
        return {
            reason: [
                {"site": row["key"], "count": row["inclusive"]["count"]}
                for row in sorted(rows, key=lambda row: -row["inclusive"]["count"])[:10]
            ]
            for reason, rows in groups.items()
        }

    def smt_metrics(self):
        all_smt = self.timing.get("all_smt", {})
        durations = sorted(self.checks)
        exact = not self.trace_capped
        checks = all_smt.get("queries", {}).get("sum")
        if exact and (checks is None or len(durations) >= checks):
            checks, total = len(durations), sum(durations)
            maximum = durations[-1] if durations else None
        else:
            total = all_smt.get("smt_seconds", {}).get("sum")
            maximum = all_smt.get("smt_seconds", {}).get("max") if checks else None
        return {
            "z3_checks": checks,
            "z3_seconds": total,
            "z3_p50_seconds": statistics.median(durations) if exact and durations else None,
            "z3_p95_seconds": durations[(len(durations) * 95 + 99) // 100 - 1] if exact and durations else None,
            "z3_max_seconds": maximum,
            "z3_sample_count": len(durations),
            "z3_check_timeouts_observed": max(self.check_timeouts,
                sum(self.timeouts_by_operation[op] for op in ("CheckSat", "CheckSatAssuming"))),
            "z3_model_eval_timeouts_observed": self.timeouts_by_operation["ModelEval"],
            "z3_trace_capped": self.trace_capped,
            "model_eval_calls": all_smt.get("model_calls", {}).get("sum"),
            **{f"enum_{field}": self.enumeration.get(key) for field, key in
               (("calls", "calls"), ("completed", "completed"), ("z3_checks", "solver_checks"),
                ("structural_candidates", "structural_candidates"), ("model_candidates", "model_candidates"))},
            "enum_z3_seconds": 0 if self.enumeration.get("solver_checks") == 0 else None,
            "smt_error_causes": compact(self.smt_errors),
            "solver_active_samples": self.memory.get("sampled_active_tasks"),
            "solver_container_bytes": self.memory.get("active_solver_container_bytes"),
        }

    def sample(self, clause, event, elapsed, now, rss, stream, native):
        queue = self.memory.get("queue") or {}
        load1, available = host_snapshot()
        rejections = [
            json.dumps({key: count for key, count in self.outcomes(scope).items() if key != "success"},
                       sort_keys=True, separators=(",", ":")) if self.timing else None
            for scope in ("root", "inclusive")
        ]
        fields = [
            timestamp(), clause, event, f"{elapsed:.2f}", rss,
            self.outcomes("root").get("success", 0) if self.timing else None,
            self.timing.get("in_flight"),
            self.timing.get("finished"),
            sum(self.terminals.values()),
            queue.get("tasks"),
            self.memory.get("active_tasks"),
            f"{now - self.updated:.2f}" if self.updated is not None else None,
            self.timing.get("trigger"),
            sum(count for (_, cert), count in self.terminals.items() if cert == "uncertified"),
            self.memory.get("resident_paths"),
            *rejections,
            HEAD,
            load1, available,
            sum(count for (_, cert), count in self.terminals.items() if cert == "checked"),
            sum(count for (name, _), count in self.terminals.items() if name == "normal"),
            compact(self.top_rejections()),
            *self.smt_metrics().values(),
            native.get("z3_live_contexts"),
            native.get("z3_estimated_alloc_bytes"),
            f'{queue["age_seconds"] + now - self.memory_updated:.2f}' if queue and self.memory_updated else None,
            *(native.get(name) for name in FIELDS[FIELDS.index("z3_native_snapshot_age_s"):
                                                  FIELDS.index("solver_path_drops")]),
            compact(self.solver_drops),
            *(self.errors[name] for name in ("path_timeout_log_lines", "execution_error_log_lines", "panic")),
            *(sum(count for (name, _), count in self.terminals.items() if name == terminal)
              for terminal in ("execution_error", "sail_exception")),
        ]
        assert len(fields) == len(FIELDS)
        row = "\t".join("NA" if item is None else str(item) for item in fields)
        print(row, file=stream, flush=True)
        print(f"{clause} {event} {elapsed:.2f}s RSS={rss}KiB load1={load1} "
              f"roots={fields[5]} queued={fields[9]} terminal={fields[8]} checked={fields[20]}",
              flush=True)

def proc_rss(pid):
    try:
        status = Path(f"/proc/{pid}/status").read_text()
    except (FileNotFoundError, ProcessLookupError):
        return None
    match = re.search(r"^VmRSS:\s+(\d+) kB", status, re.MULTILINE)
    return int(match[1]) if match else None

def collect(child):
    pid, status, usage = os.wait4(child.pid, os.WNOHANG)
    if not pid:
        return None
    child.returncode = os.waitstatus_to_exitcode(status)
    return usage

def send(child, sig):
    try:
        os.killpg(child.pid, sig)
    except ProcessLookupError:
        pass

def audit_host():
    fields = "pid,ppid,pgid,nlwp,pcpu,rss,etimes,comm,args"
    processes = subprocess.check_output(["ps", "-eo", fields, "--sort=-pcpu"], text=True)
    rows = [processes.splitlines()[0]]
    competing = []
    for line in processes.splitlines()[1:]:
        fields = line.split(None, 8)
        if len(fields) != 9:
            continue
        _, _, _, _, cpu, rss, _, command, args = fields
        if (float(cpu) >= 300 or int(rss) >= 4 * 1024**2 or
                re.search(r"/isarch(?:[-_a-zA-Z0-9]*)?(?: |$)", args)):
            rows.append(" ".join(fields[:8]) + " " + args.split(" -A ", 1)[0][:240])
        is_symbolic_runner = command.startswith("isarch") or command.startswith("ld-linux")
        high_parallelism = re.search(r"(?:^| )-T\s+(?:[2-9][0-9]|1[6-9]|[0-9]{3,})(?: |$)", args)
        if (is_symbolic_runner and re.search(r"(?:^|/)isarch(?:[-_a-zA-Z0-9]*)?(?: |$)", args)
                and (high_parallelism or float(cpu) >= 800 or int(rss) >= 8 * 1024**2)):
            competing.append(fields[0])
    audit = ARTIFACTS / "preflight.txt"
    available = next(line for line in Path("/proc/meminfo").read_text().splitlines()
                     if line.startswith("MemAvailable:"))
    audit.write_text(f"{timestamp()} {os.uname().nodename} CPU={len(os.sched_getaffinity(0))} {available}\n"
                     + "\n".join(rows) + f"\ncompeting_heavy_symbolic_pids={','.join(competing)}\n")

def set_parent_death_signal():
    # 监控器意外退出时，内核直接终止这批运行的子进程。
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "设置父进程退出信号失败")
    if os.getppid() != SUPERVISOR_PID:
        os._exit(125)

class Run:
    def __init__(self, clause, files):
        self.clause = clause
        self.directory = ARTIFACTS / clause.lower()
        self.directory.mkdir()
        self.native_path = self.directory / "z3-observer.tsv"
        args = [LOADER, "--library-path", Z3, str(BINARY), "-A", str(IR),
                "-C", str(ARTIFACTS / "scenario.toml"), "-T", "32", "--tastic", "default",
                "--path-merging", "--verbose", "-D", "s", "--merge-diagnostics", "detail",
                "--memory-stats", "--path-cache-only", "--path-cache-write", f"cache/{clause}",
                "--path-cache-format", "both", "solve-state", f"--clause={clause}",
                "--timeout", f"{PATH_LIMIT}s"]
        extras = {"ISLA_STATS": "1", "ISARCH_OBSERVER_PATH": str(self.native_path),
                  "LD_PRELOAD": str(ARTIFACTS / "observe-z3.so")}
        (self.directory / "argv.txt").write_text(shlex.join(["env", *(f"{key}={value}" for key, value in extras.items()), *args]) + "\n")
        self.observation = Observation()
        self.stop = None
        self.sent_kill = False
        self.last_rss = None
        self.rss_at_progress = None
        self.region_mark = (0, 0, 0, 0)
        raw = self.directory / "raw.log"
        log = files.enter_context(raw.open("wb"))
        self.reader = files.enter_context(raw.open("rb"))
        self.started_at = timestamp()
        self.last_progress = self.start = time.monotonic()
        self.checkpoint = self.start + INTERVAL
        env = dict(os.environ, **extras)
        self.child = subprocess.Popen(args, cwd=self.directory, stdout=log, stderr=log, process_group=0,
                                      preexec_fn=set_parent_death_signal, env=env)
        try:
            (self.directory / "pid.txt").write_text(str(self.child.pid) + "\n")
        except BaseException:
            self.close()
            raise

    def close(self):
        if self.child.returncode is None:
            send(self.child, signal.SIGKILL)
            self.child.wait()

    def poll(self, progress, memory_pressure):
        now = time.monotonic()
        observation = self.observation
        observation.read(self.reader, now)
        usage = collect(self.child)
        if usage is not None:
            observation.read(self.reader, now)
            self.summarize(now, progress, usage)
            return False
        rss = proc_rss(self.child.pid)
        if rss is not None:
            self.last_rss = rss
        mark = (observation.timing.get("finished", 0), sum(observation.terminals.values()),
                observation.stages, observation.memory.get("resident_paths", 0))
        mark += (len(observation.checks), observation.timing.get("all_smt", {}).get("queries", {}).get("sum"),
                 tuple(sorted((row["attempt"], row["steps"]) for row in observation.inflight)))
        if mark != self.region_mark:
            self.last_progress = now
            self.region_mark = mark
            self.rss_at_progress = self.last_rss
        elif rss is not None:
            if self.rss_at_progress is None or rss > self.rss_at_progress:
                self.last_progress = now
                self.rss_at_progress = rss
        elapsed = now - self.start
        if now >= self.checkpoint:
            observation.sample(self.clause, "15min", elapsed, now, rss, progress, native_metrics(self.native_path))
            self.checkpoint += INTERVAL
        if self.stop is None:
            if elapsed >= PROGRAM_LIMIT:
                self.stop = "program_limit"
            elif memory_pressure:
                self.stop = "host_memavailable_below_16_gib"
            elif now - self.last_progress >= STALL_LIMIT:
                self.stop = "no_progress_or_rss_growth_30min"
            if self.stop is not None:
                self.stop_at = now
                send(self.child, signal.SIGTERM)
        if not self.sent_kill and (elapsed >= OUTER_LIMIT or
                                  self.stop in ("no_progress_or_rss_growth_30min", "host_memavailable_below_16_gib")
                                  and now - self.stop_at >= 30):
            self.sent_kill = True
            send(self.child, signal.SIGKILL)
        return True

    def summarize(self, now, progress, usage):
        observation = self.observation
        native = native_metrics(self.native_path)
        observation.sample(self.clause, "exit_last_live_rss", now - self.start, now, self.last_rss, progress, native)
        directory = self.directory
        manifest_path = directory / "cache" / self.clause / "manifest.json"
        manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else None
        output = {}
        for path in sorted((directory / "output").glob("*.json")):
            value = json.loads(path.read_text())
            if isinstance(value, dict) and "summary" in value:
                output[path.name] = value["summary"]
        complete = bool(self.child.returncode == 0 and manifest and manifest["completeness"] == "complete"
                        and manifest.get("valid", True) and manifest.get("errors", {}).get("valid", True)
                        and not observation.errors["panic"])
        report = {
            "complete": complete,
            "clause": self.clause, "started_at": self.started_at, "exited_at": timestamp(),
            "pid": self.child.pid, "wall_seconds": round(now - self.start, 3), "peak_rss_kib": usage.ru_maxrss,
            "returncode": self.child.returncode, "stop": self.stop, "sent_sigkill": self.sent_kill,
            "last_progress_elapsed_seconds": round(self.last_progress - self.start, 3),
            "terminal_log_counts": {f"{name}/{cert}": count for (name, cert), count in observation.terminals.items()},
            "diagnostic_log_counts": dict(observation.errors),
            "solver_path_drops": dict(observation.solver_drops),
            "root_outcomes": observation.outcomes("root"),
            "all_outcomes": observation.outcomes("inclusive"),
            "last_region_snapshot": observation.timing,
            "last_memory_snapshot": observation.memory,
            "rejection_site_rows": observation.sites,
            "last_inflight_snapshot": observation.inflight,
            "smt_metrics": {**observation.smt_metrics(), **native},
            "z3_check_positions": [{"file": site[0], "line": site[1], "column": site[2], "count": stat[0],
                                    "seconds": stat[1], "max_seconds": stat[2]}
                                   for site, stat in sorted(observation.check_times_by_position.items(),
                                                            key=lambda item: -item[1][1])],
            "manifest_path": str(manifest_path.relative_to(directory)) if manifest is not None else None,
            "manifest": {key: manifest[key] for key in ("completeness", "certification", "errors", "normal_paths",
                         "model_exception_paths", "execution_error_paths")} if manifest is not None else None,
            "solve_summaries": output,
            "output_files": {str(p.relative_to(directory)): p.stat().st_size
                             for folder in ("cache", "output") for p in (directory / folder).rglob("*")
                             if p.is_file()},
        }
        pending = directory / "summary.json.tmp"
        pending.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
        pending.rename(directory / "summary.json")
        self.complete = complete and self.stop is None
        print(f"{self.clause} 退出 {self.child.returncode}，原因={self.stop}，墙钟={report['wall_seconds']:.2f}s，"
              f"峰值RSS={usage.ru_maxrss}KiB，完整DAG={complete}", flush=True)

def stop_supervisor(signum, _frame):
    raise SystemExit(128 + signum)

if __name__ == "__main__":
    SUPERVISOR_PID = os.getpid()
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop_supervisor)
    resource.setrlimit(resource.RLIMIT_STACK, (64 * 1024 * 1024, resource.getrlimit(resource.RLIMIT_STACK)[1]))
    audit_host()
    if host_snapshot()[1] < MIN_AVAILABLE_KIB:
        raise SystemExit("启动前可用内存低于 16 GiB")
    progress_path = ARTIFACTS / "progress.tsv"
    existing = progress_path.exists()
    if existing:
        with progress_path.open() as previous:
            rows = csv.DictReader(previous, delimiter="\t")
            assert tuple(rows.fieldnames) == FIELDS
            assert all(row["isla_head"] != HEAD for row in rows), "此版本已有进度记录"
    with ExitStack() as files:
        progress = files.enter_context(progress_path.open("a" if existing else "x"))
        if not existing:
            print("\t".join(FIELDS), file=progress, flush=True)
        runs = []
        judges = []
        for clause in ("LOAD", "STORE"):
            run = Run(clause, files)
            files.callback(run.close)
            runs.append(run)
        for run in runs:
            run.observation.sample(run.clause, "start", 0, run.start, proc_rss(run.child.pid), progress,
                                   native_metrics(run.native_path))
        while runs or judges:
            pressure = None
            if runs and host_snapshot()[1] < MIN_AVAILABLE_KIB and all(run.stop is None for run in runs):
                pressure = max(runs, key=lambda run: proc_rss(run.child.pid) or 0)
            live = []
            for run in runs:
                if run.poll(progress, run is pressure):
                    live.append(run)
                elif run.complete:
                    judge_log = files.enter_context((run.directory / "judge-supervisor.log").open("wb"))
                    judge = subprocess.Popen(
                        ["python3", str(ARTIFACTS / "run-judge.py"), run.clause],
                        stdout=judge_log, stderr=judge_log, process_group=0, preexec_fn=set_parent_death_signal,
                    )
                    files.callback(lambda child: (send(child, signal.SIGKILL), child.wait()) if child.poll() is None else None,
                                   judge)
                    judges.append(judge)
            runs = live
            judges = [judge for judge in judges if judge.poll() is None]
            if runs:
                wake = min(min(run.checkpoint, run.start + PROGRAM_LIMIT if run.stop is None
                               else run.start + OUTER_LIMIT) for run in runs)
                time.sleep(max(0.05, min(1.0, wake - time.monotonic())))
            elif judges:
                time.sleep(1.0)
