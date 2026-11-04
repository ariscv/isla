#!/usr/bin/env python3
"""逐项运行第35轮对抗测试，避免Z3退出进程后漏跑其他模块。"""
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = Path(os.environ.get("ISLA_REVIEW35_LOG_DIR", "/tmp/isla-review35-results"))
LOGS.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.setdefault("CARGO_TARGET_DIR", "/tmp/isla-review35-target")
results = []
for package, target in [("isla-lib", ["--lib"]), ("isla", ["--test", "review35_memory"])]:
    command = ["cargo", "test", "-p", package, *target, "-j", "8", "--no-run", "--message-format=json"]
    build = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
    (LOGS / (package + "-build.log")).write_text(build.stdout + build.stderr)
    if build.returncode:
        print("构建失败：", package, file=sys.stderr)
        sys.exit(build.returncode)
    binaries = []
    for line in build.stdout.splitlines():
        try:
            item = json.loads(line)
        except ValueError:
            continue
        if item.get("reason") == "compiler-artifact" and item.get("profile", {}).get("test") and item.get("executable"):
            if (package == "isla-lib" and item["target"]["name"] == "isla_lib") or item["target"]["name"] == "review35_memory":
                binaries.append(item["executable"])
    assert len(binaries) == 1, binaries
    binary = binaries[0]
    listing = subprocess.check_output([binary, "--list"], text=True)
    tests = [line[:-6] for line in listing.splitlines() if "review35" in line and line.endswith(": test")]
    assert tests, listing
    for name in tests:
        log = LOGS / (name.replace("::", "_") + ".log")
        try:
            run = subprocess.run([binary, "--exact", name, "--nocapture"], env=env, capture_output=True, text=True, timeout=60)
            log.write_text(run.stdout + run.stderr)
            code = run.returncode
        except subprocess.TimeoutExpired as error:
            log.write_text(str(error))
            code = 124
        results.append({"test": name, "exit_code": code, "log": str(log)})
        print(("PASS" if code == 0 else "FAIL"), name, "exit=", code, flush=True)
(LOGS / "summary.json").write_text(json.dumps(results, ensure_ascii=False, indent=2))
print("总计", len(results), "通过", sum(r["exit_code"] == 0 for r in results), "失败", sum(r["exit_code"] != 0 for r in results))
sys.exit(1 if any(r["exit_code"] != 0 for r in results) else 0)
