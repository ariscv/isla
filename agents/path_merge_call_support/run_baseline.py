#!/usr/bin/env python3
"""复用现有函数入口，记录原始输出、命令、退出码及墙上耗时。"""
import json
import os
from pathlib import Path
import subprocess
import time

root = Path(__file__).resolve().parents[2]
base = Path(__file__).resolve().parent
out = base / "logs"
binary = Path("/tmp/claude-1005/-data1-baiyifan-workplace-isla-runner/a39d8bcc-3e1b-4db3-8d63-110f0b832032/scratchpad/target_b/debug/isla-execute-function")
command = ["timeout", "--signal=TERM", "--kill-after=5s", "590s", str(binary),
           "-A", "/data1/baiyifan/workplace/isla-runner/isla/.worktrees/memory-consistency/rv64d.ir",
           "-C", str(base / "baseline_config.toml"), "-T", "1", "--timeout", "540",
           "--traces", "--error-traces", "pte_is_invalid", "_", "_"]
env = os.environ.copy()
env["LD_LIBRARY_PATH"] = str(Path.home() / ".local/opt/z3-official-1fd1d3613/lib") + ":" + env.get("LD_LIBRARY_PATH", "")
env["ISLA_STATS"] = "1"
start = time.monotonic()
with (out / "pte_no_merge.stdout").open("w") as stdout, (out / "pte_no_merge.stderr").open("w") as stderr:
    result = subprocess.run(command, cwd=root, env=env, stdout=stdout, stderr=stderr)
metadata = dict(command=command, returncode=result.returncode, elapsed_seconds=round(time.monotonic()-start, 3))
(out / "pte_no_merge.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2)+"\n")
print(json.dumps(metadata, ensure_ascii=False))
