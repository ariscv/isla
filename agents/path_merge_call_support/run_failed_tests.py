#!/usr/bin/env python3
"""逐条复跑 HEAD 的五个已知失败测试；单条含构建最多 595 秒。"""
import json
import os
from pathlib import Path
import subprocess
import time

root = Path(__file__).resolve().parents[2]
out = Path(__file__).resolve().parent / "logs"
out.mkdir(exist_ok=True)
env = os.environ.copy()
z3 = str(Path.home() / ".local/opt/z3-official-1fd1d3613/lib")
env["RUSTFLAGS"] = f"-L {z3} -C link-arg=-Wl,-rpath,{z3}"
env["LD_LIBRARY_PATH"] = z3 + ":" + env.get("LD_LIBRARY_PATH", "")
env["CARGO_TARGET_DIR"] = "/tmp/claude-1005/-data1-baiyifan-workplace-isla-runner/a39d8bcc-3e1b-4db3-8d63-110f0b832032/scratchpad/target_b"
cases = [
    "review12_tests::internal_vector_init_after_merge",
    "review13_tests::monomorphize_machine_integer_after_merge_does_not_crash",
    "review14_tests::internal_vector_update_retries_merged_index",
    "review21_tests::review21_merged_overflow_path",
    "review8_tests::adversarial_merge_machine_index_width",
]
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
results = []
for case in cases:
    name = "executor::tests::" + case
    command = ["timeout", "--signal=TERM", "--kill-after=5s", "590s",
               "cargo", "test", "-p", "isla-lib", name, "--offline",
               "--features", "smt-thread-interrupt", "-j", "8", "--", "--exact", "--nocapture"]
    start = time.monotonic()
    print("开始：" + name, flush=True)
    with (out / (case.split("::")[0] + ".log")).open("w") as log:
        completed = subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
    result = dict(name=name, command=command, returncode=completed.returncode,
                  elapsed_seconds=round(time.monotonic()-start, 3), head=head)
    results.append(result)
    (out / "failed_tests.json").write_text(json.dumps(results, ensure_ascii=False, indent=2)+"\n")
    print(json.dumps(result, ensure_ascii=False), flush=True)
