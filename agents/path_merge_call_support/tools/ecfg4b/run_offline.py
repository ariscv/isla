"""最多四个离线进程，保存每场景计数和证明的实测耗时与退出码。"""

import argparse
import concurrent.futures
import json
from pathlib import Path
import subprocess
import sys
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("capture", type=Path)
a = p.parse_args()
base = a.capture.resolve()
tools = Path(__file__).resolve().parent
start = time.monotonic()


def run(scene):
    folder = base / scene
    records = {}
    for stage, command in [
        ("count", [sys.executable, str(tools / "exact_count.py"), str(folder)]),
        (
            "validate",
            [
                sys.executable,
                str(tools / "exact_validate.py"),
                str(folder),
                "--skip-f16-classes",
            ],
        ),
    ]:
        before = time.monotonic()
        with (folder / (stage + ".log")).open("w") as log:
            result = subprocess.run(
                command, stdout=log, stderr=subprocess.STDOUT, timeout=2400
            )
        records[stage] = dict(exit=result.returncode, seconds=time.monotonic() - before)
        (folder / "offline-status.json").write_text(
            json.dumps(records, indent=2) + "\n"
        )
        print(scene, stage, records[stage], flush=True)
        assert result.returncode == 0, (scene, stage)
    return records


with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    results = dict(
        zip(
            ["sv39-load", "sv39-store", "sv48-load", "sv48-store"],
            pool.map(run, ["sv39-load", "sv39-store", "sv48-load", "sv48-store"]),
        )
    )
(base / "offline-status.json").write_text(
    json.dumps(dict(seconds=time.monotonic() - start, scenarios=results), indent=2)
    + "\n"
)
