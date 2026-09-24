#!/usr/bin/env python3
"""按分片并行重跑 PoC:rerun_shard.py --manifest M --shard i --shards N --jobs J --out out.ndjson"""

from __future__ import annotations

import argparse
import json
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


def run_one(case: dict, emu: str, so: str, timeout: int) -> dict:
    started = time.monotonic()
    cmd = [emu, "-i", case["elf"], "--diff", so]
    try:
        p = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=timeout)
        out = p.stdout
        rc = p.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or "")
        if isinstance(out, bytes):
            out = out.decode(errors="replace")
        rc = None
    ok = rc == 0 and "HIT GOOD TRAP" in out
    diffs = [l.strip() for l in out.splitlines() if "different at" in l]
    log = Path(case["elf"]).parent / "difftest.log"
    log.write_text("HIT GOOD TRAP\n" if ok else out, encoding="utf-8", errors="replace")
    return {**case, "category": "success" if ok else "failure", "returncode": rc,
            "diffs": diffs[:6], "log": str(log),
            "elapsed": round(time.monotonic() - started, 2)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--shard", type=int, required=True)
    ap.add_argument("--shards", type=int, required=True)
    ap.add_argument("--jobs", type=int, default=16)
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--emu", required=True)
    ap.add_argument("--so", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    cases = json.loads(Path(args.manifest).read_text(encoding="utf-8"))
    mine = [c for i, c in enumerate(cases) if i % args.shards == args.shard]
    done = set()
    out_path = Path(args.out)
    if out_path.is_file():
        for line in out_path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line:
                try:
                    done.add(json.loads(line)["id"])
                except json.JSONDecodeError:
                    pass
    pending = [c for c in mine if c["id"] not in done]
    print(f"shard {args.shard}/{args.shards}: 本片 {len(mine)} 条,已完成 {len(done)},待跑 {len(pending)},jobs={args.jobs}", flush=True)

    n = len(done)
    with out_path.open("a", encoding="utf-8") as sink:
        with ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(run_one, c, args.emu, args.so, args.timeout): c for c in pending}
            for f in as_completed(futs):
                r = f.result()
                sink.write(json.dumps(r, ensure_ascii=False) + "\n")
                sink.flush()
                n += 1
                if n % 50 == 0 or n == len(mine):
                    ok = sum(1 for _ in [1])  # 进度行
                    print(f"shard {args.shard}: [{n}/{len(mine)}] 最新 {r['id']}={r['category']} ({r['elapsed']}s)", flush=True)
    print(f"shard {args.shard} 完成: {out_path}", flush=True)


if __name__ == "__main__":
    main()
