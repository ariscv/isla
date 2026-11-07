#!/usr/bin/env python3
"""汇总 ecfg4b 新约束的精确值与旧模型对照，拒绝不完整证明。"""

import argparse
from decimal import Decimal, localcontext
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path)
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    old = json.loads(args.old.read_text())["scenarios"]
    summary = dict(
        scope="ecfg4b；按路径累加的被测位组合，隐藏变量只要求存在可行取值",
        inputs=json.loads((args.capture / "inputs.json").read_text()),
        scenarios={},
    )
    for scene in ["sv39-load", "sv39-store", "sv48-load", "sv48-store"]:
        folder = args.capture / scene
        paths = [
            json.loads(p.read_text()) for p in sorted((folder / "exact").glob("*.json"))
        ]
        expected = json.loads((folder / "expected-paths.json").read_text())
        proofs = json.loads((folder / "validation.json").read_text())
        assert {p["signature"]: p["guard_classes"] for p in paths} == expected
        assert len(proofs) == len(expected)
        assert {p["signature"] for p in proofs} == set(expected)
        assert all(p["guard_functional"] for p in paths)
        for record in proofs:
            proof = record["memory_proof"]
            assert proof["original_implies_reduced"] == "unsat_counterexample"
            assert proof["reduced_has_explicit_array_witness"] == "unsat_counterexample"
        total = sum(int(p["exact"]) for p in paths)
        previous = int(old[scene]["exact"])
        with localcontext() as ctx:
            ctx.prec = 12
            ratio = str(Decimal(total) / Decimal(previous))
        data = dict(
            exact=str(total),
            lower_bound=str(total),
            upper_bound=str(total),
            old_exact=str(previous),
            new_over_old=ratio,
            paths=len(paths),
            guard_classes=sum(p["guard_classes"] for p in paths),
            memory_equivalence_proved_paths=len(proofs),
            memory_proof_queries=2 * len(proofs),
            f16_small_classes="跳过：旧模型的路径与守卫类目录不适用",
            capture=json.loads((folder / "exit.json").read_text()),
            raw_summary=json.loads((folder / "raw-summary.json").read_text()),
            count_path_seconds_sum=sum(p["seconds"] for p in paths),
            validation_path_seconds_sum=sum(p["seconds"] for p in proofs),
            path_results=paths,
        )
        summary["scenarios"][scene] = data
        print(scene, total, ratio, flush=True)
    args.output.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
