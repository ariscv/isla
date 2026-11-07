#!/usr/bin/env python3
"""汇总逐路径精确数、验证证据及 F16 对照；拒绝不完整批次。"""

import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path)
    parser.add_argument("--f16", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compare", type=Path, help="另一个受测版本的完整精确计数目录")
    args = parser.parse_args()
    f16 = json.loads(args.f16.read_text())
    summary = dict(
        scope="F16 新配置；按路径累加的被测位组合，隐藏变量存在量化",
        inputs=json.loads((args.capture / "inputs.json").read_text()),
        scenarios={},
    )
    for scene, reference in f16["scenarios"].items():
        folder = args.capture / scene
        paths = [
            json.loads(p.read_text()) for p in sorted((folder / "exact").glob("*.json"))
        ]
        proofs = json.loads((folder / "validation.json").read_text())
        expected = {
            str(p["path_signature"]): p["classes"] for p in reference["glue"]["paths"]
        }
        assert {p["signature"]: p["guard_classes"] for p in paths} == expected
        assert {p["signature"] for p in proofs} == set(expected)
        assert all(p["guard_functional"] for p in paths)
        checks = {p["signature"]: p for p in proofs}
        for path in paths:
            proof = checks[path["signature"]]["memory_proof"]
            assert proof["original_implies_reduced"] == "unsat_counterexample"
            assert proof["reduced_has_explicit_array_witness"] == "unsat_counterexample"
            if args.compare:
                other = json.loads(
                    (
                        args.compare / scene / "exact" / f"{path['signature']}.json"
                    ).read_text()
                )
                assert path["exact"] == other["exact"]
            path["smt_sha256"] = hashlib.sha256(
                (folder / "smt" / f"path-{path['signature']}.smt2").read_bytes()
            ).hexdigest()
        total = sum(int(p["exact"]) for p in paths)
        estimate = reference["predict"]["total"]
        data = dict(
            exact=str(total),
            lower_bound=str(total),
            upper_bound=str(total),
            paths=len(paths),
            guard_classes=sum(p["guard_classes"] for p in paths),
            f16_mean=estimate["mean"],
            f16_interval=estimate["confidence_95"],
            exact_relative_to_f16_mean=total / estimate["mean"],
            inside_f16_approximate_interval=estimate["confidence_95"][0]
            <= total
            <= estimate["confidence_95"][1],
            memory_equivalence_proved_paths=len(proofs),
            f16_small_exact_paths=sum("f16_exact_total" in p for p in proofs),
            f16_small_exact_classes=sum(p.get("f16_exact_classes", 0) for p in proofs),
            compared_version_paths=len(paths) if args.compare else None,
            capture=json.loads((folder / "exit.json").read_text()),
            count_path_seconds_sum=sum(p["seconds"] for p in paths),
            validation_path_seconds_sum=sum(p["seconds"] for p in proofs),
            path_results=paths,
        )
        summary["scenarios"][scene] = data
        print(scene, total, flush=True)
    args.output.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
