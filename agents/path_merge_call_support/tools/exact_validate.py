#!/usr/bin/env python3
"""对本轮转换作双向证明，并与 F16 的已知精确逐类结果核对。"""

import argparse
import json
from pathlib import Path
import sys
import time
import z3
from exact_bdd import count_formula, eliminate_memory
from exact_count import prepare


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder", type=Path)
    args = parser.parse_args()
    sys.setrecursionlimit(20000)
    f16 = json.loads((args.folder / "f16-prediction.json").read_text())
    f16_paths = {str(p["path_signature"]): p for p in f16["paths"]}
    result = []
    for path in sorted((args.folder / "smt").glob("*.smt2")):
        start = time.monotonic()
        signature = path.stem[5:]
        original = z3.And(*z3.parse_smt2_file(str(path)))
        _, proof = eliminate_memory(original, prove=True)
        record = dict(signature=signature, memory_proof=proof)
        old = f16_paths[signature]
        if old["method"] == "exact":
            report = json.loads(
                (args.folder / "reports" / f"glue-{signature}.json").read_text()
            )
            _, _, boolean, targets, guards, _ = prepare(path, report)
            total = 0
            counts = []
            for guard_class in old["guard_classes"]:
                # 按函数、分支位置和父边核对类目录，不能直接比较跨进程 record_id。
                assignment = guard_class["guard_values"]

                def descriptors(records, order):
                    by_id = {r["record_id"]: r for r in records}
                    positions = {i: n for n, i in enumerate(order)}
                    return [
                        (
                            by_id[i]["function"],
                            by_id[i]["branch_pc"],
                            by_id[i]["arm"],
                            positions.get(by_id[i]["parent_record"]),
                        )
                        for i in order
                    ]

                assert descriptors(
                    old["guard_records"], old["guard_order"]
                ) == descriptors(report["guard_records"], report["record_ids"])
                assert len(assignment) == len(guards)
                condition = z3.And(
                    *[
                        guard if value else z3.Not(guard)
                        for value, guard in zip(assignment, guards)
                    ]
                )
                count = count_formula(z3.And(boolean, condition), targets)
                assert count == int(guard_class["exact"]), (
                    signature,
                    guard_class["class_id"],
                    count,
                    guard_class["exact"],
                )
                total += count
                counts.append(str(count))
            computed = json.loads(
                (args.folder / "exact" / f"{signature}.json").read_text()
            )
            assert total == int(old["total"]["exact"]) == int(computed["exact"])
            record["f16_exact_classes"] = len(counts)
            record["class_counts"] = counts
            record["f16_exact_total"] = str(total)
        record["seconds"] = time.monotonic() - start
        result.append(record)
        print(
            signature,
            record.get("f16_exact_classes", ""),
            round(record["seconds"], 3),
            flush=True,
        )
        (args.folder / "validation.json").write_text(
            json.dumps(result, indent=2) + "\n"
        )


if __name__ == "__main__":
    main()
