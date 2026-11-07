"""先检查汇总会拒绝缺失证明和缺失路径。"""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class SummaryTests(unittest.TestCase):
    def fixture(self, root):
        (root / "inputs.json").write_text("{}")
        old = {"scenarios": {}}
        for scene in ["sv39-load", "sv39-store", "sv48-load", "sv48-store"]:
            folder = root / scene
            (folder / "exact").mkdir(parents=True)
            (folder / "exact/1.json").write_text(
                json.dumps(
                    dict(
                        signature="1",
                        exact="20",
                        guard_classes=2,
                        guard_functional=True,
                        seconds=0.1,
                    )
                )
            )
            (folder / "expected-paths.json").write_text('{"1": 2}')
            (folder / "validation.json").write_text(
                json.dumps(
                    [
                        dict(
                            signature="1",
                            seconds=0.2,
                            memory_proof=dict(
                                original_implies_reduced="unsat_counterexample",
                                reduced_has_explicit_array_witness="unsat_counterexample",
                            ),
                        )
                    ]
                )
            )
            (folder / "exit.json").write_text('{"exit": 1, "seconds": 1}')
            (folder / "raw-summary.json").write_text('{"status": "partial"}')
            old["scenarios"][scene] = {"exact": "10"}
        (root / "old.json").write_text(json.dumps(old))

    def run_summary(self, root):
        return subprocess.run(
            [
                sys.executable,
                str(Path(__file__).with_name("exact_summary.py")),
                str(root),
                "--old",
                str(root / "old.json"),
                "--output",
                str(root / "result.json"),
            ],
            text=True,
            capture_output=True,
        )

    def test_精确求和与倍数(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            run = self.run_summary(root)
            self.assertEqual(run.returncode, 0, run.stderr)
            data = json.loads((root / "result.json").read_text())["scenarios"][
                "sv39-load"
            ]
            self.assertEqual(data["exact"], "20")
            self.assertEqual(data["new_over_old"], "2")

    def test_缺少内存证明必须拒绝(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "sv39-load/validation.json").write_text("[]")
            self.assertNotEqual(self.run_summary(root).returncode, 0)

    def test_缺少路径必须拒绝(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / "sv39-load/expected-paths.json").write_text('{"1": 2, "2": 3}')
            self.assertNotEqual(self.run_summary(root).returncode, 0)


if __name__ == "__main__":
    unittest.main()
