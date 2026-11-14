#!/usr/bin/env python3
"""确认类型擦除前把有限整数集合写成运行期假设。"""
import argparse
from pathlib import Path
import re
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]

class FiniteDomain(unittest.TestCase):
    def test_union_payload_retains_noncontiguous_domain(self):
        command = ["sail", "-plugin", str(ROOT / "isla-sail/plugin.cmxs"), "-isla",
                   "--isla-preserve", "read_width", "--isla-preserve", "prop",
                   *[arg for n in (1, 2, 4, 8) for arg in ("--isla-preserve", f"witness{n}")],
                   "--isla-output-dir", str(OUTPUT),
                   "-o", "finite_domain", str(ROOT / "test/isla-sail/finite_domain.sail")]
        subprocess.run(command, check=True, capture_output=True, text=True)
        ir_path = OUTPUT / "finite_domain.ir"
        ir = ir_path.read_text()
        self.assertRegex(ir, r'= \$zisla_type_assume\(')
        for value in (1, 2, 4, 8):
            self.assertRegex(ir, rf'@eq\([^\n]*, {value}\)')
        for name, expected in [("prop", 0), *[(f"witness{n}", 1) for n in (1, 2, 4, 8)]]:
            result = subprocess.run([str(PROPERTY_BIN), "-A", str(ir_path),
                                     "-C", str(ROOT / "configs/plain.toml"), "-p", name],
                                    capture_output=True, text=True)
            (OUTPUT / f"{name}.log").write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, expected, result.stdout + result.stderr)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--property-bin", type=Path, default=ROOT / "target/debug/isla-property")
    args, rest = parser.parse_known_args()
    PROPERTY_BIN = args.property_bin.resolve()
    OUTPUT = args.output.resolve()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    unittest.main(argv=[__file__] + rest)
