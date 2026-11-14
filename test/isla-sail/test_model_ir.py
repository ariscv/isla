#!/usr/bin/env python3
"""检查浮点 helper 及平台随机数均由 Sail 函数体提供。"""
import argparse
from pathlib import Path
import re
import unittest
import subprocess

class ModelIR(unittest.TestCase):
    def test_float_helpers_have_bodies(self):
        names = set(re.findall(r"^val (zriscv_\w+)", IR, re.M))
        bodies = set(re.findall(r"^fn (zriscv_\w+)", IR, re.M))
        self.assertGreaterEqual(len(names), 79)
        self.assertEqual(sorted(names - bodies), [])

    def test_random_bits_are_fresh_and_unconstrained(self):
        if not ARGS.property_bin:
            self.skipTest("未指定 isla-property")
        output = ARGS.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
        wrapped = IR
        for left, right in [(0, 65535), (65535, 0), (4660, 4660)]:
            wrapped += f"""
val zentropy_{left}_{right} : (%unit) -> %bool
fn zentropy_{left}_{right}(zu) {{
  za : %bv16;
  zb : %bv16;
  za = zget_16_random_bits(());
  zb = zget_16_random_bits(());
  return = @not(@and(@eq(za, 0x{left:04x}), @eq(zb, 0x{right:04x})));
  end;
}}
"""
        path = output / "entropy.ir"
        path.write_text(wrapped)
        for left, right in [(0, 65535), (65535, 0), (4660, 4660)]:
            name = f"entropy_{left}_{right}"
            result = subprocess.run([str(ARGS.property_bin.resolve()), "-A", str(path), "-C",
                                     str(Path(__file__).resolve().parents[2] / "configs/riscv64_difftest.toml"),
                                     "--verbose", "--no-model-reg-init", "-p", name], capture_output=True, text=True)
            text = result.stdout + result.stderr
            (output / f"{name}.log").write_text(text)
            self.assertEqual(result.returncode, 1, text)
            self.assertIn("Got sat", text)

    def test_random_bits_have_model_body(self):
        self.assertIn("fn zget_16_random_bits(", IR)
        body = IR.split("fn zget_16_random_bits(", 1)[1].split("\n}", 1)[0]
        self.assertIn("undefined_bitvector", body)
        self.assertIn("16", body)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--ir", required=True, type=Path)
    parser.add_argument("--property-bin", type=Path)
    parser.add_argument("--output", type=Path)
    ARGS, rest = parser.parse_known_args()
    if ARGS.property_bin and not ARGS.output:
        parser.error("语义检查需要 --output")
    IR = ARGS.ir.read_text()
    unittest.main(argv=[__file__] + rest)
