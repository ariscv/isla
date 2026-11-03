#!/usr/bin/env python3
"""验证统一调度、安全拒绝与预处理序列化；先构建 isla-preprocess。"""
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "test/linearize"


class LinearizePipeline(unittest.TestCase):
    def run_target(self, function, strategy, limits="", flags=(), verify=True):
        with tempfile.TemporaryDirectory(prefix="linearize-") as directory:
            directory = pathlib.Path(directory)
            config = directory / "config.toml"
            config.write_text((FIXTURES / "base.toml").read_text() +
                              f'\n[linearize]\nverify = {str(verify).lower()}\n'
                              f'[[linearize.targets]]\nfunction = "{function}"\n'
                              f'strategy = "{strategy}"\n{limits}')
            result = subprocess.run([
                str(ROOT / "target/debug/isla-preprocess"),
                "--tastic", "qfaufbv", "-T", "2", "-A", str(FIXTURES / "scalar.ir"),
                "-C", str(config), "-o", str(directory / "processed"), *flags,
            ], capture_output=True, text=True)
            if result.returncode == 0:
                self.assertTrue((directory / "processed.irx").is_file())
                result.irx_bytes = (directory / "processed.irx").read_bytes()
            return result

    def test_full_and_known_pure_call_serialize(self):
        for function in ("scalar", "pure"):
            result = self.run_target(function, "full")
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_bounded_threshold_decision(self):
        result = self.run_target("scalar", "bounded", "max_branches=1\nmax_instructions=5\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        result = self.run_target("scalar", "bounded", "max_branches=0\nmax_instructions=5\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("保留原 IR", result.stderr)
        unchanged = self.run_target("scalar", "none")
        self.assertEqual(unchanged.returncode, 0, unchanged.stderr)
        self.assertEqual(result.irx_bytes, unchanged.irx_bytes)

    def test_full_fail_fast_and_bounded_preserves_ir(self):
        for function in ("impure", "loop", "assertion"):
            result = self.run_target(function, "full", flags=("--fork-assertions",))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("安全资格检查失败", result.stderr)
            result = self.run_target(function, "bounded", "max_branches=100\nmax_instructions=100\n")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("保留原 IR", result.stderr)
            unchanged = self.run_target(function, "none")
            self.assertEqual(unchanged.returncode, 0, unchanged.stderr)
            self.assertEqual(result.irx_bytes, unchanged.irx_bytes)

    def test_cli_overrides_none_and_uses_safety_gate(self):
        for flag in ("-P", "-L"):
            result = self.run_target("pure", "none", flags=(flag, "pure", "--test-linearize"), verify=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            result = self.run_target("impure", "none", flags=(flag, "impure"), verify=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("安全资格检查失败", result.stderr)


if __name__ == "__main__":
    unittest.main()
