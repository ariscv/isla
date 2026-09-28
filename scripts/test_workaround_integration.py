"""检查 solve 入口直接读取 Sail-RISC-V 中的 workaround。"""

from pathlib import Path
import subprocess
import tomllib
import unittest


ISLA = Path(__file__).resolve().parents[1]
WORKAROUNDS = ISLA.parent / "sail-riscv/configs/isla/workarounds"


class WorkaroundMakeTest(unittest.TestCase):
    def dry_run(self, clause: str) -> str:
        result = subprocess.run(
            ["make", "-n", "-f", "scripts/run.mk", f"solve-{clause}"],
            cwd=ISLA,
            text=True,
            capture_output=True,
            check=True,
        )
        return result.stdout

    def test_configured_clause_uses_sail_riscv_workaround(self) -> None:
        output = self.dry_run("VVTYPE")
        self.assertIn("--execution-limits-config ../sail-riscv/configs/isla/workarounds/vvtype.toml", output)
        self.assertNotIn("generate_isla_workarounds.py", output)

    def test_unconfigured_clause_has_no_workaround(self) -> None:
        output = self.dry_run("ADDIW")
        self.assertNotIn("--execution-limits-config", output)

    def test_sail_workarounds_use_advisory_ir_hash(self) -> None:
        paths = sorted(WORKAROUNDS.glob("*.toml"))
        self.assertEqual(len(paths), 79)
        for path in paths:
            limits = tomllib.loads(path.read_text())["execution_limits"]
            self.assertIs(limits["strict"], False, path.name)
            self.assertEqual(len(limits["ir_sha256"]), 64, path.name)


if __name__ == "__main__":
    unittest.main()
