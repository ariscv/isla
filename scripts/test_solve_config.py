"""检查 solve 入口的主配置与显式指定的独立配置。"""

from pathlib import Path
import subprocess
import tempfile
import unittest


ISLA = Path(__file__).resolve().parents[1]


class SolveConfigTest(unittest.TestCase):
    def dry_run(self, clause: str, *options: str) -> str:
        result = subprocess.run(
            ["make", "-n", f"solve-{clause}", *options],
            cwd=ISLA,
            text=True,
            capture_output=True,
            check=True,
        )
        return result.stdout

    def test_solve_uses_main_config_by_default(self) -> None:
        for clause in ("MRET", "MVVCOMPRESS", "VVTYPE"):
            with self.subTest(clause=clause):
                output = self.dry_run(clause)
                self.assertIn("-C ./configs/riscv64_difftest.toml", output)
                self.assertIn(f"solve-state --clause={clause}", output)
                self.assertNotIn("--execution-limits-config", output)

    def test_solve_accepts_explicit_standalone_config(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            override = Path(directory) / "limits.toml"
            override.write_text("[execution_limits.path_merge]\nenabled = true\n")
            output = self.dry_run("VVTYPE", f"EXECUTION_LIMITS_CONFIG={override}",
                                  "SOLVE_CONFIG=./configs/riscv64_difftest_mem.toml")
            self.assertIn(f"--execution-limits-config {override}", output)
            self.assertIn("-C ./configs/riscv64_difftest_mem.toml", output)


if __name__ == "__main__":
    unittest.main()
