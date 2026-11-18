#!/usr/bin/env python3
"""内层合并失败不连累外层：Sail 最简模型端到端验收（骨架，待 Codex 审核与补全）。"""
import argparse
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
SAIL_FILE = ROOT / "test/path-merge/nested_merge_local_failure.sail"


def compile_sail(output: Path) -> Path:
    """把 Sail 模型编译成 IR（沿用 test/isla-sail/test_finite_domain.py 的命令形态）。"""
    # TODO：--isla-preserve 需要保留各场景函数名
    command = ["sail", "-plugin", str(ROOT / "isla-sail/plugin.cmxs"), "-isla",
               "--isla-output-dir", str(output), "-o", "nested_merge_local_failure", str(SAIL_FILE)]
    subprocess.run(command, check=True, capture_output=True, text=True)
    return output / "nested_merge_local_failure.ir"


def run_function(ir: Path, function: str, args: list, merging: bool, strategy: str = "recursive") -> str:
    """调用 isla-execute-function，返回标准输出。TODO：写临时 TOML 配置设置 strategy；解析 --traces 输出。"""
    raise NotImplementedError("骨架")


def count_paths(output: str) -> int:
    """TODO：按 --traces 输出里每条成功执行的分隔符统计路径数。"""
    raise NotImplementedError("骨架")


class NestedMergeLocalFailure(unittest.TestCase):
    def test_s1_outer3_inner_partial(self):
        self.skipTest("骨架：待 Codex 补全；期望 不合并 9 条，合并后 2 条")

    def test_s2_inner_all_same(self):
        self.skipTest("骨架：期望 9 → 1")

    def test_s3_inner_all_distinct(self):
        self.skipTest("骨架：期望 9 → 3")

    def test_s4_three_levels(self):
        self.skipTest("骨架")

    def test_s5_callee_inner_failure(self):
        self.skipTest("骨架")

    def test_s6_failure_at_outer_join(self):
        self.skipTest("骨架")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--execute-bin", type=Path, default=ROOT / "target/debug/isla-execute-function")
    args, rest = parser.parse_known_args()
    EXECUTE_BIN = args.execute_bin.resolve()
    OUTPUT = args.output.resolve()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    unittest.main(argv=[__file__] + rest)
