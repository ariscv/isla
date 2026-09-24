#!/usr/bin/env python3
"""pipeline.py 的 V 上下文重放测试。"""

import importlib.util
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("pipeline", ROOT / "pipeline.py")
pipeline = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(pipeline)


class ExpectTrapTests(unittest.TestCase):
    def test_detects_illegal_and_memory_exception(self):
        self.assertTrue(pipeline.expects_trap({"ret_val": "Illegal_Instruction(())"}))
        self.assertTrue(
            pipeline.expects_trap(
                {"ret_val": "Memory_Exception({tuple#%bv64_%union ExceptionType1: E_SAMO_Access_Fault(())})"}
            )
        )
        self.assertFalse(pipeline.expects_trap({"ret_val": "Retire_Success(())"}))
        self.assertFalse(pipeline.expects_trap({}))


class SourceEntryFilterTests(unittest.TestCase):
    def test_ret_val_regex_filters_and_stamps_source_file(self):
        with TemporaryDirectory() as directory:
            source = Path(directory) / "rv64_zX.json"
            source.write_text(
                json.dumps(
                    {
                        "gen": [
                            {
                                "test-ins": "ok",
                                "test-ins-encdec": "32'h1",
                                "arch": {"xlen": "64"},
                                "ret_val": "Retire_Success(())",
                            },
                            {
                                "test-ins": "bad",
                                "test-ins-encdec": "32'h2",
                                "arch": {"xlen": "64"},
                                "ret_val": "Illegal_Instruction(())",
                            },
                        ]
                    }
                ),
                encoding="utf-8",
            )
            entries = pipeline.source_entries([source], 0, False, r"^Illegal_Instruction")
            self.assertEqual(len(entries), 1)
            self.assertEqual(entries[0]["test-ins"], "bad")
            self.assertEqual(entries[0]["source_file"], "rv64_zX.json")
            all_entries = pipeline.source_entries([source], 0, False, None)
            self.assertEqual(len(all_entries), 2)


class TrapAwareAssemblyTests(unittest.TestCase):
    def make_trap_entry(self):
        return {
            "test-ins": "vmerge.vim v0, v30, 0x9, v0",
            "test-ins-encdec": "32'h5de4_b057",
            "isa-state": {
                "cur_privilege": "User",
                "vcsr": "3'h0",
                "vl": "64'h0000_0000_0000_0000",
                "vstart": "64'h0000_0000_0000_0000",
                "vtype": "64'h0000_0000_0000_0019",
            },
            "ret_val": "Illegal_Instruction(())",
        }

    def test_trap_entry_installs_handler_and_sentinel(self):
        assembly = pipeline.make_assembly(self.make_trap_entry(), 128)

        self.assertIn("csrw medeleg, x0", assembly)
        self.assertIn("la t0, trap_handler", assembly)
        self.assertIn("csrw mtvec, t0", assembly)
        self.assertLess(assembly.index("csrw mtvec, t0"), assembly.index("vsetvli"))
        self.assertIn("trap_handler:", assembly)
        self.assertIn("csrr t0, mepc", assembly)
        self.assertIn("la t1, payload_ins", assembly)
        self.assertIn("bne t0, t1, 2f", assembly)
        # payload_ins 紧贴 payload 指令，位于其前
        self.assertLess(assembly.index("payload_ins:"), assembly.index(".4byte 0x5de4b057"))

        payload_instruction = assembly.index(".4byte 0x5de4b057")
        park = assembly.index("1:  j 1b")
        sentinel = assembly.index(".4byte 0x00000000")
        self.assertGreater(sentinel, payload_instruction)
        self.assertLess(sentinel, park)
        # 顺序流不经过 GOODTRAP：只有 payload 处 trap 的 handler 路径才 GOODTRAP
        self.assertNotIn(".4byte 0x0000006b", assembly[payload_instruction:park])

    def test_success_entry_keeps_goodtrap_without_sentinel(self):
        entry = {
            "test-ins": "vadd.vv v8, v4, v12",
            "test-ins-encdec": "32'h0246_0457",
            "isa-state": {
                "cur_privilege": "User",
                "vl": "64'h0000_0000_0000_0007",
                "vtype": "64'h0000_0000_0000_00da",
            },
        }

        assembly = pipeline.make_assembly(entry, 256)

        self.assertNotIn(".4byte 0x00000000", assembly)
        payload_instruction = assembly.index(".4byte 0x02460457")
        park = assembly.index("1:  j 1b")
        self.assertLess(assembly.index(".4byte 0x0000006b"), park)
        self.assertGreater(assembly.index(".4byte 0x0000006b"), payload_instruction)
        self.assertIn("trap_handler:", assembly)
        self.assertIn("2:  j 2b", assembly)
        self.assertNotIn("csrr t0, mepc", assembly)


class VectorContextAssemblyTests(unittest.TestCase):
    def test_replays_vtype_vl_vstart_and_vcsr_before_payload(self):
        entry = {
            "test-ins": "vadd.vv v8, v4, v12",
            "test-ins-encdec": "32'h0246_0457",
            "isa-state": {
                "cur_privilege": "User",
                "vl": "64'h0000_0000_0000_0007",
                "vstart": "64'h0000_0000_0000_0002",
                "vtype": "64'h0000_0000_0000_00da",
                "vcsr": "3'h5",
            },
        }

        assembly = pipeline.make_assembly(entry, 256)

        self.assertIn("li t1, 7", assembly)
        self.assertIn("vsetvli zero, t1, 0xda", assembly)
        self.assertIn("li t0, 2", assembly)
        self.assertIn("csrw vstart, t0", assembly)
        self.assertIn("li t0, 2", assembly)
        self.assertIn("csrw vxrm, t0", assembly)
        self.assertIn("li t0, 1", assembly)
        self.assertIn("csrw vxsat, t0", assembly)
        self.assertIn("csrw pmpaddr0, t0", assembly)
        self.assertIn("csrw pmpcfg0, t0", assembly)
        self.assertIn("mret", assembly)
        self.assertLess(assembly.index("vsetvli zero, t1, 0xda"), assembly.index(".4byte 0x02460457"))

    def test_replays_vill_with_a_reserved_vsetvli_immediate(self):
        entry = {
            "test-ins": "vadd.vv v8, v4, v12",
            "test-ins-encdec": "32'h0246_0457",
            "isa-state": {
                "vl": "64'h0000_0000_0000_0000",
                "vtype": "64'h8000_0000_0000_0000",
            },
        }

        assembly = pipeline.make_assembly(entry, 128)

        self.assertIn("vsetvli zero, t1, 0x400 (建立 VILL)", assembly)

    def test_replays_scalar_registers_after_privilege_setup(self):
        entry = {
            "test-ins": "vsetvl x0, x26, x1",
            "test-ins-encdec": "32'h801d_7057",
            "isa-state": {
                "cur_privilege": "User",
                "vl": "64'h0000_0000_0000_0001",
                "vtype": "64'h0000_0000_0000_0000",
                "x1": "64'h0000_0000_0000_0007",
                "x26": "64'h8000_0000_0000_000c",
            },
        }

        assembly = pipeline.make_assembly(entry, 128)

        payload = assembly.index("payload:")
        payload_instruction = assembly.index(".4byte 0x801d7057")
        self.assertGreater(assembly.index("li x1, 0x7"), payload)
        self.assertGreater(assembly.index("li x26, 0x800000000000000c"), payload)
        self.assertLess(assembly.index("li x1, 0x7"), payload_instruction)
        self.assertLess(assembly.index("li x26, 0x800000000000000c"), payload_instruction)

    def test_rejects_vl_that_vsetvl_would_clamp(self):
        entry = {
            "test-ins": "vadd.vv v8, v4, v12",
            "test-ins-encdec": "32'h0246_0457",
            "isa-state": {
                "vl": "64'h0000_0000_0000_0011",
                "vtype": "64'h0000_0000_0000_0000",
            },
        }

        with self.assertRaisesRegex(ValueError, "VLMAX"):
            pipeline.make_assembly(entry, 128)

    def test_difftest_case_worker_marks_goodtrap(self):
        with TemporaryDirectory() as directory:
            elf = Path(directory) / "program.elf"
            elf.touch()
            case = {"id": "case-000", "elf": str(elf)}
            completed = SimpleNamespace(returncode=0, stdout="HIT GOOD TRAP")
            with patch.object(pipeline.subprocess, "run", return_value=completed) as run:
                result = pipeline.run_case(case, Path("emu"), Path("ref.so"), 1)

            self.assertEqual(result["category"], "success")
            self.assertEqual(
                (elf.parent / "difftest.log").read_text(encoding="utf-8"),
                "HIT GOOD TRAP\n",
            )
            self.assertNotIn("--force-dump-result", run.call_args.args[0])
            self.assertIs(run.call_args.kwargs["stderr"], pipeline.subprocess.STDOUT)

    def test_difftest_case_worker_rejects_zero_exit_without_goodtrap(self):
        with TemporaryDirectory() as directory:
            elf = Path(directory) / "program.elf"
            elf.touch()
            case = {"id": "case-000", "elf": str(elf)}
            completed = SimpleNamespace(returncode=0, stdout="")
            with patch.object(pipeline.subprocess, "run", return_value=completed) as run:
                result = pipeline.run_case(case, Path("emu"), Path("ref.so"), 1)

            self.assertEqual(result["category"], "failure")
            self.assertEqual(run.call_count, 1)
            self.assertNotIn("--force-dump-result", run.call_args.args[0])
            self.assertIs(run.call_args.kwargs["stderr"], pipeline.subprocess.STDOUT)

    def test_difftest_case_worker_records_first_run_output_for_failure(self):
        with TemporaryDirectory() as directory:
            elf = Path(directory) / "program.elf"
            elf.touch()
            case = {"id": "case-000", "elf": str(elf)}
            failed = SimpleNamespace(returncode=1, stdout="abort with different-at")
            with patch.object(pipeline.subprocess, "run", return_value=failed) as run:
                result = pipeline.run_case(case, Path("emu"), Path("ref.so"), 1)

            self.assertEqual(result["category"], "failure")
            # ABORT 的第一跑 stdout 已含差异信息，不再重跑 trace
            self.assertEqual(run.call_count, 1)
            self.assertEqual(
                (elf.parent / "difftest.log").read_text(encoding="utf-8"),
                "abort with different-at",
            )

    def test_difftest_case_worker_records_execution_timeout_as_failure(self):
        with TemporaryDirectory() as directory:
            elf = Path(directory) / "program.elf"
            elf.touch()
            case = {"id": "case-000", "elf": str(elf)}
            timed_out = pipeline.subprocess.TimeoutExpired(["emu"], 1, output="partial run")
            trace_timed_out = pipeline.subprocess.TimeoutExpired(
                ["emu", "--dump-commit-trace"], 1, output="partial trace"
            )
            with patch.object(
                pipeline.subprocess, "run", side_effect=[timed_out, trace_timed_out]
            ) as run:
                result = pipeline.run_case(case, Path("emu"), Path("ref.so"), 1)

            self.assertEqual(result["category"], "failure")
            log = (elf.parent / "difftest.log").read_text(encoding="utf-8")
            self.assertIn("execution timeout", log)
            self.assertIn("partial trace", log)
            self.assertIn("--dump-commit-trace", run.call_args_list[1].args[0])
            self.assertIn("elapsed", result)


class RunIncrementalRecordingTests(unittest.TestCase):
    def make_cases_dir(self, directory: str) -> Path:
        cases_dir = Path(directory)
        elf = cases_dir / "case-000" / "program.elf"
        elf.parent.mkdir(parents=True, exist_ok=True)
        elf.touch()
        manifest = [
            {
                "id": "case-000",
                "instruction": "vmerge.vim v0, v30, 0x9, v0",
                "encoding": "32'h5de4_b057",
                "elf": str(elf),
                "ret_val": "Illegal_Instruction(())",
                "expect_trap": True,
            }
        ]
        (cases_dir / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        (cases_dir / "emu").touch()
        (cases_dir / "ref.so").touch()
        return cases_dir

    def test_run_appends_each_result_and_resumes(self):
        with TemporaryDirectory() as directory:
            cases_dir = self.make_cases_dir(directory)
            args = SimpleNamespace(
                cases=str(cases_dir),
                emulator=str(cases_dir / "emu"),
                diff_so=str(cases_dir / "ref.so"),
                jobs=1,
                timeout=5,
            )
            fake = {
                **json.loads((cases_dir / "manifest.json").read_text(encoding="utf-8"))[0],
                "category": "success",
                "returncode": 0,
                "log": "x",
                "elapsed": 0.1,
            }
            with patch.object(pipeline, "run_case", return_value=fake) as run_case_mock:
                pipeline.run(args)

            run_case_mock.assert_called_once()
            ndjson = cases_dir / "results.ndjson"
            lines = ndjson.read_text(encoding="utf-8").strip().splitlines()
            self.assertEqual(len(lines), 1)
            self.assertEqual(json.loads(lines[0])["id"], "case-000")
            results = json.loads((cases_dir / "results.json").read_text(encoding="utf-8"))
            self.assertEqual(len(results), 1)

            # 再次运行：全部条目已完成，不再执行任何用例，记录不重复
            with patch.object(pipeline, "run_case") as run_case_mock:
                pipeline.run(args)

            run_case_mock.assert_not_called()
            self.assertEqual(
                len(ndjson.read_text(encoding="utf-8").strip().splitlines()), 1
            )

    def test_run_skips_incomplete_ndjson_line(self):
        with TemporaryDirectory() as directory:
            cases_dir = self.make_cases_dir(directory)
            ndjson = cases_dir / "results.ndjson"
            ndjson.write_text('{"id": "case-00', encoding="utf-8")
            args = SimpleNamespace(
                cases=str(cases_dir),
                emulator=str(cases_dir / "emu"),
                diff_so=str(cases_dir / "ref.so"),
                jobs=1,
                timeout=5,
            )
            fake = {
                "id": "case-000",
                "category": "success",
                "returncode": 0,
                "log": "x",
                "elapsed": 0.1,
            }
            with patch.object(pipeline, "run_case", return_value=fake):
                pipeline.run(args)

            lines = ndjson.read_text(encoding="utf-8").strip().splitlines()
            self.assertEqual(len(lines), 2)
            self.assertEqual(json.loads(lines[1])["id"], "case-000")


if __name__ == "__main__":
    unittest.main()
