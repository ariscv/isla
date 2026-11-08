"""验证指令字段和通用寄存器保持符号化，并启用已有执行限制。"""
import importlib.util
import json
from pathlib import Path
import tempfile
import tomllib
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('s1_run', Path(__file__).with_name('run.py'))
RUN = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUN)
ANALYSIS_SPEC = importlib.util.spec_from_file_location('s1_analyze', Path(__file__).with_name('analyze.py'))
ANALYSIS = importlib.util.module_from_spec(ANALYSIS_SPEC)
ANALYSIS_SPEC.loader.exec_module(ANALYSIS)


class ExplorationConfigTests(unittest.TestCase):
    def test_prepare_reuses_configs_without_gpr_overrides(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, e2, output = root / 'source', root / 'e2', root / 'out'
            source.mkdir()
            e2.mkdir()
            (source / 'enumeration.toml').write_text(
                '[execution_limits]\nstrict = false\n'
                '[execution_limits.merge_enumeration]\nenabled = true\nclass_cap = 1\n')
            (source / 'config-xs.toml').write_text('pc = "PC"\n')
            (e2 / 'E2.toml').write_text('[symbolic_registers]\nmstatus = "symbolic"\n')
            with patch.multiple(RUN, SOURCE=source, E2=e2, OUT=output, CLASS_CAP=32):
                RUN.prepare()
            for base in ('E0', 'E2'):
                config = tomllib.loads((output / f'{base}.toml').read_text())
                original = source / 'config-xs.toml' if base == 'E0' else e2 / 'E2.toml'
                self.assertEqual(config, tomllib.loads(original.read_text()))
            for name in ('enumeration', 'enumeration-16', 'enumeration-32', 'enumeration-64', 'judge'):
                limits = tomllib.loads((output / f'{name}.toml').read_text())['execution_limits']
                self.assertTrue(limits['path_merging'])
                self.assertEqual(limits['on_limit_reached'], 'truncate')
                self.assertTrue(limits['branch_region_limits'])
                self.assertTrue(all(item['max_forks_per_branch'] > 0 for item in limits['branch_region_limits']))
                if name != 'judge':
                    self.assertEqual(limits['merge_enumeration']['class_cap'], 32)

    def test_process_exit_does_not_imply_complete_exploration(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / 'E0-sv39-load-export'
            (directory / 'output').mkdir(parents=True)
            (directory / 'samples.jsonl').write_text('')
            for timed_out, returncode, status, truncated, complete in (
                    (False, 0, 'finished', 0, True),
                    (False, 1, 'partial', 0, False),
                    (True, -9, 'finished', 0, False),
                    (False, 0, 'finished', 1, False)):
                done = dict(seconds=1.5, limit_seconds=2, timed_out=timed_out,
                            returncode=returncode, max_rss_kib=1024,
                            user_seconds=1.0, system_seconds=0.1)
                (directory / 'done.json').write_text(json.dumps(done))
                merge = dict(attempts=0, successes=0, merge_enumeration=dict(truncated_paths=truncated))
                (directory / 'stderr.txt').write_text(
                    '[MERGE_STATS] ' + json.dumps(merge) + '\n[FORK_STATS] {"total": 0}\n')
                (directory / 'output/rv64_zLOAD.json').write_text(json.dumps(dict(
                    summary=dict(status=status), diagnostics=[], gen=[])))
                result = ANALYSIS.summarize(directory)
                self.assertEqual(result['fully_converged'], complete)
                self.assertEqual(result['max_rss_kib'], 1024)

    def test_runner_removes_x1_override_and_records_timeout_resources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            binary = root / 'target/release/isarch'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/usr/bin/python3\nimport time\ntime.sleep(10)\n')
            binary.chmod(0o755)
            source = root / 'source/sv39-load'
            source.mkdir(parents=True)
            command = ['isarch', '-C', 'old.toml', '-T', '1', '--timeout', '1',
                       '--prestate', 'x1=123', '--prestate', 'satp=456',
                       '--execution-limits-config', 'old-limits.toml', 'solve-state']
            (source / 'done.json').write_text(json.dumps(dict(command=command)))
            output = root / 'output'
            with patch.multiple(RUN, ROOT=root, SOURCE=root / 'source', OUT=output,
                                GROUP='test', SECONDS=1, THREADS=32, ENUM_THREADS=32):
                RUN.run('E0-sv39-load', 'export')
            directory = output / 'test/E0-sv39-load-export'
            done = json.loads((directory / 'done.json').read_text())
            self.assertTrue(done['timed_out'])
            self.assertEqual(done['returncode'], -9)
            self.assertGreaterEqual(done['seconds'], 1)
            self.assertLess(done['seconds'], 5)
            self.assertGreater(done['max_rss_kib'], 0)
            self.assertNotIn('x1=123', done['command'])
            self.assertIn('satp=0x8000000000080200', done['command'])
            self.assertTrue((directory / 'resources.jsonl').read_text())

    def test_every_phase_builds_symbolic_clause_without_legacy_command(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            binary = root / 'target/release/isarch'
            binary.parent.mkdir(parents=True)
            binary.write_text('#!/usr/bin/python3\n')
            binary.chmod(0o755)
            for scene in ('sv39-load', 'sv48-store', 'bare-load', 'bare-store'):
                source = root / 'source' / scene
                source.mkdir(parents=True)
                # 旧记录中两种机器码参数拼法和任意通用寄存器固定值都不能继承。
                (source / 'done.json').write_text(json.dumps(dict(command=[
                    'old-isarch', '--instruction-bits', '0x0000b103',
                    '--instruction-bits=0x0020b023', '--prestate', 'x1=123',
                    '--prestate=x31=456'])))
                for base in ('E0', 'E2'):
                    for phase in ('export', 'slots', 'judge', 'check'):
                        with self.subTest(scene=scene, base=base, phase=phase):
                            with patch.multiple(RUN, ROOT=root, SOURCE=root / 'source',
                                                OUT=root / 'out', GROUP='test', SECONDS=1):
                                RUN.run(f'{base}-{scene}', phase)
                            directory = root / f'out/test/{base}-{scene}-{phase}'
                            command = json.loads((directory / 'done.json').read_text())['command']
                            self.assertFalse(any(arg.startswith('--instruction-bits') for arg in command))
                            self.assertFalse(any(arg.startswith(('x1=', 'x31=')) for arg in command))
                            self.assertIn(f'--clause={scene.split("-")[1].upper()}', command)
                            self.assertIn('--path-merging', command)
                            satp = {'sv39': '0x8000000000080200', 'sv48': '0x9000000000080200',
                                    'bare': '0x0000000000000000'}[scene.split('-')[0]]
                            self.assertIn(f'satp={satp}', command)
                            self.assertEqual('cur_privilege=Supervisor' in command, base == 'E0')

    def test_analysis_counts_actual_operand_registers_and_effective_addresses(self):
        for clause in ('LOAD', 'STORE'):
            with self.subTest(clause=clause), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary) / f'E0-sv39-{clause.lower()}-export'
                (directory / 'output').mkdir(parents=True)
                (directory / 'done.json').write_text(json.dumps(dict(
                    seconds=2, limit_seconds=10, timed_out=False, returncode=0,
                    max_rss_kib=2048, user_seconds=1, system_seconds=0.1)))
                merge = dict(attempts=10, successes=7, merge_enumeration=dict(truncated_paths=0))
                (directory / 'stderr.txt').write_text(
                    '[MERGE_STATS] ' + json.dumps(merge) + '\n[FORK_STATS] {"total": 3}\n')
                (directory / f'output/rv64_z{clause}.json').write_text(json.dumps(dict(
                    summary=dict(status='finished'), diagnostics=[], gen=[{}, {}])))
                names = (ANALYSIS.LOAD_FIELDS if clause == 'LOAD' else ANALYSIS.STORE_FIELDS)
                samples = []
                for index, (rs1, other) in enumerate(((0, 5), (31, 11), (5, 15))):
                    operands = (rs1, other) if clause == 'LOAD' else (other, rs1)
                    values = [dict(bits='111111111000'),
                              *(dict(bits=f'{value:05b}') for value in operands)]
                    if clause == 'LOAD':
                        values.append(dict(bool=False))
                    # 自由符号整数具体化后编码为 bits；固定参数保留 i64 编码。
                    width = 0 if index == 2 else 4
                    values.append(dict(i64='4') if index == 0 else dict(bits=f'{width:064b}'))
                    samples.append(dict(sample_id=index, path_signature=index // 2, class_id=0,
                        pre_registers={'$instruction': dict(ctor=clause, value=dict(struct=dict(zip(names, values)))),
                                       **({f'x{rs1}': dict(bits=f'{0x1000:064b}')} if rs1 else {})}))
                (directory / 'samples.jsonl').write_text(''.join(json.dumps(s) + '\n' for s in samples))
                (directory / 'resources.jsonl').write_text('{"seconds": 1, "VmRSS": 1024}\n')
                result = ANALYSIS.summarize(directory)
                self.assertEqual(result['register_distribution']['rs1'], {'x0': 1, 'x31': 1, 'x5': 1})
                self.assertEqual(result['register_distribution']['rd' if clause == 'LOAD' else 'rs2'],
                                 {'x5': 1, 'x11': 1, 'x15': 1})
                self.assertEqual(result['distinct_effective_addresses'], 2)
                self.assertEqual(result['effective_address_max'], '0xfffffffffffffff8')
                self.assertEqual(result['merge_success_rate'], 0.7)
                self.assertEqual(result['peak_sampled_vmrss_kib'], 1024)
                self.assertEqual(result['access_width_distribution'], {'4': 2, '0': 1})
                self.assertEqual(result['exported_samples'], 3)
                self.assertEqual(result['exported_classes'], 2)
                self.assertEqual(result['encoding_domain_samples'], 2)
                self.assertEqual(result['encoding_domain_register_distribution']['rs1'], {'x0': 1, 'x31': 1})

    def test_timeout_reports_unfinished_last_statistics_line(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / 'E0-sv39-load-export'
            directory.mkdir()
            (directory / 'done.json').write_text(json.dumps(dict(
                seconds=2.1, limit_seconds=2, timed_out=True, returncode=-9,
                max_rss_kib=1024, user_seconds=1, system_seconds=0.1)))
            (directory / 'stderr.txt').write_text(
                    '[MERGE_STATS_SNAPSHOT] {"attempts": 0, "successes": 0, "merge_enumeration": {"truncated_paths": 0}}\n'
                '[FORK_STATS_SNAPSHOT] {"total": 3}\n'
                '[FORK_STATS_SNAPSHOT] {"total":')
            result = ANALYSIS.summarize(directory)
            self.assertFalse(result['fully_converged'])
            self.assertEqual(result['incomplete_statistics_lines'], 1)
            self.assertFalse(result['statistics_final'])


if __name__ == '__main__':
    unittest.main()
