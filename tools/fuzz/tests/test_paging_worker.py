"""薄入口的契约；重放与窄规则必须调用现有模块。"""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

PATH = Path(__file__).resolve().parents[1] / 'paging_worker.py'
spec = importlib.util.spec_from_file_location('paging_worker', PATH)
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)


class WorkerTests(unittest.TestCase):
    def test_three_way_result_calls_existing_narrow_rule(self):
        fuzz = Mock()
        fuzz.observe_run.return_value = dict(xs_cause=7, nemu_cause=15, isla_consistent_side='nemu')
        fuzz.MismatchTable.return_value.record.return_value = dict(filtered=True, known_rule='xs_leaf_ppn_af_over_permission_pf', group_key={'ptes': []})
        case = dict(expected={'cause': 15}, sample={'sample_id': 4})
        result = dict(agree=False, bucket='xs!=nemu', abort=True, log='difftest.log', elf_sha256='recorded')
        actual = worker.finish_result(case, result, [], '日志', fuzz)
        self.assertEqual((actual['isla_cause'], actual['xs_cause'], actual['nemu_cause']), (15, 7, 15))
        self.assertTrue(actual['mismatch']['filtered'])
        fuzz.observe_run.assert_called_once_with(case, result, [], '日志')
        fuzz.MismatchTable.return_value.record.assert_called_once()

    def test_agreement_requires_all_three_sides(self):
        fuzz = Mock()
        fuzz.observe_run.return_value = dict(xs_cause=0, nemu_cause=0, isla_consistent_side='both')
        actual = worker.finish_result(dict(expected={'cause': 0}, sample={'sample_id': 1}), dict(agree=True, bucket='agree'), [], '日志', fuzz)
        self.assertTrue(actual['agree'])
        self.assertEqual(actual['mismatch'], dict(filtered=False, known_rule=None, group_key=None))
        fuzz.MismatchTable.return_value.record.assert_not_called()

    def test_timeout_does_not_invent_causes(self):
        fuzz = Mock()
        actual = worker.finish_result(dict(expected={'cause': 13}, sample={'sample_id': 1}), dict(agree=False, bucket='timeout'), [], '', fuzz)
        self.assertIsNone(actual['xs_cause'])
        self.assertIsNone(actual['nemu_cause'])
        fuzz.observe_run.assert_not_called()

    def test_cleanup_reaps_emu_session_and_native_fork(self):
        import json
        import os
        import subprocess
        import sys
        import time
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'children.json'
            script = "import os,sys,time,json;child=os.fork();(time.sleep(300) if child==0 else (open(sys.argv[1],'w').write(json.dumps([os.getpid(),child])),time.sleep(300)))"
            with self.assertRaises(InterruptedError):
                with worker.managed_children():
                    subprocess.Popen([sys.executable, '-c', script, str(path)], start_new_session=True)
                    started = time.monotonic()
                    while not path.exists():
                        self.assertLess(time.monotonic()-started, 5)
                        time.sleep(.01)
                    time.sleep(.02)
                    pids = json.loads(path.read_text())
                    raise InterruptedError('测试取消')
            for pid in pids:
                with self.assertRaises(ProcessLookupError):
                    os.kill(pid, 0)

    def test_worker_failure_writes_result_and_keeps_failure(self):
        import json
        import sys
        with tempfile.TemporaryDirectory() as directory:
            args = ['paging_worker.py', '--input', '缺少输入', '--profile', '平台', '--lock', '锁', '--files', '工具路径', '--observer', '观察器', '--output', directory]
            with patch.object(sys, 'argv', args), patch.object(worker, 'run', side_effect=ValueError('认证输入不满足平台约束')):
                with self.assertRaises(ValueError):
                    worker.main()
            result = json.loads((Path(directory) / 'result.json').read_text())
            self.assertEqual(result['bucket'], 'worker-error')
            self.assertFalse(result['agree'])
            self.assertIn('认证输入不满足平台约束', result['reason'])

    def test_signal_during_spawn_does_not_lose_child_registration(self):
        import os
        import signal
        import subprocess
        events = []
        class FakePopen:
            def __init__(self, **kwargs):
                os.kill(os.getpid(), signal.SIGTERM)
            def poll(self):
                return None
            def kill(self):
                events.append('kill')
            def wait(self):
                events.append('wait')
        with patch.object(subprocess, 'Popen', FakePopen):
            with self.assertRaises(InterruptedError):
                with worker.managed_children():
                    subprocess.Popen()
        self.assertEqual(events, ['kill', 'wait'])
