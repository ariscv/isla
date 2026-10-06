#!/usr/bin/python3
"""solve 清理回归：仅使用临时目录和本测试创建的进程。"""
import importlib.util
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from types import SimpleNamespace

SCRIPTS = Path(__file__).resolve().parent
SYSTEM_PYTHON = Path('/usr/bin/python3')
DEFAULT_PYTHON = Path(shutil.which('python3'))
EVIDENCE = Path(os.environ['SOLVE_CLEANUP_TEST_EVIDENCE']).resolve() if 'SOLVE_CLEANUP_TEST_EVIDENCE' in os.environ else None
WORKER = r'''#!/usr/bin/python3
import json, os, signal, subprocess, sys, time
from pathlib import Path
clause = next((a.split('=', 1)[1] for a in sys.argv if a.startswith('--clause=')), 'direct')
cfg = json.loads(Path('worker.json').read_text())[clause]
mode = cfg['mode']
if mode == 'tree':
    subprocess.Popen([sys.executable, __file__, '--clause=grandchild'])
if mode in ('stubborn', 'grandchild'):
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
if mode == 'handler':
    signal.signal(signal.SIGTERM, lambda sig, frame: sys.exit(0))
Path(clause + '.pid').write_text(json.dumps({'pid':os.getpid(), 'pgid':os.getpgrp()}))
print('worker-start-' + clause, flush=True)
if mode == 'exit':
    time.sleep(cfg.get('delay', 0))
    sys.exit(cfg['code'])
while True:
    time.sleep(.02)
'''


def live(pid):
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()[0] != 'Z'
    except FileNotFoundError:
        return False


class ProcessTests(unittest.TestCase):
    def setUp(self):
        if not (SCRIPTS / 'solve_process.py').exists():
            self.fail('尚无任务归属清理实现')
        self.temp = tempfile.TemporaryDirectory(prefix='solve-cleanup-test-')
        self.base = Path(self.temp.name)
        self.processes = []
        self.fds = []

    def tearDown(self):
        # 所有清理均针对本测试事先持有的精确句柄。
        for fd in self.fds:
            try:
                signal.pidfd_send_signal(fd, signal.SIGKILL)
            except ProcessLookupError:
                pass
            os.close(fd)
        for p in self.processes:
            if p.poll() is None:
                p.kill()
            p.wait(timeout=3)
            if p.stdout:
                p.stdout.close()
        if EVIDENCE:
            destination = EVIDENCE / self.id().rsplit('.', 1)[1]
            for stage in self.base.iterdir():
                if (stage / 'output').exists():
                    shutil.copytree(stage / 'output', destination / stage.name, dirs_exist_ok=True)
        self.temp.cleanup()

    def stage(self, name='stage', cases=None):
        stage = self.base / name
        (stage / 'target/release').mkdir(parents=True)
        (stage / 'scripts').mkdir()
        for source in ('run.mk', 'run_ctrl_c.mk', 'solve_process.py'):
            shutil.copyfile(SCRIPTS / source, stage / 'scripts' / source)
        worker = stage / 'target/release/isarch'
        worker.write_text(WORKER)
        worker.chmod(0o755)
        (stage / 'worker.json').write_text(json.dumps(cases or {'direct': {'mode': 'handler'}}))
        return stage

    def spawn(self, argv, stage):
        p = subprocess.Popen(argv, cwd=stage, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
        self.processes.append(p)
        self.fds.append(os.pidfd_open(p.pid))
        return p

    def ready(self, stage, clause='direct'):
        limit = time.monotonic() + 5
        path = stage / (clause + '.pid')
        while time.monotonic() < limit:
            if path.exists():
                try:
                    info = json.loads(path.read_text())
                except json.JSONDecodeError:
                    time.sleep(.01)
                    continue
                self.fds.append(os.pidfd_open(info['pid']))
                return info
            time.sleep(.01)
        self.fail('等待测试子进程超时')

    def supervised(self, stage, duration='10s', clause='direct', python=SYSTEM_PYTHON):
        return self.spawn([str(python), 'scripts/solve_process.py', 'run', '--clause', clause,
                           '--cleanup-grace', '.2', '--', 'timeout', '--signal=TERM',
                           '--kill-after=.2s', duration, './target/release/isarch',
                           '--clause=' + clause], stage)

    def finish(self, p, code, stage, clause='direct'):
        output, _ = p.communicate(timeout=5)
        self.assertEqual(p.returncode, code, output)
        events = list((stage / 'output/process').glob('*.json'))
        reports = [json.loads(path.read_text()) for path in events]
        report = next(r for r in reports if r['clause'] == clause)
        self.assertEqual(report['return_code'], code)
        return report

    def test_normal_nonzero_and_timeout(self):
        for mode, code, duration in [('exit', 0, '10s'), ('exit', 7, '10s'),
                                     ('exit', 15, '10s'), ('handler', 124, '.15s')]:
            with self.subTest(code=code):
                stage = self.stage(str(code), {'direct': {'mode': mode, 'code': code}})
                p = self.supervised(stage, duration)
                report = self.finish(p, code, stage)
                self.assertEqual(report['supervisor_signals'], [])
                self.assertEqual(report['child_wait']['exit_code'], code)
                status = 'intime' if code == 0 else 'timeout' if code == 124 else 'failed'
                self.assertIn('direct', (stage / f'output/status.{status}.log').read_text())

    def test_timeout_signal_semantics_match_direct(self):
        # uutils 与 GNU 对 signal termination 的包装码可能不同，直接实测对照。
        for wrapper in (False, True):
            stage = self.stage(str(wrapper), {'direct': {'mode': 'ordinary'}})
            p = self.supervised(stage) if wrapper else self.spawn(
                ['timeout', '--signal=TERM', '--kill-after=.2s', '10s', './target/release/isarch'], stage)
            worker = self.ready(stage)
            os.kill(worker['pid'], signal.SIGTERM)
            output, _ = p.communicate(timeout=5)
            if not wrapper:
                direct_code = p.returncode
            else:
                self.assertEqual(p.returncode, direct_code, output)

    def test_int_term_repeated_and_stubborn_descendants(self):
        for mode in ('handler', 'stubborn', 'tree'):
            for sig in (signal.SIGINT, signal.SIGTERM):
                with self.subTest(mode=mode, signal=sig):
                    stage = self.stage(f'{mode}-{sig}', {'direct': {'mode': mode},
                                                        'grandchild': {'mode': 'grandchild'}})
                    p = self.supervised(stage)
                    worker = self.ready(stage)
                    children = [worker]
                    if mode == 'tree':
                        children.append(self.ready(stage, 'grandchild'))
                    os.kill(p.pid, sig)
                    time.sleep(.01)
                    if p.poll() is None:
                        os.kill(p.pid, sig)
                    report = self.finish(p, 128 + sig, stage)
                    self.assertEqual(report['supervisor_signals'][0], sig)
                    self.assertTrue(all(not live(c['pid']) for c in children))

    def test_natural_parent_exit_cleans_stubborn_grandchild(self):
        stage = self.stage(cases={'direct': {'mode': 'tree'}, 'grandchild': {'mode': 'grandchild'}})
        p = self.supervised(stage)
        parent = self.ready(stage)
        child = self.ready(stage, 'grandchild')
        os.kill(parent['pid'], signal.SIGTERM)
        report = self.finish(p, 15, stage)
        self.assertEqual(report['supervisor_signals'], [])
        self.assertFalse(live(child['pid']))

    def test_other_stage_and_parallel_sibling_survive(self):
        stage = self.stage('same', {'first': {'mode': 'stubborn'}, 'second': {'mode': 'handler'}})
        other = self.stage('other')
        first = self.supervised(stage, clause='first')
        second = self.supervised(stage, clause='second')
        sentinel = self.spawn(['./target/release/isarch'], other)
        first_worker = self.ready(stage, 'first')
        second_worker = self.ready(stage, 'second')
        sentinel_worker = self.ready(other)
        os.kill(first.pid, signal.SIGTERM)
        self.finish(first, 143, stage, 'first')
        self.assertFalse(live(first_worker['pid']))
        self.assertTrue(live(second_worker['pid']))
        self.assertTrue(live(sentinel_worker['pid']))
        os.kill(second.pid, signal.SIGTERM)
        self.finish(second, 143, stage, 'second')
        sentinel.terminate()
        sentinel.wait(timeout=3)

    def test_manual_explicit_pid_and_invalid_ownership(self):
        stage = self.stage()
        other = self.stage('other')
        p = self.supervised(stage)
        worker = self.ready(stage)
        for cwd, pid in [(stage, None), (other, p.pid), (stage, worker['pid']), (stage, 99999999)]:
            args = ['/usr/bin/python3', str(stage / 'scripts/solve_process.py'), 'kill']
            if pid:
                args += ['--pid', str(pid)]
            result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertTrue(live(worker['pid']))
        result = subprocess.run(['/usr/bin/python3', 'scripts/solve_process.py', 'kill', '--pid', str(p.pid)],
                                cwd=stage, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.finish(p, 143, stage)
        result = subprocess.run(['/usr/bin/python3', 'scripts/solve_process.py', 'kill', '--pid', str(p.pid)],
                                cwd=stage, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0, '已退出的 PID 必须拒绝')

    def test_default_and_system_python_run_kill_combinations(self):
        self.assertNotEqual(DEFAULT_PYTHON.resolve(), SYSTEM_PYTHON.resolve(),
                            '本机 PATH Python 必须与系统 Python 不同，才能验证解释器兼容')
        actual = subprocess.run([str(DEFAULT_PYTHON), '-c',
                                 'import os, signal; print(hasattr(os, "pidfd_open"), '
                                 'hasattr(signal, "pidfd_send_signal"))'],
                                capture_output=True, text=True, check=True)
        self.assertEqual(actual.stdout.strip(), 'False True')
        for runner in (DEFAULT_PYTHON, SYSTEM_PYTHON):
            for killer in (DEFAULT_PYTHON, SYSTEM_PYTHON):
                with self.subTest(runner=str(runner), killer=str(killer)):
                    stage = self.stage(f'{runner.name}-{killer.name}-{len(self.processes)}')
                    p = self.supervised(stage, python=runner)
                    worker = self.ready(stage)
                    self.assertEqual(Path(f'/proc/{p.pid}/exe').resolve(), SYSTEM_PYTHON.resolve())
                    result = subprocess.run([str(killer), 'scripts/solve_process.py', 'kill',
                                             '--pid', str(p.pid)], cwd=stage,
                                            capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.finish(p, 143, stage)
                    self.assertFalse(live(worker['pid']))

    def test_manual_wrong_script_and_missing_pidfd_capability(self):
        stage = self.stage()
        other_script = stage / 'scripts' / 'other_process.py'
        shutil.copyfile(stage / 'scripts' / 'solve_process.py', other_script)
        p = self.spawn([str(SYSTEM_PYTHON), str(other_script), 'run', '--clause', 'direct',
                        '--cleanup-grace', '.2', '--', 'timeout', '--signal=TERM',
                        '--kill-after=.2s', '10s', './target/release/isarch',
                        '--clause=direct'], stage)
        worker = self.ready(stage)
        rejected = subprocess.run([str(DEFAULT_PYTHON), 'scripts/solve_process.py', 'kill',
                                   '--pid', str(p.pid)], cwd=stage, capture_output=True, text=True)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertTrue(live(worker['pid']))
        os.kill(p.pid, signal.SIGTERM)
        self.finish(p, 143, stage)

        spec = importlib.util.spec_from_file_location('solve_process_for_test', SCRIPTS / 'solve_process.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        args = SimpleNamespace(pid=os.getpid())
        for owner, name in ((os, 'pidfd_open'), (signal, 'pidfd_send_signal')):
            original = getattr(owner, name)
            delattr(owner, name)
            try:
                with self.subTest(missing=name), self.assertRaisesRegex(RuntimeError, 'pidfd'):
                    module.stop(args)
            finally:
                setattr(owner, name, original)

    def test_manual_make_targets(self):
        stage = self.stage()
        p = self.supervised(stage)
        self.ready(stage)
        refused = subprocess.run(['make', '-f', 'scripts/run.mk', 'solve-kill'], cwd=stage,
                                 capture_output=True, text=True)
        self.assertNotEqual(refused.returncode, 0)
        stopped = subprocess.run(['make', '-f', 'scripts/run.mk', 'kill-isarch', f'SOLVE_PID={p.pid}'],
                                 cwd=stage, capture_output=True, text=True)
        self.assertEqual(stopped.returncode, 0, stopped.stderr)
        self.finish(p, 143, stage)

    def test_actual_make_parallel_signal_and_logs(self):
        stage = self.stage(cases={'TESTA': {'mode': 'handler'}, 'TESTB': {'mode': 'handler'}})
        p = self.spawn(['make', '-f', 'scripts/run.mk', '-o', 'build-isarch', '-j2',
                        'solve-TESTA', 'solve-TESTB', 'OUTER_TIMEOUT=10s'], stage)
        first, second = self.ready(stage, 'TESTA'), self.ready(stage, 'TESTB')
        # 只中断第一个 recipe 的监督器，make 的另一个已启动 job 必须继续。
        owner = int(Path(f'/proc/{first["pid"]}/stat').read_text().rsplit(') ', 1)[1].split()[1])
        owner = int(Path(f'/proc/{owner}/stat').read_text().rsplit(') ', 1)[1].split()[1])
        os.kill(owner, signal.SIGTERM)
        limit = time.monotonic() + 3
        while live(first['pid']) and time.monotonic() < limit:
            time.sleep(.01)
        self.assertFalse(live(first['pid']))
        self.assertTrue(live(second['pid']))
        os.kill(second['pid'], signal.SIGTERM)
        output, _ = p.communicate(timeout=5)
        self.assertEqual(p.returncode, 2, output)
        self.assertIn('TESTA failed (143)', (stage / 'output/status.failed.log').read_text())
        for name in ('TESTA', 'TESTB'):
            self.assertIn('worker-start-' + name, (stage / f'output/log/{name}.log').read_text())

    def test_make_interrupt_forwarding(self):
        for sig in (signal.SIGINT, signal.SIGTERM):
            stage = self.stage(str(sig), {'TEST': {'mode': 'handler'}})
            p = self.spawn(['make', '-f', 'scripts/run.mk', '-o', 'build-isarch',
                            'solve-TEST', 'OUTER_TIMEOUT=10s'], stage)
            child = self.ready(stage, 'TEST')
            os.killpg(p.pid, sig)
            p.communicate(timeout=5)
            self.assertFalse(live(child['pid']))


class ContractTests(unittest.TestCase):
    def test_no_global_name_kill(self):
        for name in ('run.mk', 'run_ctrl_c.mk'):
            active = '\n'.join(line for line in (SCRIPTS / name).read_text().splitlines()
                               if not line.lstrip().startswith('#'))
            self.assertNotIn('pkill', active, name)
            self.assertNotIn('killall', active, name)


if __name__ == '__main__':
    unittest.main()
