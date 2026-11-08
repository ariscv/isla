"""第 6a 步复现：只写本工作树，四路各 32 线程，每次外限 900 秒。"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import datetime
import json
import os
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT.parent / 'replay-p0/output/ecfg4b'
OUT = ROOT / 'output/fuzz-step6a' / os.environ.get('FUZZ_STEP6A_GROUP', '')
THREADS = int(os.environ.get('FUZZ_STEP6A_THREADS', '32'))
assert THREADS in (32, 64)
SCENES = ['sv39-load', 'sv39-store', 'sv48-load', 'sv48-store']


def prepare():
    OUT.mkdir(exist_ok=True, parents=True)
    original = (SOURCE / 'config-xs.toml').read_text()
    (OUT / 'E0.toml').write_text(original)
    default = 'mstatus = "{ bits = 0x0000000000000600 }"\n'
    assert original.count(default) == 1
    config = original.replace(default, '')
    config += '''\n[symbolic_registers]
cur_privilege = { allowed = ["User", "Supervisor"] }

[symbolic_registers.mstatus]
pin_mask = "0xfffffffffff3ffff"
pin_value = "0x0000000a00000000"
'''
    (OUT / 'E2.toml').write_text(config)


def run(scene, phase):
    is_e0 = phase in ('E0', 'baseline')
    name = ('E0-before' if phase == 'baseline' else 'E0-sv39-load') if is_e0 else f'{scene}-{phase}'
    directory = OUT / name
    directory.mkdir(exist_ok=False)
    command = json.loads((SOURCE / scene / 'done.json').read_text())['command'].copy()
    command[0] = str(ROOT.parent / 'isla-fuzz/target/release/isarch') if phase == 'baseline' else str(ROOT / 'target/release/isarch')
    command[command.index('-C') + 1] = str(OUT / ('E0.toml' if is_e0 else 'E2.toml'))
    assert command[command.index('-T') + 1] == '32'
    command[command.index('-T') + 1] = str(THREADS)
    if not is_e0:
        for value in ['cur_privilege=Supervisor', 'mstatus={bits=0x0000000a00040000}']:
            index = command.index(value)
            del command[index - 1:index + 1]
    corpus = OUT / f'{scene}-export/samples.jsonl'
    if phase in ('judge', 'check'):
        index = command.index('--execution-limits-config')
        del command[index:index + 2]
        if phase == 'judge':
            command[command.index('solve-state')] = 'fuzz'
            command += ['--fuzz-mode', 'judge-only', '--fuzz-scenario', f'ecfg4b-E2-{scene}',
                        '--fuzz-corpus', str(corpus), '--fuzz-inputs', str(corpus),
                        '--fuzz-output', str(directory / 'fuzz'), '--fuzz-certify-all']
        else:
            command += ['--check-samples', str(corpus), '--check-samples-report', str(directory / 'check.json')]
    environment = os.environ.copy()
    environment.pop('LD_PRELOAD', None)
    environment.pop('ISLA_EXPORT_SAMPLES', None)
    environment.update(TMPDIR=str(OUT), XDG_CACHE_HOME=str(OUT / 'cache'),
                       PYTHONDONTWRITEBYTECODE='1', ISLA_STATS='1', GIT_OPTIONAL_LOCKS='0')
    if is_e0 or phase == 'export':
        environment['ISLA_EXPORT_SAMPLES'] = str(directory / 'samples.jsonl')
    record = dict(command=command, cwd=str(directory), started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  environment={key: environment[key] for key in ['TMPDIR', 'XDG_CACHE_HOME', 'PYTHONDONTWRITEBYTECODE', 'ISLA_STATS']})
    (directory / 'running.json').write_text(json.dumps(record, indent=2))
    started = time.monotonic()
    with (directory / 'stdout.txt').open('w') as stdout, (directory / 'stderr.txt').open('w') as stderr:
        process = subprocess.Popen(command, cwd=directory, env=environment, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            record.update(returncode=process.wait(timeout=900), timed_out=False)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            record.update(returncode=process.wait(), timed_out=True)
    record['seconds'] = time.monotonic() - started
    (directory / 'done.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
    print(name, record['returncode'], round(record['seconds'], 3), '超时' if record['timed_out'] else '结束', flush=True)
    return record


if __name__ == '__main__':
    phase = sys.argv[1]
    if phase == 'prepare':
        prepare()
    elif phase in ('E0', 'baseline'):
        run('sv39-load', phase)
    elif phase in ('export', 'judge', 'check'):
        scenes = sys.argv[2:] or SCENES
        assert THREADS == 32 or len(scenes) == 1, '64 线程只允许单场景串行运行'
        with ThreadPoolExecutor(max_workers=4 if THREADS == 32 else 1) as pool:
            list(pool.map(lambda scene: run(scene, phase), scenes))
    else:
        raise ValueError(phase)
