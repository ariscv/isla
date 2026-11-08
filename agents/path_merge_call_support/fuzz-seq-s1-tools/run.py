"""纯符号指令探索：复用路径合并与区域分支限制，记录预算及真实资源用量。"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import datetime
import json
import os
import signal
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT.parent / 'replay-p0/output/ecfg4b'
E2 = ROOT.parent / 'isla-sym-config/output/fuzz-step6a'
OUT = ROOT / 'output/fuzz-seq-s1-symbolic'
THREADS = int(os.environ.get('S1_THREADS', '32'))
ENUM_THREADS = int(os.environ.get('S1_ENUM_THREADS', '64' if THREADS == 64 else '16'))
CLASS_CAP = int(os.environ.get('S1_CLASS_CAP', '32'))
GROUP = os.environ.get('S1_GROUP', '')
SECONDS = int(os.environ.get('S1_SECONDS', '7200'))
assert 0 < SECONDS <= 7200
assert CLASS_CAP > 0


def prepare():
    OUT.mkdir(parents=True, exist_ok=True)
    for name in ['tmp', 'cache']:
        (OUT / name).mkdir(exist_ok=True)
    enumeration = (SOURCE / 'enumeration.toml').read_text()
    assert enumeration.count('strict = false') == 1
    source_cap = tomllib.loads(enumeration)['execution_limits']['merge_enumeration']['class_cap']
    cap_setting = f'class_cap = {source_cap}\n'
    assert enumeration.count(cap_setting) == 1
    # 每类配额只控制导出量，不固定任何指令字段；单代表不能展示类内寄存器多样性。
    enumeration = enumeration.replace(cap_setting, f'class_cap = {CLASS_CAP}\n')
    settings = ('strict = false\npath_merging = true\n'
                'on_limit_reached = "truncate"')
    # 按源码区域限制同一分支点在单路径上的重复分叉；不约束寄存器值域。
    # 若触发截断，必须在报告中标为探索不完整，不能当作收敛。
    regions = '''
[[execution_limits.branch_region_limits]]
file = "sys/vmem_tlb.sail"
start_line = 1
start_column = 0
end_line = 65535
end_column = 0
max_forks_per_branch = 4096

[[execution_limits.branch_region_limits]]
file = "sys/vmem_ptw.sail"
start_line = 1
start_column = 0
end_line = 65535
end_column = 0
max_forks_per_branch = 4096
'''
    ordered = enumeration.replace('strict = false', settings)
    (OUT / 'enumeration.toml').write_text(ordered + regions)
    for workers in [16, 32, 64]:
        threaded = ordered.replace('[execution_limits.merge_enumeration]',
                                   f'[execution_limits.merge_enumeration]\nenumeration_threads = {workers}')
        (OUT / f'enumeration-{workers}.toml').write_text(threaded + regions)
    (OUT / 'judge.toml').write_text('[execution_limits]\n' + settings + '\n' + regions)
    for base, path in [('E0', SOURCE / 'config-xs.toml'), ('E2', E2 / 'E2.toml')]:
        (OUT / f'{base}.toml').write_text(path.read_text())


def run(setting, phase):
    base, scene = setting.split('-', 1)
    mode, access = scene.split('-')
    assert base in ('E0', 'E2') and access in ('load', 'store')
    satp = {'bare': '0x0000000000000000', 'sv39': '0x8000000000080200',
            'sv48': '0x9000000000080200'}[mode]
    assert ENUM_THREADS in (16, 32, 64) and ENUM_THREADS <= THREADS
    directory = OUT / GROUP / f'{setting}-{phase}'
    directory.mkdir(parents=True, exist_ok=False)
    # 显式构造场景命令，旧运行记录不再作为输入；指令字段和通用寄存器由底层符号化。
    command = [str(ROOT / 'target/release/isarch'), '-D', 'sr', '--smt-timeout', '5',
               '-A', str(SOURCE / 'rv64d.ir'), '-C', str(OUT / f'{base}.toml'),
               '-T', str(THREADS), '--timeout', str(SECONDS),
               '--execution-limits-config', str(OUT / f'enumeration-{ENUM_THREADS}.toml'),
               '--path-merging']
    prestate = [f'satp={satp}', 'menvcfg={bits=0x0000000000000000}',
                'senvcfg={bits=0x0000000000000000}', 'mseccfg={bits=0x0000000000000000}']
    if base == 'E0':
        prestate += ['cur_privilege=Supervisor', 'mstatus={bits=0x0000000a00040000}']
    for value in prestate:
        command += ['--prestate', value]
    command += ['solve-state', f'--clause={access.upper()}']
    export = OUT / os.environ.get('S1_CORPUS_GROUP', GROUP) / f'{setting}-export'
    corpus = export / 'samples.jsonl'
    if phase in ('slots', 'judge', 'check'):
        index = command.index('--execution-limits-config')
        command[index + 1] = str(OUT / 'judge.toml')
        if phase in ('slots', 'judge'):
            command[command.index('solve-state')] = 'fuzz'
            command += ['--fuzz-mode', 'judge-only', '--fuzz-scenario', f'seq-s1-{setting}',
                        '--fuzz-corpus', str(corpus), '--fuzz-inputs', str(export / 'slot-proposals.jsonl') if phase == 'slots' else str(corpus),
                        '--fuzz-output', str(directory / 'fuzz'), '--fuzz-certify-all']
        else:
            command += ['--check-samples', str(corpus), '--check-samples-report', str(directory / 'check.json')]
    environment = os.environ.copy()
    environment.pop('LD_PRELOAD', None)
    environment.pop('ISLA_EXPORT_SAMPLES', None)
    environment.update(TMPDIR=str(OUT / 'tmp'), XDG_CACHE_HOME=str(OUT / 'cache'),
                       PYTHONDONTWRITEBYTECODE='1', ISLA_STATS='1', GIT_OPTIONAL_LOCKS='0')
    if phase == 'export':
        environment['ISLA_EXPORT_SAMPLES'] = str(directory / 'samples.jsonl')
    record = dict(command=command, cwd=str(directory), limit_seconds=SECONDS,
                  started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (directory / 'running.json').write_text(json.dumps(record, indent=2))
    started = time.monotonic()
    with (directory / 'stdout.txt').open('w') as stdout, (directory / 'stderr.txt').open('w') as stderr:
        process = subprocess.Popen(command, cwd=directory, env=environment, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        record['pid'] = process.pid
        (directory / 'running.json').write_text(json.dumps(record, indent=2))
        record['timed_out'] = False
        with (directory / 'resources.jsonl').open('w') as resources:
            next_sample = 0.0
            while True:
                child, status, usage = os.wait4(process.pid, os.WNOHANG)
                if child:
                    process.returncode = os.waitstatus_to_exitcode(status)
                    break
                elapsed = time.monotonic() - started
                if elapsed >= SECONDS and not record['timed_out']:
                    os.killpg(process.pid, signal.SIGKILL)
                    record['timed_out'] = True
                if elapsed >= next_sample:
                    try:
                        status_text = Path(f'/proc/{process.pid}/status').read_text()
                    except FileNotFoundError:
                        continue  # 进程刚退出，下一次 wait4 收取实际资源用量。
                    memory = {line.split(':')[0]: int(line.split()[1]) for line in status_text.splitlines()
                              if line.startswith(('VmRSS:', 'VmHWM:'))}
                    resources.write(json.dumps(dict(seconds=elapsed, **memory)) + '\n')
                    resources.flush()
                    next_sample = elapsed + 1
                time.sleep(0.2)
        record.update(returncode=process.returncode, max_rss_kib=usage.ru_maxrss,
                      user_seconds=usage.ru_utime, system_seconds=usage.ru_stime)
    record['seconds'] = time.monotonic() - started
    (directory / 'done.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
    print(setting, phase, record['returncode'], round(record['seconds'], 3),
          '超时' if record['timed_out'] else '结束', flush=True)


if __name__ == '__main__':
    phase = sys.argv[1]
    if phase == 'prepare':
        prepare()
    else:
        assert phase in ('export', 'slots', 'judge', 'check')
        settings = sys.argv[2:]
        assert settings and THREADS in (32, 64)
        assert THREADS == 32 or len(settings) == 1
        with ThreadPoolExecutor(max_workers=4 if THREADS == 32 else 1) as pool:
            list(pool.map(lambda setting: run(setting, phase), settings))
