#!/usr/bin/env python3
"""沿用 ecfg4b 探索参数，运行单场景 campaign；只写指定的新输出目录。"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--scenario', required=True, choices=['sv39-store', 'sv39-load', 'sv48-store', 'sv48-load'])
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--source', type=Path, default=Path('../replay-p0/output'))
    parser.add_argument('--budget', type=int, default=300)
    parser.add_argument('--threads', type=int, choices=[1, 32], default=32)
    parser.add_argument('--random-seed', type=int, default=42)
    parser.add_argument('--executor', choices=['model', 'difftest'], default='model')
    parser.add_argument('--certify-all', action='store_true')
    args, extra = parser.parse_known_args()
    root, output, source = Path.cwd(), args.output.resolve(), args.source.resolve()
    output.mkdir(parents=True, exist_ok=False)
    argv = json.loads((source / 'ecfg4b' / (args.scenario + '-j1') / 'done.json').read_text())['command']
    argv[0] = str(root / 'target/release/isarch')
    for flag in ['--check-samples', '--check-samples-report']:
        index = argv.index(flag)
        del argv[index:index+2]
    argv[argv.index('solve-state')] = 'fuzz'
    argv[argv.index('-T')+1] = str(args.threads)
    argv += ['--fuzz-mode', 'campaign', '--fuzz-scenario', args.scenario,
             '--fuzz-corpus', str(source / 'ecfg4b' / args.scenario / 'samples.jsonl'),
             '--fuzz-mutations', str(source / 'fuzz-p1b' / args.scenario / 'mutations.json'),
             '--fuzz-output', str(output / 'fuzz'), '--fuzz-budget', str(args.budget),
             '--fuzz-seed', str(args.random_seed), '--executor', args.executor]
    if args.certify_all:
        argv.append('--fuzz-certify-all')
    argv += extra
    environment = os.environ.copy()
    environment.update(PYTHONDONTWRITEBYTECODE='1', TMPDIR=str(output))
    started = time.monotonic()
    with (output / 'stdout.log').open('w') as stdout, (output / 'stderr.log').open('w') as stderr:
        process = subprocess.Popen(argv, cwd=output, env=environment, stdout=stdout, stderr=stderr, start_new_session=True)
        def cancel(signum, frame):
            os.killpg(process.pid, signal.SIGTERM)
        previous = {sig: signal.signal(sig, cancel) for sig in (signal.SIGINT, signal.SIGTERM)}
        try:
            code = process.wait(timeout=2400)
        except BaseException:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise
        finally:
            for sig, handler in previous.items():
                signal.signal(sig, handler)
    # 检查本次运行的 Python、emu 及 fork 的 NEMU；不碰其他人的进程。
    remaining = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid():
            continue
        try:
            command = (entry / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if str(output) in command and ('paging_worker.py' in command or 'program.elf' in command):
            remaining.append(dict(pid=int(entry.name), command=command))
    (output / 'remaining-processes.json').write_text(json.dumps(remaining, ensure_ascii=False, indent=2) + '\n')
    (output / 'done.json').write_text(json.dumps(dict(command=argv, returncode=code, seconds=time.monotonic()-started), ensure_ascii=False, indent=2) + '\n')
    assert not remaining, remaining
    assert (output / 'fuzz/timing.json').exists(), '必须保存完整退出与 fuzz 结果，不能只接受退出码'
    print(args.scenario, code, round(time.monotonic()-started, 3), flush=True)


if __name__ == '__main__':
    main()
