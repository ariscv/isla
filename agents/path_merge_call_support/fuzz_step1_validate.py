#!/usr/bin/env python3
"""第 1 步的受控测量与逐字段对拍，复用 M0 的数据与检查。"""
import argparse
import os
from pathlib import Path
import subprocess
import time

import fuzz_m0_validate as m0

BASE = m0.ROOT / 'output/fuzz-step1'


def run(name, threads, fast=False, diagnostic=None, inputs=None):
    folder = BASE / name
    folder.mkdir(parents=True, exist_ok=False)
    argv = m0.command(threads, folder)
    if inputs:
        argv[argv.index('--judge-resident') + 1] = str(inputs)
    if fast:
        argv.insert(argv.index('solve-state'), '--judge-resident-fast')
    env = os.environ.copy()
    env.update(TMPDIR=str(BASE / 'tmp'), XDG_CACHE_HOME=str(BASE / 'cache'))
    env.pop('LD_PRELOAD', None)
    if diagnostic:
        env['LD_PRELOAD'] = str(diagnostic)
        env['ISLA_LOCK_LOG'] = str(folder / 'locks.jsonl')
    start = time.monotonic()
    m0.write_json(folder / 'running.json', {'command': argv, 'cwd': str(folder)})
    with (folder / 'stdout.txt').open('w') as out, (folder / 'stderr.txt').open('w') as err:
        result = subprocess.run(['/usr/bin/time', '-v', '-o', str(folder / 'time.txt'), *argv],
                                cwd=folder, env=env, stdout=out, stderr=err, timeout=1200)
    m0.write_json(folder / 'done.json', {'command': argv, 'cwd': str(folder),
                                      'returncode': result.returncode, 'seconds': time.monotonic() - start})
    assert result.returncode in (0, 1), result.returncode


def verify(name, threads):
    # M0 的核对包含全部样本字段和旧独立 judge 真值。
    previous = m0.OUT
    m0.OUT = BASE
    target = BASE / f't{threads}'
    assert not target.exists()
    target.symlink_to(name, target_is_directory=True)
    for source in ['input-map.json', 'inputs.jsonl']:
        path = BASE / source
        if not path.exists():
            path.symlink_to(previous / source)
    try:
        m0.verify(threads)
    finally:
        target.unlink()
        m0.OUT = previous


def compare(left, right):
    def rows(name):
        result = {}
        for row in m0.read_rows(BASE / name / 'judged.jsonl'):
            row.pop('guard_order')
            row.pop('guard_assignment')
            assert row['sample_id'] not in result
            result[row['sample_id']] = row
        return result
    a, b = rows(left), rows(right)
    differences = [sid for sid in sorted(a.keys() | b.keys()) if a.get(sid) != b.get(sid)]
    m0.write_json(BASE / f'compare-{left}-{right}.json', {'left': left, 'right': right,
                  'left_count': len(a), 'right_count': len(b), 'differences': differences})
    assert len(a) == len(b) == 1380 and not differences


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'verify', 'compare'])
    parser.add_argument('--name', required=True)
    parser.add_argument('--threads', type=int, choices=[1, 32, 64], default=32)
    parser.add_argument('--fast', action='store_true')
    parser.add_argument('--diagnostic', type=Path)
    parser.add_argument('--inputs', type=Path)
    parser.add_argument('--other')
    args = parser.parse_args()
    if args.action == 'run':
        run(args.name, args.threads, args.fast, args.diagnostic, args.inputs)
    elif args.action == 'verify':
        verify(args.name, args.threads)
    else:
        compare(args.name, args.other)
