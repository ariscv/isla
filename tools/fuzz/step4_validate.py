#!/usr/bin/env python3
"""第 4 步验收驱动：准备输入、当前模型认证、限八路真实重放。"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import threading
import time

SCENES = ('sv39-store', 'sv39-load', 'sv48-store', 'sv48-load')


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def prepare(root, source, output):
    output.mkdir(parents=True, exist_ok=False)
    manifest = []
    for scene in SCENES:
        folder = output / scene
        folder.mkdir()
        corpus = [json.loads(line) for line in (source / 'ecfg4b' / scene / 'samples.jsonl').read_text().splitlines()]
        selected = random.Random(20261108).sample(corpus, 50)
        records = [dict(kind='normal', source_id=s['sample_id']) for s in selected]
        groups = json.loads((source / 'fuzz-p1b/reported-xs-rule' / scene / 'mismatches.json').read_text())['groups']
        mutants = {s['sample_id']: s for s in map(json.loads, (root / 'output/fuzz-step2/replay' / scene / 'fuzz/classified.jsonl').read_text().splitlines())}
        for group in groups:
            index = int(group['representative'].rsplit('-', 1)[1])
            selected.append(mutants[index])
            records.append(dict(kind='known', source_id=index, expected=group['key']))
        for index, (sample, record) in enumerate(zip(selected, records)):
            sample['sample_id'] = index
            manifest.append(dict(scene=scene, sample_id=index, **record))
        (folder / 'selected.jsonl').write_text(''.join(json.dumps(s, ensure_ascii=False) + '\n' for s in selected))
    write(output / 'manifest.json', manifest)


def certify(root, output, workers):
    assert 1 <= workers <= 4
    def task(scene):
        folder = output / scene
        argv = json.loads((root / 'output/fuzz-step2/replay' / scene / 'done.json').read_text())['command']
        argv[0] = str(root / 'target/release/isarch')
        for flag, value in [('--fuzz-mode', 'judge-only'), ('--fuzz-output', str(folder / 'certified'))]:
            argv[argv.index(flag) + 1] = value
        argv += ['--fuzz-inputs', str(folder / 'selected.jsonl'), '--fuzz-certify-all']
        assert argv[argv.index('-T') + 1] == '32'
        started = time.monotonic()
        with (folder / 'certify.stdout').open('w') as stdout, (folder / 'certify.stderr').open('w') as stderr:
            process = subprocess.Popen(argv, cwd=folder, stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                code = process.wait(timeout=2400)
            except BaseException:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise
        write(folder / 'certify.done.json', dict(command=argv, returncode=code, seconds=time.monotonic()-started))
        before = [json.loads(line) for line in (folder / 'selected.jsonl').read_text().splitlines()]
        after = [json.loads(line) for line in (folder / 'certified/classified.jsonl').read_text().splitlines()]
        assert len(before) == len(after)
        for left, right in zip(before, after):
            for key in ('sample_id', 'pre_registers', 'pre_memory', 'post_registers', 'post_memory', 'isa_state', 'result', 'ret_val'):
                assert left[key] == right[key], (scene, left['sample_id'], key)
        print('认证完成', scene, len(after), flush=True)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        list(pool.map(task, SCENES))


def replay(root, source, output):
    manifest = json.loads((output / 'manifest.json').read_text())
    active = set()
    guard = threading.Lock()
    stop = threading.Event()
    def cancel(signum, frame):
        stop.set()
        with guard:
            for process in active:
                try: os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError: pass
        raise InterruptedError(f'收到取消信号 {signum}')
    previous = {sig: signal.signal(sig, cancel) for sig in (signal.SIGINT, signal.SIGTERM)}
    def task(record):
        assert not stop.is_set(), '验收已取消'
        scene, index = record['scene'], record['sample_id']
        directory = output / scene / f"{record['kind']}-{index:03}"
        directory.mkdir()
        argv = ['python3', str(root / 'tools/fuzz/paging_worker.py'), '--input', str(output / scene / 'certified/classified.jsonl'), '--sample-id', str(index), '--output', str(directory)]
        for flag, name in [('profile','profile.json'), ('lock','profile.lock.json'), ('files','files.json'), ('observer','nemu_native_observer.so')]:
            argv += ['--' + flag, str(source / 'ecfg4b' / name)]
        with (directory / 'worker.log').open('w') as log:
            process = subprocess.Popen(argv, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            with guard: active.add(process)
            try:
                assert process.wait(timeout=150) == 0, (record, directory / 'worker.log')
            except BaseException:
                stop.set()
                try: os.killpg(process.pid, signal.SIGTERM)
                except ProcessLookupError: pass
                try: process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise
            finally:
                with guard: active.remove(process)
        result = json.loads((directory / 'result.json').read_text())
        if record['kind'] == 'normal':
            assert result['agree'] and result['isla_consistent_side'] == 'both', (record, result)
        else:
            assert not result['agree'] and result['mismatch']['filtered']
            assert result['mismatch']['known_rule'] == 'xs_leaf_ppn_af_over_permission_pf'
            for key in ('xs_cause', 'nemu_cause', 'isla_consistent_side'):
                assert result[key] == record['expected'][key], (record, key, result[key])
            assert result['isla_cause'] == result['nemu_cause']
        print('重放完成', scene, record['kind'], index, result['bucket'], flush=True)
        return dict(**record, result=result)
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(task, manifest))
    for sig, handler in previous.items(): signal.signal(sig, handler)
    remaining = []
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid(): continue
        try: command = (entry / 'cmdline').read_bytes().replace(b'\0', b' ').decode(errors='replace')
        except (FileNotFoundError, ProcessLookupError): continue
        if str(output) in command and ('paging_worker.py' in command or 'program.elf' in command): remaining.append(dict(pid=int(entry.name), command=command))
    write(output / 'remaining-processes.json', remaining)
    assert not remaining, remaining
    write(output / 'results.json', results)
    write(output / 'summary.json', dict(total=len(results), normal_agree=sum(r['kind']=='normal' and r['result']['agree'] for r in results), known_filtered=sum(r['kind']=='known' and r['result']['mismatch']['filtered'] for r in results)))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['prepare','certify','replay'])
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--source',type=Path,default=Path('../replay-p0/output'))
    parser.add_argument('--isarch-processes',type=int,default=2)
    args=parser.parse_args()
    root=Path.cwd(); source=args.source.resolve(); output=args.output.resolve()
    os.environ.update(PYTHONDONTWRITEBYTECODE='1', TMPDIR=str(root / 'output/fuzz-step4'))
    if args.action=='prepare': prepare(root,source,output)
    elif args.action=='certify': certify(root,output,args.isarch_processes)
    else: replay(root,source,output)


if __name__=='__main__': main()
