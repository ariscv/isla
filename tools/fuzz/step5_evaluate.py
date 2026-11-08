#!/usr/bin/env python3
"""顺序评估反馈与轮转基线；单个 8 路 emu 池，无损压缩已结束的日志。"""
import argparse
import gzip
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def read(path):
    return json.loads(path.read_text())


def lines(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def compress_logs(directory):
    for result in directory.glob('fuzz/difftest/input-*/result.json'):
        path = result.parent / 'difftest.log'
        if path.exists():
            with path.open('rb') as source, path.with_suffix('.log.gz').open('wb') as target:
                with gzip.GzipFile(filename='difftest.log', mode='wb', fileobj=target, mtime=0) as packed:
                    import shutil
                    shutil.copyfileobj(source, packed)
            path.unlink()


def run(args):
    assert args.budget > 0
    args.output.mkdir(parents=True, exist_ok=False)
    root = Path.cwd()
    # 交替先后次序，避免所有反馈批次都在同一个时间段。
    for scene in ['sv39-store', 'sv39-load']:
        for initial in [1, 42]:
            modes = ['none', 'coverage'] if initial == 1 else ['coverage', 'none']
            for mode in modes:
                directory = args.output / f'{scene}-{mode}-{initial}'
                command = ['python3', str(root / 'tools/fuzz/run_campaign.py'),
                           '--scenario', scene, '--budget', str(args.budget),
                           '--random-seed', str(initial), '--threads', '32',
                           '--executor', 'difftest', '--output', str(directory),
                           '--fuzz-feedback', mode, '--fuzz-batch-size', '64',
                           '--difftest-workers', '8']
                with (args.output / (directory.name + '.log')).open('w') as log:
                    process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
                    def cancel(signum, frame):
                        process.send_signal(signum)
                    previous = {sig: signal.signal(sig, cancel) for sig in (signal.SIGTERM, signal.SIGINT)}
                    try:
                        while process.poll() is None:
                            compress_logs(directory)
                            time.sleep(5)
                        assert process.returncode == 0, (directory, process.returncode)
                    finally:
                        if process.poll() is None:
                            process.terminate()
                            process.wait(timeout=30)
                        for sig, handler in previous.items():
                            signal.signal(sig, handler)
                    compress_logs(directory)
                print(directory.name, read(directory / 'done.json')['seconds'], flush=True)
                report(args)


def report(args):
    rows, disagreements = [], []
    for directory in sorted(args.output.glob('sv39-*')):
        if not directory.is_dir() or not (directory / 'done.json').exists():
            continue
        output = directory / 'fuzz'
        summary = read(output / 'feedback-summary.json')
        findings = lines(output / 'findings.jsonl')
        known = {json.dumps(row['group_key'], sort_keys=True) for row in findings if row['filtered']}
        unknown = {json.dumps(row['group_key'], sort_keys=True) for row in findings
                   if not row['filtered'] and not row['infrastructure']}
        timing = lines(output / 'hardware-timing.jsonl')
        assert all(type(row['emu_seconds']) in (int, float) for row in timing), 'emu 计时缺失'
        total_time = sum(row['emu_seconds'] for row in timing)
        known_time = sum(row['emu_seconds'] for row in timing if row['known_rule'] is not None)
        scene, mode, initial = directory.name.rsplit('-', 2)
        count = read(output / 'findings-summary.json')['executed']
        loop = read(output / 'timing.json')['loop_seconds']
        rows.append(dict(scene=scene, feedback=mode, random_seed=int(initial), mutants=count,
            mutant_class_value_buckets=summary['mutant_class_value_buckets'],
            new_value_buckets=summary['final']['class_value_buckets']-summary['initial']['class_value_buckets'],
            initial_value_buckets=summary['initial']['class_value_buckets'],
            final_value_buckets=summary['final']['class_value_buckets'],
            signatures=len(known | unknown), known_signatures=len(known), unknown_signatures=len(unknown),
            known_executions=sum(row['filtered'] for row in findings),
            unknown_executions=sum(not row['filtered'] and not row['infrastructure'] for row in findings),
            infrastructure_failures=sum(row['infrastructure'] for row in findings),
            emu_seconds=total_time, known_emu_seconds=known_time, known_emu_fraction=known_time/total_time,
            loop_seconds_per_1000=loop*1000/count,
            process_seconds_per_1000=read(directory/'done.json')['seconds']*1000/count,
            corpus_added=summary['final']['corpus_added'], remaining_processes=read(directory/'remaining-processes.json')))
        for row in findings:
            if not row['filtered'] and not row['infrastructure']:
                disagreements.append(dict(setting=directory.name, sample_id=row['sample_id'],
                    input=str((output/'mutants.jsonl').relative_to(Path.cwd())),
                    isla_cause=row['isla_cause'], xs_cause=row['xs_cause'], nemu_cause=row['nemu_cause'],
                    signature=row['group_key']))
    (args.output/'comparison.json').write_text(json.dumps(rows, ensure_ascii=False, indent=2)+'\n')
    (args.output/'new-disagreements.json').write_text(json.dumps(disagreements, ensure_ascii=False, indent=2)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'report'])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--budget', type=int, default=1000)
    args = parser.parse_args()
    args.output = args.output.resolve()
    if args.action == 'run':
        run(args)
    else:
        report(args)


if __name__ == '__main__':
    main()
