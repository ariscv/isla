#!/usr/bin/env python3
"""复现 M0：只读既有输入与真值，产物全部写入本工作树。"""
import argparse
import copy
import json
import os
from pathlib import Path
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'output/fuzz-m0'
REFERENCE = ROOT.parent / 'isla-judge/output'
ECFG = ROOT.parent / 'replay-p0/output/ecfg4b'


def read_rows(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def prepare():
    OUT.mkdir(parents=True, exist_ok=True)
    corpus = read_rows(ECFG / 'sv39-store/samples.jsonl')
    mutants = read_rows(REFERENCE / 'fuzz-p1b-classes/classified/sv39-store.jsonl')
    assert len(corpus) == 380 and len(mutants) == 1000
    rows, mapping = [], []
    for group, inputs in [('corpus', corpus), ('mutant', mutants)]:
        for original in inputs:
            row = copy.deepcopy(original)
            row['sample_id'] = len(rows)
            for field in ['post_registers', 'post_memory', 'result', 'ret_val']:
                del row[field]
            mapping.append({'group': group, 'original_sample_id': original['sample_id'], 'sample_id': row['sample_id']})
            rows.append(row)
    # 选择实际读取下级页表的成功 corpus entry，保证删除的字节确实被读。
    base = next(r for r in corpus if r['result']['ctor'] == 'Retire_Success' and
                any(c['address'] == 0x80100800 for c in r['pre_memory']))
    negative = []
    changed = copy.deepcopy(base)
    bits = changed['pre_registers']['x1']['bits']
    changed['pre_registers']['x1']['bits'] = bits[:-1] + ('1' if bits[-1] == '0' else '0')
    negative.append(('前态 x1 翻转最低位', changed))
    missing = copy.deepcopy(base)
    missing['pre_memory'] = [c for c in missing['pre_memory'] if c['address'] != 0x80100800]
    assert len(missing['pre_memory']) == len(base['pre_memory']) - 1
    negative.append(('删除已读地址 0x80100800 的字节', missing))
    excluded = copy.deepcopy(base)
    # 根 PTE 指向 0x20000000 排除区，同时补齐新读取地址的内存，避免因缺字节而拒绝。
    root = 0x80200000
    assert all(any(c['address'] == root + i for c in excluded['pre_memory']) for i in range(8))
    pte = 0x08000001
    for cell in excluded['pre_memory']:
        if root <= cell['address'] < root + 8:
            cell['value'] = (pte >> (8 * (cell['address'] - root))) & 255
    lower = [c for c in base['pre_memory'] if 0x80100800 <= c['address'] < 0x80100808]
    assert len(lower) == 8
    for cell in lower:
        excluded['pre_memory'].append({**cell, 'address': cell['address'] - 0x80100800 + 0x20000800})
    negative.append(('根 PTE 指向排除区且补齐下级读取字节', excluded))
    for description, row in negative:
        original_id = row['sample_id']
        row['sample_id'] = len(rows)
        for field in ['post_registers', 'post_memory', 'result', 'ret_val']:
            del row[field]
        mapping.append({'group': 'negative', 'original_sample_id': original_id,
                        'sample_id': row['sample_id'], 'description': description})
        rows.append(row)
    (OUT / 'inputs.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in rows))
    write_json(OUT / 'input-map.json', mapping)


def command(threads, run_dir):
    argv = json.loads((ECFG / 'sv39-store-j1/done.json').read_text())['command'][:]
    argv[0] = str(ROOT / 'target/release/isarch')
    argv[argv.index('-T') + 1] = str(threads)
    for option in ['--check-samples', '--check-samples-report']:
        index = argv.index(option)
        del argv[index:index + 2]
    index = argv.index('solve-state')
    argv[index:index] = ['--judge-resident', str(OUT / 'inputs.jsonl'),
                         '--judge-resident-out', str(run_dir / 'judged.jsonl')]
    return argv


def run(threads):
    run_dir = OUT / f't{threads}'
    run_dir.mkdir(exist_ok=False)
    argv = command(threads, run_dir)
    env = os.environ.copy()
    env.update(TMPDIR=str(OUT / 'tmp'), XDG_CACHE_HOME=str(OUT / 'cache'), ISLA_STATS='1')
    env.pop('LD_PRELOAD', None)
    start = time.monotonic()
    write_json(run_dir / 'running.json', {'command': argv, 'cwd': str(run_dir)})
    with (run_dir / 'stdout.txt').open('w') as stdout, (run_dir / 'stderr.txt').open('w') as stderr:
        result = subprocess.run(['/usr/bin/time', '-v', '-o', str(run_dir / 'time.txt'), *argv],
                                cwd=run_dir, env=env, stdout=stdout, stderr=stderr, timeout=1200)
    write_json(run_dir / 'done.json', {'command': argv, 'cwd': str(run_dir),
                                     'returncode': result.returncode, 'seconds': time.monotonic() - start})
    assert result.returncode in (0, 1), result.returncode


def describe(values):
    values = sorted(values)
    return {'count': len(values), 'sum': sum(values), 'mean': statistics.mean(values),
            'min': values[0], 'median': statistics.median(values),
            'p95': values[int((len(values) - 1) * .95)], 'max': values[-1]}


def verify(threads):
    run_dir = OUT / f't{threads}'
    mapping = json.loads((OUT / 'input-map.json').read_text())
    corpus = {r['sample_id']: r for r in read_rows(REFERENCE / 'judge/judge/sv39-store/judged.jsonl')}
    mutants = {r['sample_id']: r for r in read_rows(REFERENCE / 'fuzz-p1b-classes/mutants/judge/sv39-store/judged.jsonl')}
    ledger = {r['sample_id']: r for r in json.loads((REFERENCE / 'fuzz-p1b-classes/ledger.json').read_text()) if r['scene'] == 'sv39-store'}
    judged = read_rows(run_dir / 'judged.jsonl')
    grouped = {}
    for row in judged:
        grouped.setdefault(row['sample_id'], []).append(row)
    differences = []
    # 只去掉进程内记录编号；保留完整 sample 的全部字段进行 JSON 语义比较。
    def normalized(row, original_id):
        row = copy.deepcopy(row)
        row.pop('guard_order')
        row.pop('guard_assignment')
        row['sample_id'] = original_id
        row['sample']['sample_id'] = original_id
        return row
    negative = []
    for entry in mapping:
        sid, original_id = entry['sample_id'], entry['original_sample_id']
        actual = grouped.get(sid, [])
        if entry['group'] == 'negative':
            negative.append({**entry, 'accepted_paths': len(actual)})
            assert not actual, entry
            continue
        if len(actual) != 1:
            differences.append({'sample_id': sid, 'accepted_paths': len(actual)})
            continue
        expected = (corpus if entry['group'] == 'corpus' else mutants)[original_id]
        left, right = normalized(actual[0], original_id), normalized(expected, original_id)
        if left != right:
            differences.append({'sample_id': sid, 'fields': [key for key in left if left[key] != right[key]],
                                'actual': left, 'expected': right})
        if entry['group'] == 'mutant':
            assert actual[0]['path_signature'] == ledger[original_id]['actual_path']
            assert actual[0]['guard_vector'] == ledger[original_id]['guard_vector']
    tags = {}
    for line in (run_dir / 'stderr.txt').read_text().splitlines():
        if line.startswith('[JUDGE_RESIDENT_'):
            tag, data = line.split(' ', 1)
            assert tag not in tags
            tags[tag] = json.loads(data)
    assert len(tags) == 4, list(tags)
    report = tags['[JUDGE_RESIDENT_REPORT]']
    assert report['sample_total'] == 1383
    assert report['unaccepted_sample_ids'] == [1380, 1381, 1382]
    metrics = tags['[JUDGE_RESIDENT_MEASUREMENTS]']
    mutant_metrics = [row for row in metrics['samples'] if 380 <= row['sample_id'] < 1380]
    restore = tags['[JUDGE_RESIDENT_RESTORED]']
    outputs = list((run_dir / 'output').glob('*.json'))
    assert len(outputs) == 1, outputs
    execution = json.loads(outputs[0].read_text())['summary']
    assert execution['status'] == 'partial' and execution['errors'] == 5, execution
    for key in ['execution-timeouts', 'smt-timeouts', 'model-query-timeouts', 'unfinished-paths', 'pending-batches']:
        assert execution[key] == 0, (key, execution[key])
    time_lines = (run_dir / 'time.txt').read_text().splitlines()
    peak_rss = next(int(line.rsplit(':', 1)[1]) for line in time_lines if 'Maximum resident set size' in line)
    summary = {'threads': threads, 'execution_summary': execution,
               'process_seconds': json.loads((run_dir / 'done.json').read_text())['seconds'],
               'process_peak_rss_kib': peak_rss, 'compared_corpus': len(corpus), 'compared_mutants': len(mutants),
               'judged_rows': len(judged), 'differences': len(differences), 'negative': negative,
               'saved': tags['[JUDGE_RESIDENT_SAVED]'], 'restore_wall_seconds': restore['wall_seconds'],
               'restore_per_path_wall_seconds': describe([r['wall_seconds'] for r in restore['paths']]),
               'restore_per_path_cpu_seconds': describe([r['cpu_seconds'] for r in restore['paths']]),
               'batch_wall_seconds': metrics['batch_wall_seconds'], 'batch_cpu_seconds': metrics['batch_cpu_seconds'],
               'mutant_wall_seconds': describe([r['wall_seconds'] for r in mutant_metrics]),
               'mutant_cpu_seconds': describe([r['cpu_seconds'] for r in mutant_metrics]),
               'original_corpus_batch_seconds': json.loads((REFERENCE / 'judge/judge/sv39-store/done.json').read_text())['seconds'],
               'original_mutant_batch_seconds': json.loads((REFERENCE / 'fuzz-p1b-classes/mutants/judge/sv39-store/done.json').read_text())['seconds']}
    write_json(run_dir / 'metrics.json', tags)
    write_json(run_dir / 'differences.json', differences)
    write_json(run_dir / 'summary.json', summary)
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    assert len(judged) == 1380 and not differences


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['prepare', 'run', 'verify'])
    parser.add_argument('--threads', type=int, choices=[1, 32], default=32)
    args = parser.parse_args()
    if args.action == 'prepare':
        prepare()
    elif args.action == 'run':
        run(args.threads)
    else:
        verify(args.threads)
