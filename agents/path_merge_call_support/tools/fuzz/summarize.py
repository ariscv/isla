#!/usr/bin/env python3
"""汇总互不重叠阶段与常驻线程的取样证据。"""
import argparse
import bisect
from collections import Counter, defaultdict
import json
from pathlib import Path
import subprocess


def tags(folder):
    result = {}
    for line in (folder / 'stderr.txt').read_text().splitlines():
        if line.startswith('[JUDGE_RESIDENT_'):
            key, value = line.split(' ', 1)
            result[key] = json.loads(value)
    return result


def timing(folder):
    records = tags(folder)
    measurements = records['[JUDGE_RESIDENT_MEASUREMENTS]']
    result = {'batch_wall': measurements['batch_wall_seconds'],
              'batch_cpu': measurements['batch_cpu_seconds'], 'groups': {}}
    for name, low, high in [('all', 0, 1383), ('positive', 0, 1380), ('corpus', 0, 380), ('mutant', 380, 1380)]:
        rows = [r for r in measurements['samples'] if low <= r['sample_id'] < high]
        cpu = sum(r['cpu_seconds'] for r in rows)
        wall = sum(r['wall_seconds'] for r in rows)
        stages = defaultdict(lambda: {'cpu': 0., 'wall': 0., 'calls': 0})
        for row in rows:
            for key, stage in row['stages'].items():
                stages[key]['cpu'] += stage['cpu_seconds']
                stages[key]['calls'] += stage['calls']
            for key, stage in row['critical_stages'].items():
                stages[key]['wall'] += stage['wall_seconds']
        stages['other']['cpu'] = cpu - sum(s['cpu'] for s in stages.values())
        stages['other']['wall'] = wall - sum(s['wall'] for s in stages.values())
        for value in stages.values():
            value['cpu_percent'] = value['cpu'] / cpu * 100
            value['wall_percent'] = value['wall'] / wall * 100
        result['groups'][name] = {'count': len(rows), 'cpu': cpu, 'service_wall': wall, 'stages': stages}
    return result


def symbols(library):
    raw = subprocess.check_output(['nm', '-n', '-C', str(library)], text=True)
    entries = []
    for line in raw.splitlines():
        parts = line.split(maxsplit=2)
        if len(parts) == 3 and parts[1].lower() in ['t', 'w']:
            entries.append((int(parts[0], 16), parts[2]))
    return [e[0] for e in entries], [e[1] for e in entries]


def locks(folder, workers):
    rows = [json.loads(line) for line in (folder / 'locks.jsonl').read_text().splitlines()]
    contexts = [r['thread'] for r in rows if r.get('contexts', 0)]
    # 探索线程先退出，再创建常驻线程；Z3 Context 的创建顺序给出明确边界。
    resident = sorted(contexts)[-workers:]
    assert len(resident) == workers
    totals = defaultdict(lambda: {'calls': 0, 'samples': 0, 'wall_ns': 0, 'cpu_ns': 0})
    for row in rows:
        if row.get('thread') not in resident or 'kind' not in row:
            continue
        key = row['kind'] if row['kind'] != 'mutex' else row['caller']
        for field in totals[key]:
            totals[key][field] += row[field]
    samples = [r for r in rows if r.get('sample_thread') in resident]
    resolved = Counter()
    cache = {}
    for row in samples:
        library = row['object']
        if library.endswith('libz3.so.5.3') or library.endswith('/isarch'):
            if library not in cache:
                cache[library] = symbols(library)
            addresses, names = cache[library]
            index = bisect.bisect_right(addresses, int(row['offset'], 16)) - 1
            function = names[index] if index >= 0 else '?'
            resolved[(Path(library).name, function)] += 1
        else:
            resolved[(Path(library).name, '?')] += 1
    return {'resident_threads': resident, 'context_threads': contexts, 'calls': totals,
            'pc_samples': len(samples),
            'hotspots': [{'library': key[0], 'function': key[1], 'samples': value,
                          'percent': 100 * value / len(samples)} for key, value in resolved.most_common(60)]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['timing', 'locks'])
    parser.add_argument('folder', type=Path)
    parser.add_argument('--workers', type=int, default=26)
    args = parser.parse_args()
    result = timing(args.folder) if args.mode == 'timing' else locks(args.folder, args.workers)
    (args.folder / f'{args.mode}-summary.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(result, ensure_ascii=False, indent=2))
