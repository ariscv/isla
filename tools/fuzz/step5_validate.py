#!/usr/bin/env python3
"""按 JSON 语义检查 corpus 血缘、桶增量与签名；确定性另比较完整正式文件。"""
import argparse
import json
from pathlib import Path


def lines(path):
    return [json.loads(line) for line in path.read_text().splitlines()]


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def validate(directory):
    output = directory / 'fuzz'
    summary = json.loads((output / 'feedback-summary.json').read_text())
    initial = summary['initial']['classes']
    seen = {(canonical(row['identity']), bucket) for row in initial for bucket in row['buckets']}
    initial_count = len(seen)
    unknown_signatures = set()
    admitted = set()
    additions = {row['input_id']: row for row in lines(output / 'corpus-added.jsonl')}
    catalog = json.loads((output / 'seed-map.json').read_text())
    entries = {'initial:'+str(row['corpus_sample_id']): row['identity'] for row in catalog}
    observations = lines(output / 'feedback-observations.jsonl')
    records = lines(output / 'mutations.jsonl')
    certified = {row['sample_id'] for row in lines(output / 'certified.jsonl')}
    command = json.loads((directory/'done.json').read_text())['command']
    batch_size = int(command[command.index('--fuzz-batch-size')+1])
    new_parent_uses = 0
    mutant_buckets = set()
    for index, (observation, record) in enumerate(zip(observations, records)):
        assert observation['sample_id'] == record['sample_id'] == index
        parent = record['parent_corpus_entry']
        assert parent['identity'] == entries[parent['input_id']]
        if parent['input_id'].startswith('mutant:'):
            parent_index = int(parent['input_id'].split(':')[1])
            assert parent_index//batch_size < index//batch_size, '批内提前使用新增 corpus entry'
            new_parent_uses += 1
        feature = observation['feature']
        identity = feature['identity']
        assert identity == record['actual_identity']
        if 'target_identity' in record:
            assert identity == record['target_identity']
        buckets = {(canonical(identity), bucket) for bucket in feature['buckets']}
        mismatch = feature['mismatch']
        signature = None
        if mismatch is not None and not mismatch['infrastructure'] and not mismatch['filtered']:
            signature = canonical(dict(target_class=identity, fields=mismatch['fields'], phase=mismatch['phase']))
        novel = bool(buckets-seen) or (signature is not None and signature not in unknown_signatures)
        assert novel == observation['novel']
        seen.update(buckets)
        mutant_buckets.update(buckets)
        if signature is not None:
            unknown_signatures.add(signature)
        input_id = 'mutant:'+str(index)
        if summary['mode'] == 'coverage' and novel:
            assert index in certified
            entry = additions[input_id]
            assert entry['identity'] == identity and entry['parent'] == parent
            assert entry['sample']['sample_id'] == index
            entries[input_id] = identity
            admitted.add(input_id)
        else:
            assert input_id not in additions
    assert len(observations) == len(records)
    assert admitted == additions.keys()
    assert len(seen) == summary['final']['class_value_buckets']
    assert len(mutant_buckets) == summary['mutant_class_value_buckets']
    assert len(unknown_signatures) == summary['final']['unknown_signatures']
    assert json.loads((directory/'remaining-processes.json').read_text()) == []
    return dict(directory=directory.name, mutants=len(records), new_value_buckets=len(seen)-initial_count,
                corpus_added=len(additions), new_parent_uses=new_parent_uses, valid=True)


def compare(left, right):
    excluded = {'timing.json', 'hardware-timing.jsonl'}
    def without_times(value):
        if isinstance(value, dict):
            return {key: without_times(item) for key, item in value.items() if not key.endswith('seconds')}
        if isinstance(value, list):
            return [without_times(item) for item in value]
        return value
    assert without_times(json.loads((left/'fuzz/timing.json').read_text())) == without_times(json.loads((right/'fuzz/timing.json').read_text()))
    if (left/'fuzz/hardware-timing.jsonl').exists():
        assert without_times(lines(left/'fuzz/hardware-timing.jsonl')) == without_times(lines(right/'fuzz/hardware-timing.jsonl'))
    names = {p.name for p in (left/'fuzz').iterdir() if p.is_file() and p.name not in excluded}
    assert names == {p.name for p in (right/'fuzz').iterdir() if p.is_file() and p.name not in excluded}
    rows = []
    for name in sorted(names):
        first, second = left/'fuzz'/name, right/'fuzz'/name
        if first.suffix == '.jsonl':
            assert lines(first) == lines(second), name
        else:
            assert json.loads(first.read_text()) == json.loads(second.read_text()), name
        assert first.read_bytes() == second.read_bytes(), name
        rows.append(dict(file=name, identical=True))
    dag_names = {p.name for p in (left/'fuzz/dag').iterdir()}
    assert dag_names == {p.name for p in (right/'fuzz/dag').iterdir()}
    for name in sorted(dag_names):
        first, second = left/'fuzz/dag'/name, right/'fuzz/dag'/name
        value = json.loads(first.read_text())
        assert value['schema_version'] == 2
        assert all(guard['record_id'] == guard['coordinate'] for guard in value['guards'])
        assert value == json.loads(second.read_text()), name
        assert first.read_bytes() == second.read_bytes(), name
        rows.append(dict(file='dag/'+name, identical=True))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--evaluation', type=Path)
    parser.add_argument('--left', type=Path)
    parser.add_argument('--right', type=Path)
    args = parser.parse_args()
    result = {}
    if args.evaluation:
        result['campaigns'] = [validate(path) for path in sorted(args.evaluation.glob('sv39-*')) if path.is_dir()]
    if args.left:
        result['determinism'] = compare(args.left, args.right)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')


if __name__ == '__main__':
    main()
