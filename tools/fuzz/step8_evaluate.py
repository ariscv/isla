#!/usr/bin/env python3
"""PPN 软偏好的 E2 对比；复用真实 worker、覆盖定义与第 7 步认证审计。"""
import argparse
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
from types import SimpleNamespace

from step5_validate import canonical, lines, validate
from step7_evaluate import SCENARIOS, read, run_one, write


def selected_indices(total, budget):
    assert 0 < budget <= total
    controls = budget * 5 // 100
    return list(range(budget-controls)) + list(range(total-total*5//100, total-total*5//100+controls))


def historical(root, scene):
    stage = 'initial-1' if scene.startswith('sv39') else 'sv48-retry'
    return root / 'output/fuzz-step7' / stage / f'{scene}-1-difftest'


def audit(directory, budget, decoder, replay):
    validation = validate(directory)
    output = directory/'fuzz'
    complete = read(output/'findings-summary.json')
    assert complete['infrastructure_failures'] == 0
    all_records = lines(output/'mutations.jsonl')
    assert complete['executed'] == len(all_records)
    indices = selected_indices(len(all_records), budget)
    ids = set(indices)
    samples = lines(output/'mutants.jsonl')
    classified = lines(output/'classified.jsonl')
    judgments = lines(output/'judged.jsonl')
    proofs = lines(output/'certified.jsonl')
    observations = lines(output/'feedback-observations.jsonl')
    findings = [f for f in lines(output/'findings.jsonl') if f['sample_id'] in ids]
    timing = [t for t in lines(output/'hardware-timing.jsonl') if t['sample_id'] in ids]
    assert len(timing) == budget and all(type(t['emu_seconds']) in (int, float) for t in timing)
    summary = read(output/'feedback-summary.json')
    initial_buckets = {(canonical(row['identity']), bucket)
                       for row in summary['initial']['classes'] for bucket in row['buckets']}
    buckets = {(canonical(observations[i]['feature']['identity']), b)
               for i in indices for b in observations[i]['feature']['buckets']}
    unique_inputs, unique_fields = defaultdict(set), defaultdict(set)
    hits = unique_input_count = unique_field_count = retained = guided = overflow = 0
    profile, lock = read(directory/'profile.json'), read(directory/'profile.lock.json')
    contexts = {}
    control_leaf_overflow = control_pte_overflow = 0
    canonicalized_control_memory = []
    for i in indices:
        sample, actual, record, judgment, proof = samples[i], classified[i], all_records[i], judgments[i], proofs[i]
        assert sample['sample_id'] == actual['sample_id'] == record['sample_id'] == judgment['sample_id'] == proof['sample_id'] == i
        assert proof['sample']['class_id'] is None
        proof['sample']['class_id'] = actual['class_id']
        assert proof == judgment and proof['guard_unique'] and proof['post_unique']
        for field in ('pre_registers', 'isa_state'):
            assert sample[field] == actual[field], (directory, i, field)
        if record['operator'] in ('A', 'B'):
            assert sample['pre_memory'] == actual['pre_memory'], (directory, i, 'A/B 内存')
        else:
            # SamplePath::bind 已用同一输入认证；具体化输出只保留活动读取的初始值。
            # 输入额外初始化的非读取字节不改变行为，实际读取的每个字节仍须相同。
            provided = {(cell['address'], cell['bytes']): cell['value'] for cell in sample['pre_memory']}
            assert len(provided) == len(sample['pre_memory']), '输入内存地址不得重复'
            for bound in actual['pre_memory']:
                if bound['value'] is not None:
                    assert provided[bound['address'], bound['bytes']] == bound['value'], (directory, i, bound)
            if sample['pre_memory'] != actual['pre_memory']:
                canonicalized_control_memory.append(i)
        case = replay.platform_case(actual, decoder, profile, lock['platform_gen_sha256'])
        contexts[i] = case
        raw = read(output/'difftest'/f'input-{i:06d}'/'result.json')
        assert raw['prestate_context'] == case['prestate_context']
        if record['operator'] in ('A', 'B'):
            guided += 1
            hits += record['actual_identity'] == record['target_identity']
            identity = canonical(record['target_identity'])
            value = canonical({f: sample[f] for f in ('pre_registers', 'pre_memory')})
            unique_input_count += value not in unique_inputs[identity]
            unique_inputs[identity].add(value)
            fields = canonical([(c['field'], c['after']) for c in record['changes']])
            unique_field_count += fields not in unique_fields[identity]
            unique_fields[identity].add(fields)
            retained += record.get('ppn_overflow_retained_for_class', False)
            leaf_overflow = any(e['role'] == 'leaf' and e['fields']['PPN'] >> 36
                                for e in case['decoded']['entries'])
            overflow += leaf_overflow
            if record.get('avoid_known_ppn_overflow', False) and not record['ppn_overflow_retained_for_class']:
                assert not leaf_overflow, (directory.name, i, '软偏好未生效')
        else:
            control_leaf_overflow += any(e['role'] == 'leaf' and e['fields']['PPN'] >> 36
                                         for e in case['decoded']['entries'])
            control_pte_overflow += any(e['role'] != 'data' and e['fields']['PPN'] >> 36
                                        for e in case['decoded']['entries'])
    known = sum(f['rule_id'] == 'R-XS-001' for f in findings)
    assert all(not f['infrastructure'] for f in findings)
    unknown = [f for f in findings if not f['filtered']]
    differences = []
    for finding in unknown:
        i = finding['sample_id']
        case = contexts[i]
        differences.append(dict(setting=str(directory), sample_id=i,
            input=str(output/'mutants.jsonl'), prestate=case['prestate_context'],
            pte_chain=[e for e in case['decoded']['entries'] if e['role'] != 'data'],
            target_class=all_records[i].get('target_identity'), actual_class=all_records[i]['actual_identity'],
            isla_cause=finding['isla_cause'], xs_cause=finding['xs_cause'], nemu_cause=finding['nemu_cause']))
    emu = sum(t['emu_seconds'] for t in timing)
    # hardware-timing 保留的 known_rule 是规则的内部名字；与逐例 finding 对齐。
    known_ids = {f['sample_id'] for f in findings if f['rule_id'] == 'R-XS-001'}
    assert all((t['known_rule'] is not None) == (t['sample_id'] in known_ids) for t in timing)
    known_emu = sum(t['emu_seconds'] for t in timing if t['sample_id'] in known_ids)
    done = read(directory/'done.json')
    row = dict(directory=str(directory), mutants=budget, original_mutants=len(all_records), selected_ids=indices,
        audit=validation, agree=budget-len(findings), mismatch=len(findings), r_xs_001=known, new_disagreements=len(unknown),
        emu_seconds=emu, known_emu_seconds=known_emu, known_emu_fraction=known_emu/emu,
        class_value_buckets=len(buckets), new_value_buckets=len(buckets-initial_buckets),
        ppn_bucket_coverage=dict(Counter(json.loads(b)[2] for identity, b in buckets if json.loads(b)[1] == 'PPN')),
        retained_for_class=retained, guided_leaf_overflow=overflow, guided=guided, target_hits=hits,
        hit_classes=len({canonical(all_records[i]['actual_identity']) for i in indices}),
        control_leaf_overflow=control_leaf_overflow, control_pte_overflow=control_pte_overflow,
        canonicalized_control_memory=canonicalized_control_memory,
        unique_inputs=unique_input_count, unique_fields=unique_field_count,
        operators=dict(Counter(all_records[i]['operator'] for i in indices)),
        loop_seconds_per_1000=read(output/'timing.json')['loop_seconds']*1000/len(all_records),
        process_seconds_per_1000=done['seconds']*1000/len(all_records),
        wallclock_measured_mutants=len(all_records), remaining_processes=read(directory/'remaining-processes.json'))
    assert row['target_hits'] == row['unique_inputs'] == row['unique_fields'] == guided
    assert row['remaining_processes'] == []
    return row, differences, buckets


def report(args):
    import sys
    root = Path.cwd()
    sys.path.insert(0, str(root.parent/'replay-p0/difftest-xiangshan'))
    import paging_replay as replay
    decoder, provenance = replay.load_decoder(os.environ['PT_DECODE_DIR'], standard_paging=True)
    rows, differences, deterministic, controls = [], [], [], []
    setting_buckets = {}
    for initial in (1, 42):
        for scene in SCENARIOS:
            for enabled in (False, True):
                base = args.output/('on' if enabled else 'off')
                directory = historical(root, scene) if initial == 1 and not enabled else base/f'{scene}-{initial}-difftest'
                if not (directory/'done.json').exists():
                    continue
                row, new, buckets = audit(directory, args.budget, decoder, replay)
                setting_buckets[scene, initial, enabled] = buckets
                row.update(scene=scene, random_seed=initial, enabled=enabled)
                rows.append(row)
                differences.extend(new)
                repeat = base/f'{scene}-{initial}-model'
                if (repeat/'done.json').exists():
                    files = []
                    names = ['mutants.jsonl', 'judged.jsonl', 'mutations.jsonl', 'classified.jsonl',
                             'statistics.json', 'coverage.json', 'transitions.json', 'seed-map.json']
                    if initial != 1 or enabled:
                        names.append('ppn-preference-summary.json')
                    names += [str(p.relative_to(directory/'fuzz')) for p in sorted((directory/'fuzz/dag').glob('*.json'))]
                    for name in names:
                        left, right = directory/'fuzz'/name, repeat/'fuzz'/name
                        if initial == 1 and not enabled and name == 'mutations.jsonl':
                            # 历史接口没有本轮新增的统计字段，其余字段逐项保持。
                            old, current = lines(left), lines(right)
                            for record in current:
                                if record['operator'] in ('A', 'B'):
                                    assert record.pop('avoid_known_ppn_overflow') is False
                                    assert record.pop('ppn_overflow_retained_for_class') is False
                            assert old == current
                            files.append(dict(file=name, semantic=True, historical_metadata_only=True))
                        else:
                            first = lines(left) if left.suffix == '.jsonl' else read(left)
                            second = lines(right) if right.suffix == '.jsonl' else read(right)
                            assert first == second, (directory, name, 'JSON 不同')
                            assert left.read_bytes() == right.read_bytes(), (directory, name, '字节不同')
                            files.append(dict(file=name, semantic=True, byte_identical=True))
                    deterministic.append(dict(scene=scene, random_seed=initial, enabled=enabled, files=files))
            off = args.output/'off'/f'{scene}-{initial}-difftest'
            on = args.output/'on'/f'{scene}-{initial}-difftest'
            if initial == 42 and (off/'done.json').exists() and (on/'done.json').exists():
                left, right = lines(off/'fuzz/mutants.jsonl'), lines(on/'fuzz/mutants.jsonl')
                begin = args.budget-args.budget*5//100
                assert left[begin:] == right[begin:]
                records_off, records_on = lines(off/'fuzz/mutations.jsonl'), lines(on/'fuzz/mutations.jsonl')
                assert [(r['operator'], r['target_identity']) for r in records_off[:begin]] == [(r['operator'], r['target_identity']) for r in records_on[:begin]]
                controls.append(dict(scene=scene, random_seed=initial, identical=len(left)-begin,
                    guided_targets_identical=begin))
    deltas = []
    for initial in (1, 42):
        for scene in SCENARIOS:
            if (scene, initial, False) not in setting_buckets or (scene, initial, True) not in setting_buckets:
                continue
            before, after = setting_buckets[scene, initial, False], setting_buckets[scene, initial, True]
            def grouped(buckets):
                counts = Counter(canonical(json.loads(b)[1:]) for identity, b in buckets)
                return [dict(field=json.loads(key)[0], bucket=json.loads(key)[1], count=n)
                        for key, n in sorted(counts.items())]
            deltas.append(dict(scene=scene, random_seed=initial, paired_schedule=initial == 42,
                lost=len(before-after), gained=len(after-before),
                lost_by_field_value=grouped(before-after), gained_by_field_value=grouped(after-before)))
    write(args.output/'coverage-deltas.json', deltas)
    write(args.output/'comparison.json', rows)
    write(args.output/'new-disagreements.json', differences)
    write(args.output/'determinism.json', deterministic)
    write(args.output/'controls-comparison.json', controls)
    print('已汇总', len(rows), '组；新分歧', len(differences), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('run', 'repeat', 'report'))
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--experiment', type=Path, default=Path('../isla-sym-config/output/fuzz-step6a'))
    parser.add_argument('--budget', type=int, default=500)
    parser.add_argument('--repeat-initial', type=int, nargs='+', choices=(1, 42), default=[42],
                        help='确定性复跑的初值，默认只复跑 42；两种开关及四场景均保留')
    args = parser.parse_args()
    args.output, args.experiment = args.output.resolve(), args.experiment.resolve()
    if args.action == 'run':
        args.output.mkdir(parents=True, exist_ok=False)
        for mode in ('on', 'off'):
            (args.output/mode).mkdir()
        # 硬件、探索和模型复跑串行；只有一个 8 路 emu 池。
        for initial in (1, 42):
            for scene in SCENARIOS:
                for enabled in ((True,) if initial == 1 else (False, True)):
                    sub = SimpleNamespace(output=args.output/('on' if enabled else 'off'),
                        experiment=args.experiment, budget=args.budget)
                    run_one(sub, scene, initial, 'difftest', ['--fuzz-avoid-known-ppn-overflow'] if enabled else [])
    if args.action in ('run', 'repeat'):
        for initial in args.repeat_initial:
            for scene in SCENARIOS:
                for enabled in (False, True):
                    sub = SimpleNamespace(output=args.output/('on' if enabled else 'off'),
                        experiment=args.experiment, budget=1000 if initial == 1 and not enabled else args.budget)
                    run_one(sub, scene, initial, 'model', ['--fuzz-avoid-known-ppn-overflow'] if enabled else [])
    report(args)


if __name__ == '__main__':
    main()
