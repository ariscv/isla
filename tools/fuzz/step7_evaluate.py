#!/usr/bin/env python3
"""E2 四场景闭环及逐字段验收；硬件始终只有一个八路池。"""
import argparse
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import subprocess
import time

from step5_evaluate import compress_logs
from step5_validate import canonical, lines, validate

SCENARIOS = ('sv39-store', 'sv39-load', 'sv48-store', 'sv48-load')


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n')


def run_one(args, scene, initial, executor):
    root = Path.cwd()
    directory = args.output / f'{scene}-{initial}-{executor}'
    command = ['python3', str(root/'tools/fuzz/run_campaign.py'), '--scenario', scene,
        '--e2-experiment', str(args.experiment), '--budget', str(args.budget),
        '--random-seed', str(initial), '--threads', '32', '--executor', executor,
        '--output', str(directory), '--fuzz-feedback', 'none', '--fuzz-batch-size', '64',
        '--difftest-workers', '8', '--certify-all']
    with (args.output/(directory.name+'.log')).open('w') as log:
        process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)
        try:
            while process.poll() is None:
                compress_logs(directory)
                time.sleep(5)
            assert process.returncode == 0, (directory, process.returncode)
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=30)
            compress_logs(directory)
    done = read(directory/'done.json')
    assert read(directory/'fuzz/reconfirm.json')['certified']
    assert len(lines(directory/'fuzz/mutants.jsonl')) == args.budget
    if executor == 'difftest':
        summary = read(directory/'fuzz/findings-summary.json')
        assert summary['executed'] == args.budget and summary['infrastructure_failures'] == 0, summary
    print(directory.name, done['seconds'], flush=True)
    return directory


def report(args):
    root = Path.cwd()
    import sys
    sys.path.insert(0, str(root.parent/'replay-p0/difftest-xiangshan'))
    import paging_replay as replay
    decoder, provenance = replay.load_decoder(str(root.parent/'isla-enumerate/agents/path_merge_call_support/pt_decode'),
                                             standard_paging=True)
    rows, differences, determinism, incomplete = [], [], [], []
    for directory in sorted(args.output.glob('sv*-difftest')):
        if not (directory/'done.json').exists():
            continue
        output = directory/'fuzz'
        summary = read(output/'findings-summary.json')
        if summary['executed'] != args.budget or summary['infrastructure_failures']:
            incomplete.append(dict(setting=directory.name, summary=summary,
                mutants=len(lines(output/'mutants.jsonl')), done=read(directory/'done.json')))
            continue
        audit = validate(directory)
        samples = lines(output/'mutants.jsonl')
        classified = lines(output/'classified.jsonl')
        records = lines(output/'mutations.jsonl')
        judged = lines(output/'judged.jsonl')
        certified = lines(output/'certified.jsonl')
        feedback = read(output/'feedback-summary.json')
        findings = lines(output/'findings.jsonl')
        mismatch_ids = {f['sample_id'] for f in findings if not f['infrastructure']}
        profile, lock = read(directory/'profile.json'), read(directory/'profile.lock.json')
        contexts, mismatch_contexts = Counter(), Counter()
        unique_inputs, unique_fields = defaultdict(set), defaultdict(set)
        guided, hits, unique_input_count, unique_field_count = 0, 0, 0, 0
        for sample, actual, record, judgment, proof in zip(samples, classified, records, judged, certified):
            assert sample['sample_id'] == actual['sample_id'] == record['sample_id'] == judgment['sample_id'] == proof['sample_id']
            assert proof['sample']['class_id'] is None
            proof['sample']['class_id'] = actual['class_id']
            assert judgment == proof and proof['guard_unique'] and proof['post_unique']
            for field in ('pre_registers', 'pre_memory', 'isa_state'):
                assert sample[field] == actual[field], (sample['sample_id'], field)
            case = replay.platform_case(actual, decoder, profile, lock['platform_gen_sha256'])
            context = case['prestate_context']
            key = (context['privilege'], int(context['sum']), int(context['mxr']))
            contexts[key] += 1
            if sample['sample_id'] in mismatch_ids:
                mismatch_contexts[key] += 1
            if record['operator'] in ('A', 'B'):
                guided += 1
                hits += record['target_identity'] == record['actual_identity']
                identity = canonical(record['target_identity'])
                value = canonical({field: sample[field] for field in ('pre_registers', 'pre_memory')})
                unique_input_count += value not in unique_inputs[identity]
                unique_inputs[identity].add(value)
                changes = record['changes']
                fields = canonical([(c['field'], c['after']) for c in changes])
                unique_field_count += fields not in unique_fields[identity]
                unique_fields[identity].add(fields)
            raw = read(output/'difftest'/f"input-{sample['sample_id']:06d}"/'result.json')
            assert raw['prestate_context'] == context
        for finding in findings:
            if finding['infrastructure'] or finding['filtered']:
                continue
            index = finding['sample_id']
            case = replay.platform_case(classified[index], decoder, profile, lock['platform_gen_sha256'])
            differences.append(dict(setting=directory.name, sample_id=index,
                prestate=case['prestate_context'], target_class=records[index].get('target_identity'),
                actual_class=records[index]['actual_identity'],
                pte_chain=[e for e in case['decoded']['entries'] if e['role'] != 'data'],
                isla_cause=finding['isla_cause'], xs_cause=finding['xs_cause'], nemu_cause=finding['nemu_cause'],
                input=str((output/'mutants.jsonl').relative_to(root))))
        def context_rows(counter):
            return [dict(privilege=p, sum=s, mxr=m, count=n) for (p, s, m), n in sorted(counter.items())]
        def proportions(counter):
            total = sum(counter.values())
            counts = dict(user=sum(n for (p, s, m), n in counter.items() if p == 'User'),
                sum_zero=sum(n for (p, s, m), n in counter.items() if s == 0),
                mxr_one=sum(n for (p, s, m), n in counter.items() if m == 1),
                any=sum(n for (p, s, m), n in counter.items() if p == 'User' or s == 0 or m == 1))
            return dict(total=total, counts=counts,
                        fractions={key: count/total if total else None for key, count in counts.items()})
        timing = read(output/'timing.json')
        rows.append(dict(setting=directory.name, **summary, audit=audit,
            operators=dict(Counter(r['operator'] for r in records)), guided=guided, target_hits=hits,
            unique_inputs=unique_input_count, unique_fields=unique_field_count,
            mutant_class_value_buckets=feedback['mutant_class_value_buckets'],
            new_value_buckets=feedback['final']['class_value_buckets']-feedback['initial']['class_value_buckets'],
            hit_classes=sum(row['hit'] for row in read(output/'coverage.json')),
            corpus_entries=read(output/'reconfirm.json')['corpus_entries'],
            contexts=context_rows(contexts), mismatch_contexts=context_rows(mismatch_contexts),
            prestate_proportions=proportions(contexts), mismatch_proportions=proportions(mismatch_contexts),
            process_seconds_per_1000=read(directory/'done.json')['seconds']*1000/len(samples),
            loop_seconds_per_1000=timing['loop_seconds']*1000/len(samples),
            generate_seconds_per_1000=timing['campaign']['generate_seconds']*1000/len(samples)))
        repeat = directory.with_name(directory.name.removesuffix('difftest')+'model')
        if (repeat/'done.json').exists():
            files = []
            for name in ('mutants.jsonl', 'judged.jsonl'):
                assert lines(output/name) == lines(repeat/'fuzz'/name), (directory.name, name, 'JSON 字段不同')
                assert (output/name).read_bytes() == (repeat/'fuzz'/name).read_bytes(), (directory.name, name, '字节不同')
                files.append(dict(file=name, bytes=(output/name).stat().st_size, identical=True))
            determinism.append(dict(setting=directory.name, files=files))
    write(args.output/'results.json', rows)
    write(args.output/'new-disagreements.json', differences)
    write(args.output/'determinism.json', determinism)
    write(args.output/'incomplete-attempts.json', incomplete)
    print('已汇总', len(rows), '场景；新分歧', len(differences), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['run', 'report'])
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--experiment', type=Path, default=Path('../isla-sym-config/output/fuzz-step6a'))
    parser.add_argument('--budget', type=int, default=1000)
    parser.add_argument('--initial', type=int, nargs='+', default=[1])
    parser.add_argument('--scenarios', nargs='+', choices=SCENARIOS, default=list(SCENARIOS))
    args = parser.parse_args()
    args.output, args.experiment = args.output.resolve(), args.experiment.resolve()
    if args.action == 'run':
        args.output.mkdir(parents=True, exist_ok=False)
        os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
        # 共享主机上不让 T32 模型复跑与八路 emu 争用资源。
        for initial in args.initial:
            for scene in args.scenarios:
                run_one(args, scene, initial, 'difftest')
        for initial in args.initial:
            for scene in args.scenarios:
                run_one(args, scene, initial, 'model')
    report(args)


if __name__ == '__main__':
    main()
