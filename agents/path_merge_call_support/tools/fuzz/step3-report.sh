#!/usr/bin/env bash
# 从实际 JSON 逐字段统计；确定性按字节比较，不计算哈希。
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
exec python3 - "$@" <<'PY'
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import statistics
import importlib.util
import sys

root = Path.cwd()
base = Path(os.environ['FUZZ_STEP3_OUTPUT'])
functional_only = len(sys.argv)>1 and sys.argv[1]=='functional'
sys.path.insert(0,str(root.parent/'replay-p0/difftest-xiangshan'))
import paging_replay as replay
spec = importlib.util.spec_from_file_location('step3_report_decoder',root/'agents/path_merge_call_support/pt_decode/pt_decode.py')
decoder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(decoder)
decoder.classify_pte = lambda value, level, config: replay.classify_standard_pte(decoder,value,level,config)
def read(path):
    return json.loads(path.read_text())
def lines(path):
    return [json.loads(line) for line in path.read_text().splitlines()]
def key(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False)
report = {'runs': [], 'summary': {}, 'determinism': {}, 'performance': {}} if functional_only else read(base/'functional-acceptance.json')
if not functional_only:
    assert report['complete'] is False and len(report['runs'])==12
for scene in ('sv39-store','sv39-load'):
    for number in ((1,42,2026) if functional_only else ()):
        for kind in ('guided','baseline'):
            directory = base / kind / scene / str(number)
            output = directory / 'fuzz'
            ledger = read(output/'ledger.json')
            records = lines(output/'mutations.jsonl')
            assert len(ledger) == len(records) == 2000
            counts = Counter(row['operator'] for row in records)
            if kind == 'guided':
                assert sum(counts[op] for op in ('M1','M2','M5')) == 100
                assert all(r['operator'] in ('A','B') for r in records[:1900])
                assert all(r['operator'] in ('M1','M2','M5') for r in records[1900:])
            matches = Counter()
            # “字段取值”记录逻辑字段名及最终值；另统计完整具体输入，避免差量记录误导。
            fields = defaultdict(set)
            inputs = defaultdict(set)
            denominators = Counter()
            samples = lines(output/'mutants.jsonl')
            for row, sample in zip(records,samples):
                if row['operator'] not in ('A','B'):
                    continue
                assert row['actual_certified'] is True
                assert row['actual_identity'] == row['target_identity']
                matches[row['operator']] += 1
                target = key(row['target_identity'])
                operator = row['operator']
                fields[operator,target].add(key([(c['field'],c['after']) for c in row['changes']]))
                inputs[operator,target].add(key({k:sample[k] for k in ('pre_registers','pre_memory')}))
                denominators[operator] += 1
            hit_classes = {key(row['actual_identity']) for row in ledger if row['actual_identity'] is not None}
            dag = read(output/'dag-manifest.json')
            index = read(output/'path-index.json')
            assert {r['path_signature'] for r in index} == {e['path_signature'] for e in dag['entries']}
            guard_counts = {e['path_signature']:e['guards'] for e in dag['entries']}
            for entry in read(output/'seed-map.json'):
                assert len(entry['guard_vector']) == guard_counts[entry['path_signature']]
            guard_total = 0
            for entry in dag['entries']:
                value = read(output/entry['file'])
                assert value['path_signature'] == entry['path_signature']
                assert len(value['guards']) == entry['guards']
                assert len(value['definitions']) == entry['definitions']
                assert [d['sequence'] for d in value['definitions']] == list(range(len(value['definitions'])))
                positions = [d['trace_index'] for d in value['definitions']]
                assert positions == sorted(set(positions))
                defined = set()
                for definition in value['definitions']:
                    assert set(definition.get('references',[])) <= defined
                    if 'symbol' in definition:
                        assert definition['symbol'] not in defined
                        defined.add(definition['symbol'])
                guard_total += len(value['guards'])
            assert len(dag['entries']) == dag['paths'] and guard_total == dag['guards']
            elapsed = read(output/'timing.json')
            row = dict(scene=scene, random_seed=number, kind=kind, counts=dict(counts), target_matches=dict(matches), actual_classes=len(hit_classes), classes_per_thousand=len(hit_classes)/2,
                       dag_paths=dag['paths'], dag_guards=guard_total, dag_reread=True, timing=elapsed, process_seconds=read(directory/'done.json')['seconds'])
            row['diversity'] = {op:dict(count=n, unique_changed_field_values=sum(len(v) for (o,t),v in fields.items() if o==op), unique_inputs=sum(len(v) for (o,t),v in inputs.items() if o==op), field_ratio=sum(len(v) for (o,t),v in fields.items() if o==op)/n, input_ratio=sum(len(v) for (o,t),v in inputs.items() if o==op)/n) for op,n in denominators.items()}
            if denominators:
                combined_fields = defaultdict(set)
                combined_inputs = defaultdict(set)
                for (operator,target),values in fields.items():
                    combined_fields[target].update(values)
                for (operator,target),values in inputs.items():
                    combined_inputs[target].update(values)
                n = sum(denominators.values())
                row['diversity']['A+B'] = dict(count=n,field_ratio=sum(map(len,combined_fields.values()))/n,input_ratio=sum(map(len,combined_inputs.values()))/n)
            normalized_inputs = defaultdict(set)
            for judged in lines(output/'judged.jsonl'):
                identity = key([judged['path_signature'],judged['guard_vector']])
                normalized_inputs[identity].add(key({k:judged['sample'][k] for k in ('pre_registers','pre_memory')}))
            row['all_unique_normalized_inputs'] = sum(map(len,normalized_inputs.values()))
            compatible = 0
            for sample in lines(output/'classified.jsonl'):
                decoder.exact(sample,decoder.SAMPLE_FIELDS,'samples v1')
                decoder.decode_sample(sample,decoder.Config(False,False,False))
                compatible += 1
            assert compatible == sum(r['actual_identity'] is not None for r in ledger)
            row['accepted'] = compatible
            row['python_compatible'] = compatible
            report['runs'].append(row)
    report['summary'][scene] = {}
    for kind in ('guided','baseline'):
        values = [r['actual_classes'] for r in report['runs'] if r['scene']==scene and r['kind']==kind]
        report['summary'][scene][kind] = dict(actual_classes_mean=statistics.mean(values), actual_classes_range=[min(values),max(values)], classes_per_thousand_mean=statistics.mean(values)/2, classes_per_thousand_range=[min(values)/2,max(values)/2])
    repeated = base/'repeat'/scene/'1/fuzz'
    if not functional_only:
        assert (repeated/'timing.json').exists(), '确定性复验尚未完成'
        original = base/'guided'/scene/'1/fuzz'
        same = {name:(original/name).read_bytes()==(repeated/name).read_bytes() for name in ('mutants.jsonl','judged.jsonl','mutations.jsonl','statistics.json','coverage.json','transitions.json')}
        assert all(same.values()), (scene,same)
        report['determinism'][scene] = same
    performance = base/'performance'/scene/'1'
    if not functional_only:
        assert (performance/'fuzz/timing.json').exists(), '速度批次尚未完成'
        timing = read(performance/'fuzz/timing.json')
        assert timing['campaign']['certified']==0
        reference = base/'guided'/scene/'1/fuzz'
        assert (performance/'fuzz/mutants.jsonl').read_bytes()==(reference/'mutants.jsonl').read_bytes()
        assert (performance/'fuzz/judged.jsonl').read_bytes()==(reference/'judged.jsonl').read_bytes()
        report['performance'][scene] = dict(loop_seconds_per_thousand=timing['loop_seconds']/2, campaign_seconds_per_thousand=timing['campaign']['campaign_seconds']/2, generate_seconds_per_thousand=timing['campaign']['generate_seconds']/2, fast_seconds_per_thousand=timing['campaign']['fast_seconds']/2, process_seconds_per_thousand=read(performance/'done.json')['seconds']/2, timing=timing)
test = (root/'output/fuzz-step3/test-workspace-final.log').read_text()
import re
results = re.findall(r'test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored',test)
report['tests'] = dict(zip(('passed','failed','ignored'),(sum(int(row[i]) for row in results) for i in range(3))))
report['complete'] = not functional_only
name = 'functional-acceptance.json' if functional_only else 'acceptance.json'
(base/name).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='runs'},ensure_ascii=False,indent=2))
PY
