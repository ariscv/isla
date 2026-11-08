"""逐字段检查计数、形状、前态域、认证报告和 DAG，不以哈希判有效性。"""
from collections import Counter, defaultdict
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'output/fuzz-step6a'
SOURCE = ROOT.parent / 'replay-p0/output/ecfg4b'
sys.path.insert(0, str(ROOT.parent / 'replay-p0/difftest-xiangshan'))
import paging_replay
spec = importlib.util.spec_from_file_location('step6a_pt_decode', ROOT / 'agents/path_merge_call_support/pt_decode/pt_decode.py')
decoder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(decoder)
decoder.classify_pte = lambda value, level, config: paging_replay.classify_standard_pte(decoder, value, level, config)


def read(path):
    return json.loads(path.read_text())


def summarize(scene, directory):
    clause = 'LOAD' if 'load' in scene else 'STORE'
    raw = read(directory / f'output/rv64_z{clause}.json')
    samples = [json.loads(line) for line in (directory / 'samples.jsonl').open()]
    rows = []
    for sample in samples:
        decoded = decoder.decode_sample(sample, decoder.Config(False, False, False))
        status = decoder.bit_value(sample['pre_registers']['mstatus']['struct']['bits'], 64)
        leaf = next((entry for entry in decoded['entries'] if entry['role'] == 'leaf'), None)
        rows.append(dict(sample_id=sample['sample_id'], path_signature=sample['path_signature'], class_id=sample['class_id'],
                         privilege=sample['pre_registers']['cur_privilege']['enum'], mstatus=hex(status),
                         sum=bool(status & (1 << 18)), mxr=bool(status & (1 << 19)),
                         result=decoded['exception_type'] or decoded['result'], failure_reason=decoded['failure_reason'],
                         shape_key=decoder.shape_key(decoded), leaf=leaf, entries=decoded['entries']))
    counted = sum(path['merge_enumeration']['counted_classes'] for path in raw['gen'])
    assert counted == len(samples) == len({row['sample_id'] for row in rows})
    assert len({(row['path_signature'], row['class_id']) for row in rows}) == counted
    result = dict(classes=counted, shapes=len({row['shape_key'] for row in rows}), paths=len(raw['gen']),
                  seconds=read(directory / 'done.json')['seconds'], raw_summary=raw['summary'],
                  truncated_paths=sum(bool(path['merge_enumeration']['path_truncated']) for path in raw['gen']),
                  timed_out=read(directory / 'done.json')['timed_out'])
    return result, samples, rows


results = {}
for scene in ['sv39-load', 'sv39-store', 'sv48-load', 'sv48-store']:
    group = OUT / 'serial64' if scene == 'sv48-load' and '--serial64-sv48-load' in sys.argv else OUT
    directory = group / f'{scene}-export'
    if not (directory / 'done.json').exists() or not list((directory / 'output').glob('rv64_*.json')):
        continue
    current, samples, rows = summarize(scene, directory)
    base, base_samples, base_rows = summarize(scene, SOURCE / scene)
    shapes = {row['shape_key'] for row in rows}
    base_shapes = {row['shape_key'] for row in base_rows}
    added = shapes - base_shapes
    by_shape = defaultdict(list)
    for row in rows:
        by_shape[row['shape_key']].append(row)
    categories = Counter()
    representatives = []
    for shape in sorted(added):
        row = min(by_shape[shape], key=lambda item: item['sample_id'])
        if row['failure_reason'] == 'privilege_permission':
            category = 'U 态访问 U=0 页' if row['leaf']['fields']['U'] == 0 else 'S 态 SUM=0 访问 U=1 页'
        else:
            assert 'load' in scene and row['leaf']['fields']['R'] == 0 and row['leaf']['fields']['X'] == 1 and row['mxr']
            category = 'MXR 允许 X-only 页读取：' + (row['failure_reason'] or '成功')
        categories[category] += 1
        representatives.append(dict(category=category, **row))
    violations = []
    for row in rows:
        if int(row['mstatus'], 16) & 0xfffffffffff3ffff != 0xa00000000 or row['privilege'] not in {'User', 'Supervisor'}:
            violations.append(row['sample_id'])
        for entry in row['entries']:
            assert 0x80100000 <= entry['paddr'] and entry['paddr'] + 8 <= 1 << 43
    current.update(output_group=str(group.relative_to(OUT)), E0=base, added_classes=current['classes']-base['classes'], added_shapes=len(added),
                   missing_shapes=len(base_shapes-shapes), new_shape_categories=dict(categories), state_violations=violations,
                   contexts=[dict(privilege=privilege, mstatus=status, count=count)
                             for (privilege, status), count in sorted(Counter((row['privilege'], row['mstatus']) for row in rows).items())])
    (directory / 'decoded.json').write_text(json.dumps(rows, ensure_ascii=False, indent=2))
    (directory / 'new-shapes.json').write_text(json.dumps(representatives, ensure_ascii=False, indent=2))
    judge = group / f'{scene}-judge/fuzz'
    if (judge / 'reconfirm.json').exists():
        reconfirm = read(judge / 'reconfirm.json')
        assert reconfirm['certified'] and reconfirm['corpus_entries'] == len(samples)
        assert {entry['sample_id'] for entry in reconfirm['entries']} == {entry['sample_id'] for entry in samples}
        assert all(entry['accepted_paths'] == 1 and all(entry[key] for key in
                   ['path_same', 'state_same', 'guard_unique', 'post_unique', 'class_rank_same']) for entry in reconfirm['entries'])
        manifest = read(judge / 'dag-manifest.json')
        assert manifest['reread_consistent'] and manifest['paths'] == current['paths']
        for entry in manifest['entries']:
            dag = read(judge / entry['file'])
            assert dag['path_signature'] == entry['path_signature']
            assert len(dag['guards']) == entry['guards'] and len(dag['definitions']) == entry['definitions']
        current['judge'] = dict(certified=True, entries=len(samples), dag=manifest,
                                seconds=read(judge.parent / 'done.json')['seconds'])
    check_directory = group / f'{scene}-check'
    if (check_directory / 'check.json').exists():
        check = read(check_directory / 'check.json')
        assert check['sample_total'] == len(check['samples']) == len(samples)
        assert {entry['sample_id'] for entry in check['samples']} == {entry['sample_id'] for entry in samples}
        assert all((entry['accepted_paths'], entry['consistent_paths'], entry['inconsistent_paths']) == (1, 1, 0)
                   for entry in check['samples'])
        clause = 'LOAD' if 'load' in scene else 'STORE'
        checked_raw = read(check_directory / f'output/rv64_z{clause}.json')
        current['check'] = dict(entries=len(samples), unique_consistent=True, raw_completed=check['completed'],
                               raw_summary=checked_raw['summary'], seconds=read(check_directory / 'done.json')['seconds'])
    results[scene] = current
    print(scene, current['classes'], current['shapes'], current['paths'], round(current['seconds'], 3), dict(categories), flush=True)

if (OUT / 'E0-sv39-load/done.json').exists():
    e0, samples, rows = summarize('sv39-load', OUT / 'E0-sv39-load')
    reference = SOURCE / 'sv39-load/samples.jsonl'
    e0['ecfg4b_samples_bytes_same'] = (OUT / 'E0-sv39-load/samples.jsonl').read_bytes() == reference.read_bytes()
    if (OUT / 'E0-before/samples.jsonl').exists():
        before = OUT / 'E0-before'
        e0['parent_samples_bytes_same'] = (OUT / 'E0-sv39-load/samples.jsonl').read_bytes() == (before / 'samples.jsonl').read_bytes()
        old = read(before / 'output/rv64_zLOAD.json')
        new = read(OUT / 'E0-sv39-load/output/rv64_zLOAD.json')
        e0['parent_json_fields_same'] = {key: old[key] == new[key] for key in old if key != 'provenance'}
        e0['parent_raw_json_bytes_same'] = (before / 'output/rv64_zLOAD.json').read_bytes() == (OUT / 'E0-sv39-load/output/rv64_zLOAD.json').read_bytes()
        # 运行内符号编号不作语义身份；按路径中的记录位置比较完整类目录。
        def catalog(value):
            catalogs = []
            for path in value['gen']:
                enumeration = path['merge_enumeration']
                positions = {record['record_id']: index for index, record in enumerate(enumeration['guard_records'])}
                records = [{**{key: val for key, val in record.items() if key not in ['record_id', 'parent_record', 'condition']},
                            'parent_record': None if record['parent_record'] is None else positions[record['parent_record']]}
                           for record in enumeration['guard_records']]
                classes = [dict(class_id=entry['class_id'], truncated=entry['truncated'], solution_count=entry['solution_count'],
                                guard_assignment={str(positions[int(key)]): val for key, val in entry['guard_assignment'].items()})
                           for entry in enumeration['guard_classes']]
                catalogs.append(dict(path_signature=path['path-signature'], records=records, classes=classes,
                                     counted_classes=enumeration['counted_classes'], partitions=enumeration['partitions']))
            return catalogs
        e0['parent_class_catalog_same'] = catalog(old) == catalog(new)
        (OUT / 'E0-canonical-comparison.json').write_text(json.dumps(dict(
            class_catalog_same=e0['parent_class_catalog_same'], paths=len(old['gen']),
            comparison='路径签名、守卫位置及父关系、逐类规范向量、类号、计数与分区逐字段比较；不比较运行内编号及未固定的代表值'), ensure_ascii=False, indent=2))

    results['E0'] = e0
first = OUT / 'sv48-load-export/done.json'
if first.exists() and read(first)['timed_out']:
    results['sv48-load-first-attempt'] = dict(timed_out=True, seconds=read(first)['seconds'],
        returncode=read(first)['returncode'], written_rows=sum(1 for line in (first.parent / 'samples.jsonl').open()),
        complete_corpus=False, limit_seconds=900)
(OUT / 'analysis.json').write_text(json.dumps(results, ensure_ascii=False, indent=2) + '\n')
