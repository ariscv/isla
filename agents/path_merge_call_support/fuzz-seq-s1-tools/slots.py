"""从实际符号指令代表中抽查，保持原条目，不限制操作数取值域。"""
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'output/fuzz-seq-s1-symbolic' / os.environ.get('S1_GROUP', 'merged')
for setting in sys.argv[1:]:
    export = OUT / f'{setting}-export'
    samples = [json.loads(line) for line in (export / 'samples.jsonl').read_text().splitlines()]
    assert samples, '空导出不能用于语义抽查'
    # 均匀选择实际代表，覆盖文件首尾；选择过程不修改寄存器或内存。
    count = min(32, len(samples))
    indices = [index * (len(samples) - 1) // max(1, count - 1) for index in range(count)]
    selected = [samples[index] for index in indices]
    assert len({sample['sample_id'] for sample in selected}) == count
    (export / 'slot-proposals.jsonl').write_text(''.join(json.dumps(sample, separators=(',', ':')) + '\n' for sample in selected))
    (export / 'slot-plan.json').write_text(json.dumps(dict(
        corpus_count=len(samples), proposal_count=count,
        selected_ids=[sample['sample_id'] for sample in selected],
        unchanged_entries=True), ensure_ascii=False, indent=2) + '\n')
    print(setting, count)
