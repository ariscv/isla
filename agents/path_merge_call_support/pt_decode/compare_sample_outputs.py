"""严格比较三种后端还原的每个 v1 字段，并分别核算类索引和全部载荷。"""
import argparse
import hashlib
import json
from pathlib import Path
import struct

from sample_outputs import compact_samples, binary_samples, exact


def signatures(rows):
    result = {}
    for sample in rows:
        identifier = sample['sample_id']
        assert identifier not in result, '重复 sample_id'
        result[identifier] = hashlib.sha256(json.dumps(sample,ensure_ascii=False,sort_keys=True,
                                                       separators=(',',':')).encode()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--v1',type=Path,required=True)
    parser.add_argument('--compact',type=Path,required=True)
    parser.add_argument('--binary',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    args = parser.parse_args()
    assert args.report.resolve() not in {args.v1.resolve(),args.compact.resolve(),args.binary.resolve()}, '比较报告不得覆盖输入'
    with args.v1.open() as source:
        expected = signatures(json.loads(line) for line in source)
    with args.compact.open() as source:
        compact = signatures(compact_samples(source))
    with args.binary.open('rb') as source:
        binary = signatures(binary_samples(source))
    assert expected == compact == binary, '存在字段差异，不能把三个输出视为相同样本'
    classes = 0
    payload = 0
    with args.binary.open('rb') as source:
        exact(source,8)
        version, size, record_size, metadata_size = struct.unpack('<IIII',exact(source,16))
        assert (version,size,record_size) == (1,24,40)
        source.seek(metadata_size,1)
        while True:
            signature, class_id, count, length, flags = struct.unpack('<QQQQQ',exact(source,40))
            if flags == (1<<64)-1:
                break
            classes += 1
            payload += length
            source.seek(length,1)
    samples = len(expected)
    assert samples > 0 and classes > 0
    report = dict(all_v1_fields_equal=True,samples=samples,classes=classes,removed_fields=[],
                  binary_header_bytes=24+metadata_size,binary_class_index_bytes=40*classes,
                  binary_index_bytes_per_class=40,binary_payload_bytes=payload,binary_footer_bytes=40,formats={})
    for name,path in [('v1_jsonl',args.v1),('compact_jsonl',args.compact),('binary',args.binary)]:
        total = path.stat().st_size
        report['formats'][name] = dict(total_bytes=total,bytes_per_class=total/classes,bytes_per_combination=total/samples)
    assert report['formats']['binary']['total_bytes'] == 24+metadata_size+40*classes+payload+40
    args.report.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
