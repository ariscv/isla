"""将紧凑 JSONL 或二进制类记录还原为普通 samples v1 JSONL，无需求解器。"""
import argparse
import copy
import json
from pathlib import Path
import struct


def apply_delta(base, delta):
    result = copy.deepcopy(base)
    for pointer in delta['remove']:
        assert pointer.startswith('/')
        keys = [key.replace('~1','/').replace('~0','~') for key in pointer[1:].split('/')]
        parent = result
        for key in keys[:-1]:
            parent = parent[int(key)] if isinstance(parent,list) else parent[key]
        assert not isinstance(parent,list), '数组长度变化必须替换整个数组'
        del parent[keys[-1]]
    for pointer, value in delta['set'].items():
        if pointer == '':
            result = copy.deepcopy(value)
            continue
        assert pointer.startswith('/')
        keys = [key.replace('~1','/').replace('~0','~') for key in pointer[1:].split('/')]
        parent = result
        for key in keys[:-1]:
            parent = parent[int(key)] if isinstance(parent,list) else parent[key]
        if isinstance(parent,list):
            parent[int(keys[-1])] = copy.deepcopy(value)
        else:
            parent[keys[-1]] = copy.deepcopy(value)
    return result


def restore(header, rows):
    assert header['compact_schema_version'] == 1
    assert header['skeleton']['schema_version'] == 1
    count = 0
    previous = -1
    for row in rows:
        assert row['solution_index'] > previous
        previous = row['solution_index']
        sample = apply_delta(header['skeleton'], row['delta'])
        assert sample['path_signature'] == header['path_signature']
        assert sample['class_id'] == header['class_id']
        yield sample
        count += 1
    assert count == header['solution_count']


class JsonStream:
    """按单个 JSON 值读取，类内组合集合不必一次装入内存。"""
    def __init__(self, source):
        self.source, self.buffer, self.position, self.eof = source, '', 0, False
        self.decoder = json.JSONDecoder()

    def refill(self):
        extra = self.source.read(65536)
        self.buffer = self.buffer[self.position:]+extra
        self.position = 0
        self.eof = not extra

    def peek(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position].isspace():
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            if self.eof:
                return None
            self.refill()

    def expect(self, character):
        assert self.peek() == character, f'预期 {character!r}'
        self.position += 1

    def value(self):
        assert self.peek() is not None, 'JSON 记录已截断'
        while True:
            try:
                result, end = self.decoder.raw_decode(self.buffer,self.position)
            except json.JSONDecodeError:
                if self.eof:
                    raise
                self.refill()
                continue
            # 数字可能恰好跨块，必须先读取后续分隔符。
            if end == len(self.buffer) and not self.eof:
                self.refill()
                continue
            self.position = end
            return result


def compact_samples(source):
    stream = JsonStream(source)
    while stream.peek() is not None:
        stream.expect('{')
        header = {}
        while True:
            key = stream.value()
            assert isinstance(key,str) and key not in header
            stream.expect(':')
            if key == 'increments':
                stream.expect('[')
                def rows():
                    for index in range(header['solution_count']):
                        if index:
                            stream.expect(',')
                        yield stream.value()
                    stream.expect(']')
                yield from restore(header,rows())
                stream.expect('}')
                break
            header[key] = stream.value()
            stream.expect(',')


def exact(source, size):
    data = source.read(size)
    if len(data) != size:
        raise EOFError('二进制样本已截断')
    return data


def value(source):
    tag = exact(source,1)[0]
    if tag <= 2:
        return [None,False,True][tag]
    if tag in (3,4,5):
        return struct.unpack({3:'<Q',4:'<q',5:'<d'}[tag],exact(source,8))[0]
    if tag in (6,7,8,9,10):
        count = struct.unpack('<I',exact(source,4))[0]
        if tag == 6:
            return exact(source,count).decode('utf-8')
        if tag == 7:
            return [value(source) for _ in range(count)]
        if tag == 8:
            result = {}
            for _ in range(count):
                key = value(source)
                assert isinstance(key,str) and key not in result
                result[key] = value(source)
            return result
        data = exact(source,(count+7)//8)
        assert count > 0
        if count%8:
            assert data[-1] >> (count%8) == 0
        text = ''.join(str((data[bit//8] >> (bit%8)) & 1) for bit in reversed(range(count)))
        return '#b'+text if tag == 10 else text
    raise ValueError(f'未知二进制值类型 {tag}')


def binary_summary(source):
    """从固定文件尾定位预算会话汇总，不扫描或展开组合。"""
    source.seek(-40,2)
    tail=struct.unpack('<QQQQQ',exact(source,40))
    assert tail[:3] == (0,0,0) and tail[4] == (1<<64)-1
    offset=tail[3]
    source.seek(offset)
    signature,cls,count,size,flags=struct.unpack('<QQQQQ',exact(source,40))
    assert (signature,cls,count,flags) == (0,0,0,2)
    reason,total,path_count,class_count=struct.unpack('<QQQQ',exact(source,32))
    assert reason in (0,1,2) and size == 32+32*(path_count+class_count)
    paths={}
    classes={}
    for index in range(path_count):
        path,signature,count,truncated=struct.unpack('<QQQQ',exact(source,32))
        assert path not in paths and truncated in (0,1)
        paths[path]=dict(path_signature=signature,combinations=count,truncated=bool(truncated))
    for index in range(class_count):
        path,cls,count,truncated=struct.unpack('<QQQQ',exact(source,32))
        assert path in paths and (path,cls) not in classes and truncated in (0,1)
        classes[path,cls]=dict(combinations=count,truncated=bool(truncated))
    assert sum(p['combinations'] for p in paths.values()) == total
    assert sum(c['combinations'] for c in classes.values()) == total
    assert source.tell() == offset+40+size
    assert struct.unpack('<QQQQQ',exact(source,40)) == tail and source.read(1) == b''
    return dict(reason={0:None,1:'output_budget',2:'no_progress'}[reason], combinations=total,
                paths=paths,classes=classes,offset=offset)


def binary_samples(source, selected=None):
    if exact(source,8) != b'ISLASB1\0':
        raise ValueError('二进制样本 magic 不匹配')
    version, header_size, record_size, metadata_size = struct.unpack('<IIII',exact(source,16))
    assert version in (1,2) and (header_size,record_size) == (24,40)
    metadata = json.loads(exact(source,metadata_size))
    assert metadata['schema_version'] == version and metadata['sample_schema_version'] == 1
    assert metadata['endianness'] == 'little' and metadata['payload_codec'] == 'typed-json-v1'
    assert metadata['fields'] == [['path_signature','u64',0],['class_id','u64',8],['solution_count','u64',16],
                                  ['payload_bytes','u64',24],['flags','u64',32]]
    start=source.tell()
    summary=binary_summary(source) if version == 2 else None
    source.seek(start)
    ordinal=0
    observed={}
    while True:
        signature, class_id, count, size, flags = struct.unpack('<QQQQQ',exact(source,40))
        if flags == (1<<64)-1:
            assert version == 1 and (signature,class_id,count,size) == (0,0,0,0) and source.read(1) == b''
            return
        if version == 2 and flags == 2:
            assert source.tell()-40 == summary['offset']
            assert ordinal == summary['combinations']
            if selected is None:
                assert observed == {key:entry['combinations'] for key,entry in summary['classes'].items()}
            return
        assert flags in (0,1) and count > 0
        if version == 2:
            assert source.tell()+size <= summary['offset']
        wanted = None if selected is None else {item-ordinal for item in selected if ordinal <= item < ordinal+count}
        ordinal += count
        if wanted == set():
            source.seek(size,1)
            continue
        end = source.tell()+size
        header = value(source)
        assert header['path_signature'] == signature and header['solution_count'] == count
        assert header['class_id'] == (None if class_id == (1<<64)-1 else class_id)
        if version == 2:
            path=header['path_nonce']
            key=(path,class_id)
            assert summary['paths'][path]['path_signature'] == signature
            observed[key]=observed.get(key,0)+count
        for index,sample in enumerate(restore(header,(value(source) for _ in range(count)))):
            assert sample['truncated'] == bool(flags)
            if version == 2:
                sample['truncated'] = summary['paths'][path]['truncated'] or summary['classes'][key]['truncated']
            if wanted is None or index in wanted:
                yield sample
        assert source.tell() == end, '类载荷长度不符'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--format',choices=['compact_jsonl','binary'],required=True)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--random',type=int,help='按组合均匀无放回抽取，流式二进制专用')
    parser.add_argument('--seed',type=int,default=11)
    args = parser.parse_args()
    assert args.input.resolve() != args.output.resolve()
    rows = 0
    with args.input.open('rb' if args.format == 'binary' else 'r') as source, args.output.open('x') as output:
        selected=None
        if args.random is not None:
            import random
            assert args.format == 'binary' and args.random > 0
            summary=binary_summary(source)
            selected=set(random.Random(args.seed).sample(range(summary['combinations']),min(args.random,summary['combinations'])))
            source.seek(0)
        samples = binary_samples(source,selected) if args.format == 'binary' else compact_samples(source)
        for sample in samples:
            output.write(json.dumps(sample,ensure_ascii=False,separators=(',',':'))+'\n')
            rows += 1
    print(f'已还原 {rows} 条 samples v1')


if __name__ == '__main__':
    main()
