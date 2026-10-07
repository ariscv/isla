#!/usr/bin/env python3
"""装配冻结Sail生成的浮点IR组件；严格检查依赖、绑定及来源位置。"""
import argparse
import hashlib
import json
from pathlib import Path
import re

TOP = re.compile(r'^(?:val|fn|enum|struct|union|register|let|files|#\w+)\b', re.M)
WORD = re.compile(r'\b(?:z\w+|have_exception|current_exception|throw_location)\b')
STRING = re.compile(r'"(?:\\.|[^"\\])*"')
LOC = re.compile(r' `\d+(?: \d+:\d+-\d+:\d+)?')


def normalized(text):
    names = {}
    def renamed(match):
        name = match[0]
        if name not in names:
            names[name] = f'z3zEN{len(names)}'
        return names[name]
    return re.sub(r'z3zE\d+', renamed, LOC.sub('', text)).strip()


def definitions(text):
    starts = [m.start() for m in TOP.finditer(text)] + [len(text)]
    assert starts[0] == 0, 'IR必须从顶层定义开始'
    result = {}
    owners = {}
    files = None
    pragmas = {}
    for start, end in zip(starts, starts[1:]):
        block = text[start:end]
        kind = block.split()[0]
        if kind == 'files':
            assert files is None, '重复files表'
            files = [json.loads(s) for s in STRING.findall(block)]
            key = ('files', '')
        elif kind.startswith('#'):
            key = (kind, block.split()[1] if kind == '#tuplestruct' else str(len(result)))
            if kind == '#tuplestruct':
                pragmas[key[1]] = block
        elif kind == 'let':
            names = re.findall(r'(z\w+)\s*:', block[:block.index('{')])
            assert names, 'let缺少绑定'
            key = (kind, names[0])
            for name in names:
                owners.setdefault(name, []).append(key)
        else:
            name = re.match(r'\w+\s+(\w+)', block)[1]
            key = (kind, name)
            owners.setdefault(name, []).append(key)
            if kind in ('struct', 'enum', 'union'):
                # 字段/constructor/enum成员同样依赖所属的完整类型定义。
                for token in re.findall(r'^\s+(z\w+)\s*(?=[:,\n])', block, re.M):
                    owners.setdefault(token, []).append(key)
        if key in result:
            assert kind == 'val' and normalized(result[key]) == normalized(block), f'重复定义冲突: {key}'
            key = ('duplicate-val', str(len(result)))
        result[key] = block
    assert files is not None, 'IR缺少files表'
    return result, owners, files, pragmas


def assemble(source, target, replace):
    src, owners, source_files, pragmas = definitions(source)
    dst, _, target_files, target_pragmas = definitions(target)
    if replace:
        roots = replace
        assert all(('fn', name) in src and ('fn', name) in dst for name in roots), '替换函数必须已存在'
        assert not all(normalized(src[('fn', name)]) == normalized(dst[('fn', name)]) for name in roots), '目标已经具有相同状态函数，拒绝重复装配'
    else:
        roots = sorted(name for kind, name in dst if kind == 'val' and name.startswith('zriscv_') and ('fn', name) not in dst)
        assert roots, '目标没有缺体浮点接口，拒绝重复迁移'
    required = set()
    reused = set()
    todo = [('fn', name) for name in roots]
    while todo:
        key = todo.pop()
        if key in required or key in reused:
            continue
        assert key in src, f'提供方缺少依赖: {key}'
        block = src[key]
        if key in dst and not (key[0] == 'fn' and key[1] in replace):
            if key[0] != 'fn' or not replace:
                assert normalized(block) == normalized(dst[key]), f'同名定义冲突: {key}'
            reused.add(key)
            if key[0] == 'struct':
                assert normalized(pragmas.get(key[1], '')) == normalized(target_pragmas.get(key[1], '')), f'元组字段顺序冲突: {key}'
            # 状态组件调用目标的架构专属函数，绝不导入提供方的SD位实现。
            if replace and key[0] in ('fn', 'let', 'register'):
                continue
        else:
            required.add(key)
        # 函数签名属于依赖，即使函数体里没显式出现其返回类型。
        if key[0] == 'fn':
            todo.append(('val', key[1]))
        for token in WORD.findall(STRING.sub('', block)):
            todo.extend(owners.get(token, []))
    assert not any(kind in ('register', 'let') for kind, _ in required), '不得迁入全局状态或初始化'
    new_files = list(target_files)
    mapping = {}
    for i, name in enumerate(source_files):
        if name not in new_files:
            new_files.append(name)
        mapping[i] = new_files.index(name)
    unique_ids = [int(x) for x in re.findall(r' `(\d+)(?=;)', target)]
    unique_offset = max(unique_ids, default=-1) + 1

    def relocated(block):
        block = re.sub(r' `(\d+)(?= \d+:\d+-)', lambda m: ' `' + str(mapping[int(m[1])]), block)
        return re.sub(r' `(\d+)(?=;)', lambda m: ' `' + str(unique_offset + int(m[1])), block)

    parts = []
    for key, block in dst.items():
        if key == ('files', ''):
            continue
        parts.append(relocated(src[key]) if key in required else block)
    for key, block in src.items():
        if key in required and key not in dst:
            parts.append(relocated(block))
            if key[0] == 'struct' and key[1] in pragmas:
                pragma_key = ('#tuplestruct', key[1])
                if pragma_key not in dst:
                    parts.append(pragmas[key[1]])
    parts.append('files ' + ' '.join(json.dumps(name) for name in new_files) + '\n')
    output = ''.join(parts)
    final, _, actual_files, _ = definitions(output)
    assert actual_files == new_files
    for key, block in dst.items():
        if key != ('files', '') and key not in required:
            assert final[key] == block, f'非目标定义被修改: {key}'
    for name in roots:
        assert ('fn', name) in final, f'缺少普通函数体: {name}'
    report = {'roots': sorted(roots), 'imported': sorted(required), 'reused': sorted(reused),
              'file_index_mapping': mapping, 'unknown_location_offset': unique_offset,
              'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
              'target_sha256': hashlib.sha256(target.encode()).hexdigest(),
              'output_sha256': hashlib.sha256(output.encode()).hexdigest()}
    return output, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-ir', type=Path, required=True)
    parser.add_argument('--target-ir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--replace', default='', help='逗号分隔的已有函数名；默认补齐缺体riscv接口')
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    replace = {name for name in args.replace.split(',') if name}
    assert replace <= {'zget_F_bits', 'zset_F_bits'}, '状态替换仅限已审查的FD访问接口'
    output, report = assemble(args.source_ir.read_text(), args.target_ir.read_text(), replace)
    args.output.write_text(output)
    args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(f'迁移{len(report["roots"])}接口，导入{len(report["imported"])}定义')


if __name__ == '__main__':
    main()
