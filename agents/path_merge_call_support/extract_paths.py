#!/usr/bin/env python3
"""把已保存的 Isla 迹转换成逐路径 SMT-LIB；只接受本次实测出现的表达式。"""
import json
from pathlib import Path
import re

base = Path(__file__).resolve().parent
raw = (base / 'logs/pte_no_merge.stdout').read_text()
chunks = re.split(r'^Result: ', raw, flags=re.MULTILINE)
assert chunks[0] == '', '输出包含结果以外的信息，需人工检查'
out = base / 'paths'
out.mkdir(exist_ok=True)
summary = []
for index, chunk in enumerate(chunks[1:], 1):
    result, trace = chunk.split('\n', 1)
    assert trace.startswith('(trace\n')
    definitions = []
    conditions = []
    for line in trace.splitlines()[1:]:
        expression = line.strip().split(' ; ', 1)[0]
        if expression.startswith('(declare-const '):
            match = re.fullmatch(r'\(declare-const (v\d+) \(_ BitVec (8|10)\)\)', expression)
            assert match, expression
            symbol, width = match.groups()
            source = 'pte_flags' if width == '8' else 'pte_ext'
            definitions.append(f'(define-fun {symbol} () (_ BitVec {width}) {source})')
        elif expression.startswith('(define-const '):
            match = re.fullmatch(r'\(define-const (v\d+) (.*)\)', expression)
            assert match, expression
            symbol, body = match.groups()
            extract = re.fullmatch(r'\(\(_ extract (\d+) (\d+)\) v\d+\)', body)
            if extract:
                high, low = map(int, extract.groups())
                sort = f'(_ BitVec {high-low+1})'
            else:
                assert body.startswith('(= ') or body.startswith('(not '), body
                sort = 'Bool'
            definitions.append(f'(define-fun {symbol} () {sort} {body})')
        elif expression.startswith('(assert '):
            assert expression.endswith(')')
            conditions.append(expression[len('(assert '):-1])
        else:
            assert expression.startswith(('(branch ', '(define-enum ', '(read-reg ', '(write-reg ')), expression
    assert result == 'true' or re.fullmatch(r'v\d+', result), result
    condition = '(and ' + ' '.join(conditions) + ')'
    script = '\n'.join([
        '; 从实测迹转换；输入名归一化，枚举及寄存器事件保存在原始迹中。',
        '; 返回值保留符号表达式；get-value 的模型值不代表恒定返回值。',
        '(set-logic QF_BV)', '(set-option :produce-models true)',
        '(declare-const pte_flags (_ BitVec 8))',
        '(declare-const pte_ext (_ BitVec 10))', *definitions,
        f'(define-fun path_condition () Bool {condition})',
        f'(define-fun result () Bool {result})', '(assert path_condition)',
        '(check-sat)', '(get-value (result))', '',
    ])
    filename = f'path-{index:02d}.smt2'
    (out / filename).write_text(script)
    summary.append(dict(path=index, result=result, assertions=conditions, file=filename))
(out / 'index.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2)+'\n')
print(f'已导出 {len(summary)} 条路径')
