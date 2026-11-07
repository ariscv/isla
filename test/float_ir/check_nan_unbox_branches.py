#!/usr/bin/env python3
"""检查所支持IR保留NaN-boxing显式分支；可核对FLEQ JSON的两侧见证。"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
IRS = ['rv64d.ir', 'rv32d.ir', 'ir/rv64d_v128_e64.ir',
       'ir/rv64d_v256_e64.ir', 'ir/rv64d_v512_e64.ir']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ir', type=Path, action='append')
    parser.add_argument('--fleq-json', type=Path)
    args = parser.parse_args()
    for path in args.ir or [ROOT / name for name in IRS]:
        text = path.read_text()
        function = re.search(r'(?ms)^fn znan_unbox\([^\n]*\n(.*?)^}', text)
        assert function, f'{path}: 缺少nan_unbox'
        body = function[1]
        jumps = re.findall(r'(?m)^\s*jump\b', body)
        assert len(jumps) == 2, f'{path}: 应保留等宽与boxing两个显式判断，实际{len(jumps)}个jump'
        assert re.search(r'= zeq_bits\(', body), f'{path}: 缺少boxing高位比较'
        assert not re.search(r'= zite(?:zI\w*)?\(', body), f'{path}: boxing不能合并为ITE'
        print(f'PASS {path}: 等宽和boxing显式判断均保留')
    if args.fleq_json:
        data = json.loads(args.fleq_json.read_text())
        patterns = set()
        for item in data['gen']:
            if not item['ret_val'].startswith('Retire_Success'):
                continue
            regs = re.findall(r'\bf\d+\b', item['test-ins'])
            assert len(regs) == 2, '要求FLEQ.S的两个源FPR'
            values = [item['isa-state-complete'][reg] for reg in regs]
            bits = [int(value.split("'h")[1].replace('_', ''), 16) for value in values]
            patterns.add(tuple(value >> 32 == 0xffffffff for value in bits))
        # 单独确保有全有效和至少一个无效源；不假定寄存器别名允许四种组合。
        assert (True, True) in patterns, f'缺少两个源均有效boxing的见证：{patterns}'
        assert any(not all(pattern) for pattern in patterns), f'缺少无效boxing见证：{patterns}'
        print(f'PASS FLEQ.S boxing见证：{sorted(patterns)}')


if __name__ == '__main__':
    main()
