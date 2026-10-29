"""给完整模型 IR 的测试副本追加纯调用包装器，不修改正式 IR。"""
import argparse
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--ir', type=Path, required=True)
parser.add_argument('--cases', type=Path, default=Path(__file__).with_name('cases.tsv'))
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
full = args.ir.read_text()
names = sorted({line.split('\t', 1)[0] for line in args.cases.read_text().splitlines() if line})
blocks = []
for name in names:
    match = re.search(rf'^val z{re.escape(name)}\s*:\s*\(([^)]*)\)\s*->\s*(.+)$', full, re.M)
    assert match, f'missing declaration: {name}'
    assert re.search(rf'^fn z{re.escape(name)}\(', full, re.M), f'missing ordinary body: {name}'
    argument_names = ', '.join(f'za{i}' for i in range(len(match.group(1).split(','))))
    blocks.append(f'val zd_probe_{name} : ({match.group(1)}) -> {match.group(2)}\n'
                  f'fn zd_probe_{name}({argument_names}) {{\n  return = z{name}({argument_names});\n  end;\n}}\n')
args.output.write_text(full + '\n' + '\n'.join(blocks))
print(f'added {len(names)} wrappers')
