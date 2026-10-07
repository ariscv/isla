#!/usr/bin/env python3
"""执行各受支持IR的真实helper与FD状态回归，失败立即体现在最终退出码。"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--mode', choices=['helpers', 'state', 'all'], default='all')
args = parser.parse_args()
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
target = Path(os.environ.get('CARGO_TARGET_DIR', ROOT / 'target')).resolve()
env = dict(os.environ, CARGO_NET_OFFLINE='true', CARGO_TARGET_DIR=str(target))
checks = []


def run(label, command):
    with (output / (label + '.log')).open('w') as log:
        try:
            status = subprocess.run(list(map(str, command)), cwd=ROOT, env=env, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=120).returncode
        except subprocess.TimeoutExpired:
            status = 124
    checks.append({'label': label, 'command': list(map(str, command)), 'exit': status})
    (output / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    print(label, status, flush=True)
    return status


assert run('build', ['cargo', 'build', '--offline', '-q', '--manifest-path', ROOT / 'test/float_ir/runner/Cargo.toml']) == 0
for name in ['rv64d.ir', 'rv32d.ir', 'ir/rv64d_v128_e64.ir', 'ir/rv64d_v256_e64.ir', 'ir/rv64d_v512_e64.ir']:
    ir = ROOT / name
    label = ir.stem
    if args.mode in ('helpers', 'all'):
        text = ir.read_text()
        # 清单来自修前已声明的接口；RV32只有63项，不能按RV64清单虚增接口。
        cases = [line for line in (ROOT / 'test/float_ir/helpers.tsv').read_text().splitlines()
                 if re.search(r'^val z' + re.escape(line.split('\t')[0]) + r'\s*:', text, re.M)]
        assert cases, 'IR没有已声明的浮点接口'
        fixture = output / (label + '.tsv')
        fixture.write_text('\n'.join(cases) + '\n')
        wrapped = output / (label + '-wrapped.ir')
        rc = run(label + '-wrap', ['python3', ROOT / 'test/softfloat_legacy/wrap.py', '--ir', ir,
                                 '--cases', fixture, '--output', wrapped])
        if rc == 0:
            run(label + '-helpers', [target / 'debug/float-ir-helpers', wrapped, fixture])
    if args.mode in ('state', 'all'):
        for mode in ['state', 'guard']:
            run(label + '-' + mode, [target / 'debug/float-ir-state', ir, mode, ROOT / 'configs/riscv64_difftest_fd.toml'])
raise SystemExit(0 if all(check['exit'] == 0 for check in checks) else 1)
