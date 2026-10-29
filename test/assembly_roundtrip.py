#!/usr/bin/env python3
"""用GCC和Clang驱动汇编JSON文本，逐条核对机器编码；任一失败即退出非零。"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('json', type=Path, nargs='+')
    parser.add_argument('--march', default='rv64gcv_zfh_zfa_zfbfmin_zvfbfmin_zvfbfwma')
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    drivers = {'gcc': [shutil.which('riscv64-unknown-elf-gcc')],
               'clang': [shutil.which('clang'), '--target=riscv64-unknown-elf']}
    assert all(command[0] for command in drivers.values()), '必须同时安装GCC和Clang'
    objcopy = shutil.which('riscv64-unknown-elf-objcopy')
    assert objcopy
    records = []
    with tempfile.TemporaryDirectory(prefix='isla-assembly-') as directory:
        directory = Path(directory)
        for source in args.json:
            data = json.loads(source.read_text())
            for index, item in enumerate(data['gen']):
                text, encoding = item['test-ins'], item['test-ins-encdec']
                width, bits = encoding.replace('_', '').split("'h")
                expected = int(bits, 16).to_bytes((int(width) + 7) // 8, 'little')
                (directory/'probe.s').write_text('.text\n.option norelax\n'+text+'\n')
                for driver, command in drivers.items():
                    march = ['-march=rv64gcv_zfh_zfa', '-Wa,-march='+args.march] if driver == 'gcc' else ['-march='+args.march]
                    cmd = [*command, *march, '-mabi=lp64d', '-c', str(directory/'probe.s'), '-o', str(directory/'probe.o')]
                    result = subprocess.run(cmd, capture_output=True, text=True)
                    actual = None
                    if result.returncode == 0:
                        subprocess.run([objcopy, '-O', 'binary', '-j', '.text', str(directory/'probe.o'), str(directory/'probe.bin')], check=True)
                        actual = (directory/'probe.bin').read_bytes()
                    records.append({'source':str(source), 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                                    'index':index, 'driver':driver, 'command':cmd, 'instruction':text,
                                    'expected':expected.hex(), 'actual':actual.hex() if actual is not None else None,
                                    'exit':result.returncode, 'error':result.stderr, 'pass':actual == expected})
    report = {'versions':{name:subprocess.check_output([command[0], '--version'], text=True).splitlines()[0] for name,command in drivers.items()}, 'checks':records}
    args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(f'{sum(r["pass"] for r in records)}/{len(records)} GCC/Clang往返检查通过')
    raise SystemExit(0 if records and all(r['pass'] for r in records) else 1)

if __name__ == '__main__':
    main()
