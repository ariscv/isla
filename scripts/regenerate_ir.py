#!/usr/bin/env python3
"""从干净模型源码生成严格SYMBOLIC IR，并记录实际输入及工具哈希。"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

PRESERVE = ('encdec_compressed_forwards', 'encdec_compressed_forwards_matches',
            'encdec_compressed_backwards', 'encdec_compressed_backwards_matches',
            'get_F', 'set_F', 'set_V', 'riscv_f16ToI16', 'riscv_f16ToUi16',
            'riscv_f32ToI16', 'riscv_f32ToUi16')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['model', 'plugin', 'config', 'output']:
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('--sail', default='sail')
    parser.add_argument('--name', default='rv64d')
    args = parser.parse_args()
    repo = args.model.resolve()
    if subprocess.check_output(['git', '-C', str(repo), 'status', '--porcelain']):
        parser.error('模型仓有未提交改动，请先固定来源提交')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output/(args.name+'.ir')).exists():
        parser.error('输出IR已存在；请使用新目录')
    sail = Path(shutil.which(args.sail) or args.sail).resolve()
    config, plugin = args.config.resolve(), args.plugin.resolve()
    sources = {str(p.relative_to(repo/'model')):digest(p) for p in (repo/'model').rglob('*') if p.is_file()}
    command = [str(sail), '-plugin', str(plugin), '-isla', '-D', 'SYMBOLIC',
               '--strict-var', '--strict-bitvector', '--strict-exponentials',
               '--require-version', '0.20.1', '--memo-z3-path', str(output/'sail_smt_cache'), '--all-modules']
    for name in PRESERVE:
        command += ['--isla-preserve', name]
    command += ['--isla-output-dir', str(output), '--config', str(config), '-o', args.name, 'riscv.sail_project']
    record = {'model_commit':subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip(),
              'model_files':sources, 'config_sha256':digest(config), 'plugin_sha256':digest(plugin),
              'sail_launcher_sha256':digest(sail), 'sail_version':subprocess.check_output([str(sail), '--version'], text=True).strip(),
              'command':command}
    start = time.monotonic()
    with (output/'generation.log').open('w') as log:
        result = subprocess.run(command, cwd=repo/'model', stdout=log, stderr=subprocess.STDOUT)
    assert all(digest(repo/'model'/name) == sha for name,sha in sources.items()), '生成期间模型源码发生变化'
    record.update(exit_code=result.returncode, seconds=time.monotonic()-start)
    ir = output/(args.name+'.ir')
    if result.returncode == 0:
        record['ir_sha256'] = digest(ir)
    (output/'generation.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n')
    raise SystemExit(result.returncode)

if __name__ == '__main__':
    main()
