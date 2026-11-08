"""汇总纯符号指令探索；区分进程结束、预算超时与完整收敛。"""
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'output/fuzz-seq-s1-symbolic'
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'pt_decode'))
from pt_decode import LOAD_FIELDS, STORE_FIELDS, MASK64, bit_value, exact, struct_value


def summarize(directory):
    done_path = directory / 'done.json'
    assert done_path.exists(), f'尚未结束：{directory}'
    done = json.loads(done_path.read_text())
    merge, forks = None, None
    statistics_final = False
    incomplete_statistics_lines = 0
    with (directory / 'stderr.txt').open() as stream:
        for line in stream:
            if line.startswith(('[MERGE_STATS', '[FORK_STATS')) and not line.endswith('\n'):
                assert done['timed_out'], '正常退出时统计行应已写完'
                incomplete_statistics_lines += 1
                continue
            if line.startswith(('[MERGE_STATS]', '[MERGE_STATS_SNAPSHOT]')):
                merge = json.loads(line.split('] ', 1)[1])
                statistics_final |= line.startswith('[MERGE_STATS]')
            elif line.startswith(('[FORK_STATS]', '[FORK_STATS_SNAPSHOT]')):
                forks = json.loads(line.split('] ', 1)[1])
    assert merge is not None and forks is not None, '进程未留下执行统计，须单独检查启动失败'
    clause = directory.name.split('-')[2].upper()
    raw_path = directory / f'output/rv64_z{clause}.json'
    summary, diagnostics, output_cases = None, None, None
    if raw_path.exists():
        raw = json.loads(raw_path.read_text())
        summary = raw['summary']
        diagnostics = dict(Counter(item.get('error', item['reason']) for item in raw['diagnostics']))
        output_cases = len(raw['gen'])
    samples = directory / 'samples.jsonl'
    addresses, signatures, classes, sample_ids = set(), set(), set(), set()
    registers = {'rs1': Counter(), 'rd' if clause == 'LOAD' else 'rs2': Counter()}
    encoding_registers = {name: Counter() for name in registers}
    encoding_domain_samples = 0
    immediates, widths = Counter(), Counter()
    exported = 0
    incomplete_last_line = False
    if samples.exists():
        with samples.open() as stream:
            for line in stream:
                if not line.endswith('\n'):
                    assert done['timed_out'], '正常结束的 JSONL 不应有未完成行'
                    incomplete_last_line = True
                    break
                sample = json.loads(line)
                assert sample['sample_id'] not in sample_ids, '导出的样本标识应唯一'
                sample_ids.add(sample['sample_id'])
                exported += 1
                instruction = sample['pre_registers']['$instruction']
                assert instruction['ctor'] == clause, '导出指令必须与场景 clause 一致'
                names = LOAD_FIELDS if clause == 'LOAD' else STORE_FIELDS
                fields = exact(struct_value(instruction['value']), names, f'{clause} 参数')
                immediate = bit_value(fields[names[0]], 12)
                immediate -= 4096 if immediate & 0x800 else 0
                first, second = (bit_value(fields[names[index]], 5) for index in (1, 2))
                rs1, other = (first, second) if clause == 'LOAD' else (second, first)
                registers['rs1'][f'x{rs1}'] += 1
                registers['rd' if clause == 'LOAD' else 'rs2'][f'x{other}'] += 1
                immediates[immediate] += 1
                width_value = fields[names[-1]]
                if 'bits' in width_value:
                    width = bit_value(width_value, 64)
                    width -= 1 << 64 if width & (1 << 63) else 0
                else:
                    width = int(exact(width_value, ['i64'], '访问宽度')['i64'])
                widths[str(width)] += 1
                # 原始语义样本在机器码编码过滤前导出；此处仅核对 RV64 构造子的编码参数域。
                # 这不是求解器认证，不改变样本或探索约束。
                unsigned = False
                if clause == 'LOAD':
                    unsigned = exact(fields[names[3]], ['bool'], 'LOAD 无符号标记')['bool']
                    assert type(unsigned) is bool
                if width in (1, 2, 4, 8) and not (clause == 'LOAD' and width == 8 and unsigned):
                    encoding_domain_samples += 1
                    encoding_registers['rs1'][f'x{rs1}'] += 1
                    encoding_registers['rd' if clause == 'LOAD' else 'rs2'][f'x{other}'] += 1
                base = bit_value(sample['pre_registers'][f'x{rs1}'], 64) if rs1 else 0
                addresses.add((base + immediate) & MASK64)
                signatures.add(sample['path_signature'])
                classes.add((sample['path_signature'], sample['class_id']))
    resources = directory / 'resources.jsonl'
    sampled_rss = []
    if resources.exists():
        sampled_rss = [row['VmRSS'] for line in resources.read_text().splitlines()
                       if 'VmRSS' in (row := json.loads(line))]
    return dict(
        seconds=done['seconds'], budget_seconds=done['limit_seconds'],
        timed_out=done['timed_out'], returncode=done['returncode'],
        max_rss_kib=done['max_rss_kib'], user_seconds=done['user_seconds'],
        system_seconds=done['system_seconds'], output_cases=output_cases,
        exported_samples=exported, exported_classes=len(classes),
        exported_path_signatures=len(signatures), distinct_effective_addresses=len(addresses),
        register_distribution={name: dict(counts) for name, counts in registers.items()},
        encoding_domain_samples=encoding_domain_samples,
        encoding_domain_register_distribution={name: dict(counts) for name, counts in encoding_registers.items()},
        distinct_immediates=len(immediates), access_width_distribution=dict(widths),
        merge_success_rate=merge['successes'] / merge['attempts'] if merge['attempts'] else None,
        peak_sampled_vmrss_kib=max(sampled_rss) if sampled_rss else None,
        incomplete_last_line=incomplete_last_line,
        effective_address_min=hex(min(addresses)) if addresses else None,
        effective_address_max=hex(max(addresses)) if addresses else None,
        addresses_not_aligned_to_8=any(value % 8 for value in addresses),
        merge=merge, forks=forks, summary=summary, diagnostics=diagnostics,
        statistics_final=statistics_final, incomplete_statistics_lines=incomplete_statistics_lines,
        fully_converged=(not done['timed_out'] and done['returncode'] == 0
                         and summary is not None and summary['status'] == 'finished'
                         and merge['merge_enumeration']['truncated_paths'] == 0))


if __name__ == '__main__':
    group = sys.argv[1] if len(sys.argv) > 1 else 'merged'
    directories = sorted((OUT / group).glob('*-export'))
    assert directories, '没有找到本轮导出目录'
    results = {directory.name: summarize(directory) for directory in directories}
    (OUT / group / 'analysis.json').write_text(json.dumps(results, ensure_ascii=False, indent=2) + '\n')
    for name, result in results.items():
        print(name, json.dumps({key: result[key] for key in
              ('seconds', 'max_rss_kib', 'exported_classes', 'timed_out', 'fully_converged')}, ensure_ascii=False))
