#!/usr/bin/env python3
"""检查特殊值、分类、合法性和活动lane的行为分界没有再次合并为ITE。"""
import argparse
from pathlib import Path
import re
import shlex

ROOT = Path(__file__).resolve().parents[2]
IRS = ['rv64d.ir', 'rv32d.ir', 'ir/rv64d_v128_e64.ir',
       'ir/rv64d_v256_e64.ir', 'ir/rv64d_v512_e64.ir']
# 下界来自恢复前后的完整IR；包含原有类型/位宽检查，不能仅要求存在Jump。
MIN_JUMPS = {
    'zfp_min_pure': 8,
    'zfp_max_pure': 8,
    'zfp_minm_pure': 1,
    'zfp_maxm_pure': 1,
    'zriscv_f32_symbolic_bits': 1,
    'zfp_class_onehot_pure': 17,
    'zvalid_fp_op': 3,
    'zillegal_fp_normal': 3,
    'zillegal_fp_reduction': 3,
}


def check_mask_control(text, functions, path):
    """核对本轮两个循环：mask Jump 支配纯运算，关闭该lane会绕过运算。"""
    files_line = re.search(r'(?m)^files (.*)$', text)
    assert files_line, f'{path}: 缺少源码文件表'
    files = shlex.split(files_line.group(1))
    instructions = [line.strip() for line in functions['zexecute'].splitlines() if line.strip()]

    def successors(pc):
        instruction = instructions[pc]
        target = re.search(r'\bgoto (\d+)', instruction)
        if instruction.startswith('jump '):
            return [pc + 1, int(target.group(1))]
        if instruction.startswith('goto '):
            return [int(target.group(1))]
        if instruction == 'end;':
            return []
        return [pc + 1] if pc + 1 < len(instructions) else []

    def reachable(start, stop):
        visited, pending = set(), [start]
        while pending:
            pc = pending.pop()
            if pc in visited or pc == stop:
                continue
            visited.add(pc)
            pending.extend(successors(pc))
        return visited

    # 固定本次审核过的源码区间。源码漂移时应重新核对测试，而非放宽为总Jump计数。
    for name, source, line, expected_operations in [
            ('FVVTYPE', 'extensions/V/vext_fp_insts.sail', 67, 6),
            ('RFVVTYPE', 'extensions/V/vext_fp_red_insts.sail', 62, 4)]:
        source_id = files.index(source)
        location = re.compile(r'`' + str(source_id) + r' (\d+):\d+-(\d+):\d+;')
        mask_jumps = []
        for pc, instruction in enumerate(instructions):
            match = location.search(instruction)
            if match and int(match.group(1)) == line and int(match.group(2)) > line:
                jump = re.match(r'jump (\w+) goto (\d+)', instruction)
                if jump:
                    mask_jumps.append((pc, jump.group(1), int(jump.group(2)), int(match.group(2))))
        assert len(mask_jumps) == 1, f'{path}: {name}缺少唯一mask Jump'
        branch, condition, active, end_line = mask_jumps[0]
        prefix = instructions[max(0, branch - 15):branch]
        definitions = {}
        for instruction in prefix:
            assignment = re.match(r'(\w+) = (.*?) `', instruction)
            if assignment:
                definitions[assignment.group(1)] = assignment.group(2)

        def resolve(value):
            visited = set()
            while value in definitions and value not in visited:
                visited.add(value)
                value = definitions[value]
            return value

        comparison = re.fullmatch(r'zeq_bits\((\w+), (\w+)\)', definitions.get(condition, ''))
        assert comparison, f'{path}: {name}mask条件不是位比较'
        operands = [resolve(value) for value in comparison.groups()]
        assert '0b1' in operands and any(value.startswith('zbitvector_access(') for value in operands), \
            f'{path}: {name}mask条件不是活动位与1的比较'
        # Sail iif 的 false出口为 unit赋值后goto合流点；true目标进入运算体。
        assert instructions[branch + 2].startswith('goto '), f'{path}: {name}非活动出口结构变化'
        merge = int(re.search(r'goto (\d+)', instructions[branch + 2]).group(1))
        on_active = reachable(active, merge)
        on_inactive = reachable(branch + 1, merge)
        without_branch = reachable(0, branch)
        operations = []
        for pc, instruction in enumerate(instructions):
            match = location.search(instruction)
            if match and line < int(match.group(1)) <= end_line and re.search(r'= zfp_\w+_pure\(', instruction):
                operations.append(pc)
        assert len(operations) == expected_operations, f'{path}: {name}纯运算调用数变化: {len(operations)}'
        assert all(pc in on_active for pc in operations), f'{path}: {name}活动分支不能到达全部运算'
        assert all(pc not in on_inactive for pc in operations), f'{path}: {name}非活动分支仍执行运算'
        assert all(pc not in without_branch for pc in operations), f'{path}: {name}mask Jump不支配运算'
        print(f'PASS {path}: {name} mask Jump支配{len(operations)}处纯运算，非活动lane绕过运算')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ir', type=Path, action='append')
    args = parser.parse_args()
    for path in args.ir or [ROOT / name for name in IRS]:
        text = path.read_text()
        functions = dict(re.findall(r'(?ms)^fn ([^(\n]+)\([^\n]*\) \{\n(.*?)^\}', text))
        for name, minimum in MIN_JUMPS.items():
            assert name in functions, f'{path}: 缺少{name}'
            count = len(re.findall(r'(?m)^\s*jump\b', functions[name]))
            assert count >= minimum, f'{path}: {name}仅有{count}个Jump，预期至少{minimum}'
        check_mask_control(text, functions, path)
        print(f'PASS {path}: 已恢复行为分界保留显式Jump')


if __name__ == '__main__':
    main()
