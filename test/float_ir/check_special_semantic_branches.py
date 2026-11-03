#!/usr/bin/env python3
"""检查特殊值源角色、NaN出口及20个活动lane的真实IR控制分界。"""
import argparse
from pathlib import Path
import re
import shlex
from check_float_closure_branches import check_narrow, check_operand_order

ROOT = Path(__file__).resolve().parents[2]
IRS = ['rv64d.ir', 'rv32d.ir', 'ir/rv64d_v128_e64.ir',
       'ir/rv64d_v256_e64.ir', 'ir/rv64d_v512_e64.ir']
# 模型a9fd947审核位置；源码位置变化时重新核对，不能改成总Jump下界。
GATES = [
    ('FVVMATYPE', 'extensions/V/vext_fp_insts.sail', 208, 221, 8),
    ('FWVVTYPE', 'extensions/V/vext_fp_insts.sail', 343, 353, 5),
    ('FWVVMATYPE', 'extensions/V/vext_fp_insts.sail', 471, 482, 6),
    ('FWVTYPE', 'extensions/V/vext_fp_insts.sail', 599, 607, 3),
    ('VFUNARY0', 'extensions/V/vext_fp_insts.sail', 746, 799, 18),
    ('VFWUNARY0', 'extensions/V/vext_fp_insts.sail', 1065, 1126, 16),
    ('VFNUNARY0', 'extensions/V/vext_fp_insts.sail', 1418, 1487, 20),
    ('VFUNARY1', 'extensions/V/vext_fp_insts.sail', 1730, 1743, 4),
    ('FVFTYPE', 'extensions/V/vext_fp_insts.sail', 1955, 1973, 8),
    ('FVFMATYPE', 'extensions/V/vext_fp_insts.sail', 2119, 2132, 8),
    ('FWVFTYPE', 'extensions/V/vext_fp_insts.sail', 2252, 2262, 5),
    ('FWVFMATYPE', 'extensions/V/vext_fp_insts.sail', 2378, 2389, 6),
    ('FWFTYPE', 'extensions/V/vext_fp_insts.sail', 2505, 2513, 3),
    ('RFWVVTYPE', 'extensions/V/vext_fp_red_insts.sail', 195, 200, 2),
    ('FVVMTYPE', 'extensions/V/vext_fp_vm_insts.sail', 61, 70, 4),
    ('FVFMTYPE', 'extensions/V/vext_fp_vm_insts.sail', 183, 194, 6),
    ('VFNCVTBF16_F_F_W', 'extensions/bfloat16/zvfbfmin_insts.sail', 51, 55, 1),
    ('VFWCVTBF16_F_F_V', 'extensions/bfloat16/zvfbfmin_insts.sail', 151, 155, 1),
    ('VFWMACCBF16_VV', 'extensions/bfloat16/zvfbfwma_insts.sail', 53, 60, 3),
    ('VFWMACCBF16_VF', 'extensions/bfloat16/zvfbfwma_insts.sail', 157, 164, 3),
]


def parse_functions(text):
    return dict(re.findall(r'(?ms)^fn ([^(\n]+)\([^\n]*\) \{\n(.*?)^\}', text))


def check(text, path):
    functions = parse_functions(text)
    assert 'zieee_operand_invalid' in functions, f'{path}: 缺少独立源NaN行为helper'
    helper = [line.strip() for line in functions['zieee_operand_invalid'].splitlines() if line.strip()]
    jumps = [i for i, line in enumerate(helper) if line.startswith('jump ')]
    assert len(jumps) == 2, f'{path}: 源helper须有NaN和sNaN两个Jump'
    for pc, predicate in zip(jumps, ['zieee_is_nan', 'zieee_is_snan']):
        condition = re.match(r'jump (\w+) goto ', helper[pc]).group(1)
        assert any(re.match(re.escape(condition) + r' = ' + predicate + r'\(', line)
                   for line in helper[:pc]), f'{path}: 源helper分支未使用{predicate}'

    operand_count = 0
    for width in [16, 32, 64]:
        for op, roles in [('eq', 'ab'), ('lt', 'ab'), ('add', 'ab'), ('sub', 'ab'),
                          ('mul', 'ab'), ('div', 'ab'), ('sqrt', 'a'), ('fma', 'abc')]:
            name = 'zieee_' + op + str(width) + '_exceptions'
            body = functions[name]
            assignments = dict(re.findall(r'(?m)^\s*(\w+) = (.*?) `', body))

            def resolve(value):
                seen = set()
                while value in assignments and value not in seen:
                    seen.add(value)
                    value = assignments[value]
                return value

            calls = re.findall(r'= zieee_operand_invalid\((\w+), (\w+)\)', body)
            assert len(calls) == len(roles), f'{path}: {name}源角色调用数变化'
            assert [resolve(raw) for mode, raw in calls] == ['z' + role for role in roles], \
                f'{path}: {name}源角色次序或参数变化'
            expected_mode = 'zsignaling' if op == 'lt' else 'false'
            assert all(resolve(mode) == expected_mode for mode, raw in calls), \
                f'{path}: {name}quiet/ordered模式变化'
            check_operand_order(name, [line.strip() for line in body.splitlines() if line.strip()],
                                len(roles))
            operand_count += 1

    # 规范化出口须是真分支；ROD模式选择和普通数值ITE不在这里机械禁止。
    outputs = ['zriscv_f16' + name for name in ['Add', 'Sub', 'Mul', 'Div', 'MulAdd',
               'Sqrt', 'roundToInt', 'ToF32', 'ToF64']]
    outputs += ['zriscv_f64_result_bits', 'zriscv_f64ToF16', 'zriscv_f64ToF32',
                'zriscv_f32ToF64', 'zriscv_f32ToF16', 'zriscv_f32ToBF16']
    for name in outputs:
        body = functions[name]
        definitions = dict(re.findall(r'(?m)^\s*(\w+) = (.*?) `', body))
        conditions = re.findall(r'(?m)^\s*jump (\w+) goto ', body)
        assert any(re.match(r'z(?:fp(?:16|32|64)_is_nan|ieee_is_nan)\(',
                            definitions.get(condition, '')) for condition in conditions), \
            f'{path}: {name}缺少由NaN谓词控制的出口Jump'
    assert len(re.findall(r'= zfp32_fma\(', functions['zriscv_f32MulAdd'])) == 1, \
        f'{path}: f32融合运算必须调用一次fp32_fma'
    assert not re.search(r'= zfp32_(?:add|mul)\(', functions['zriscv_f32MulAdd']), \
        f'{path}: f32融合运算被拆成乘加'

    # 与完整闭环回归共用真实overflow/符号/NV/端点控制检查。
    narrow = [line.strip() for line in functions['zriscv_f16ToI16_pure'].splitlines()
              if line.strip()]
    check_narrow('zriscv_f16ToI16_pure', narrow, 16, True)
    print(f'PASS {path}: f16转i16的两端饱和与NV仍受目标Jump控制')

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

    for name, source, line, end_line, expected_operations in GATES:
        source_id = files.index(source)
        location = re.compile(r'`' + str(source_id) + r' (\d+):\d+-(\d+):\d+;')
        branches = [pc for pc, instruction in enumerate(instructions)
                    if instruction.startswith('jump ') and (match := location.search(instruction))
                    and int(match.group(1)) == line and int(match.group(2)) == end_line]
        assert len(branches) == 1, f'{path}: {name}缺少唯一活动lane Jump'
        branch = branches[0]
        condition, active = re.match(r'jump (\w+) goto (\d+)', instructions[branch]).groups()
        definitions = dict(re.findall(r'^(\w+) = (.*?) `', '\n'.join(instructions[max(0, branch - 15):branch]), re.M))

        def resolve(value):
            seen = set()
            while value in definitions and value not in seen:
                seen.add(value)
                value = definitions[value]
            return value

        comparison = re.fullmatch(r'zeq_bits\((\w+), (\w+)\)', definitions.get(condition, ''))
        assert comparison, f'{path}: {name}活动条件不是位比较'
        operands = [resolve(value) for value in comparison.groups()]
        assert '0b1' in operands and any(value.startswith('zbitvector_access(') for value in operands), \
            f'{path}: {name}活动条件不是mask位与1的比较'
        assert instructions[branch + 2].startswith('goto '), f'{path}: {name}非活动出口结构变化'
        merge = int(re.search(r'goto (\d+)', instructions[branch + 2]).group(1))
        on_active = reachable(int(active), merge)
        on_inactive = reachable(branch + 1, merge)
        without_branch = reachable(0, branch)
        operations = []
        for pc, instruction in enumerate(instructions):
            match = location.search(instruction)
            if match and line < int(match.group(1)) < end_line and re.search(
                    r'= z(?:fp_\w+_pure|riscv_f\w+|riscv_[ui]\w+ToF\w+|bf16_to_f32)\(', instruction):
                operations.append(pc)
        assert len(operations) == expected_operations, f'{path}: {name}纯运算数变化: {len(operations)}'
        assert all(pc in on_active for pc in operations), f'{path}: {name}活动出口漏运算'
        assert all(pc not in on_inactive for pc in operations), f'{path}: {name}不活动出口仍执行运算'
        assert all(pc not in without_branch for pc in operations), f'{path}: {name}mask Jump不支配运算'
        # VF的scalar与向量转换、累加器FMA均在这3个活动调用中。
        if name == 'VFWMACCBF16_VF':
            assert sum('= zbf16_to_f32(' in instructions[pc] for pc in operations) == 2
        print(f'PASS {path}: {name}活动Jump支配{len(operations)}处运算')
    print(f'PASS {path}: 20个活动gate、{operand_count}个异常helper独立源、NaN出口与单次FMA')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ir', type=Path, action='append')
    args = parser.parse_args()
    for path in args.ir or [ROOT / name for name in IRS]:
        check(path.read_text(), path)


if __name__ == '__main__':
    main()
