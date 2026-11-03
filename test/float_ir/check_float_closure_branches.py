#!/usr/bin/env python3
"""检查浮点异常、窄饱和、ROD与flags的实际IR控制关系。"""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
IRS = ('rv64d.ir', 'rv32d.ir', 'ir/rv64d_v128_e64.ir',
       'ir/rv64d_v256_e64.ir', 'ir/rv64d_v512_e64.ir')
NARROW = {'zriscv_f16ToI16_pure': (16, True), 'zriscv_f16ToI8_pure': (8, True),
          'zriscv_f16ToUi8_pure': (8, False), 'zriscv_f16ToUi16_pure': (16, False),
          'zriscv_f32ToI16_pure': (16, True), 'zriscv_f32ToUi16_pure': (16, False)}
EXCEPTION_CALLS = {
    'add': ((('inf', 'a'), ('inf', 'b')),
            (('finite', 'a'), ('finite', 'b'))),
    'sub': ((('inf', 'a'), ('inf', 'b')),
            (('finite', 'a'), ('finite', 'b'))),
    'mul': ((('zzero', 'a'), ('inf', 'b')),
            (('inf', 'a'), ('zzero', 'b')),
            (('finite', 'a'), ('finite', 'b'))),
    'div': ((('zzero', 'a'), ('zzero', 'b')),
            (('inf', 'a'), ('inf', 'b')),
            (('finite', 'a'), ('zzero', 'a'), ('zzero', 'b')),
            (('finite', 'a'), ('finite', 'b'), ('zzero', 'b'))),
    'sqrt': ((('nan', 'a'), ('zzero', 'a')),
             (('finite', 'a'), ('zzero', 'a'), ('zzero', 'a'))),
    'fma': ((('zzero', 'a'), ('inf', 'b')),
            (('inf', 'a'), ('zzero', 'b')),
            (('inf', 'c'), ('zzero', 'a'), ('nan', 'a'), ('inf', 'b'),
             ('zzero', 'b'), ('nan', 'b'), ('inf', 'a')),
            (('finite', 'a'), ('finite', 'b'), ('finite', 'c'))),
}


def representative_values(width):
    exponent_width = {16: 5, 32: 8, 64: 11}[width]
    fraction_width = width - exponent_width - 1
    inf = ((1 << exponent_width) - 1) << fraction_width
    normal = ((1 << (exponent_width - 1)) - 1) << fraction_width
    base = (normal, 1, 0, inf, inf | 1, inf | (1 << (fraction_width - 1)))
    return tuple(value | sign << (width - 1) for value in base for sign in (0, 1))


def classify(value, width):
    exponent_width = {16: 5, 32: 8, 64: 11}[width]
    fraction_width = width - exponent_width - 1
    exponent = (value >> fraction_width) & ((1 << exponent_width) - 1)
    fraction = value & ((1 << fraction_width) - 1)
    nan = exponent == (1 << exponent_width) - 1 and fraction != 0
    inf = exponent == (1 << exponent_width) - 1 and fraction == 0
    zero = exponent == 0 and fraction == 0
    return {'sign': bool(value >> (width - 1)), 'nan': nan,
            'snan': nan and not bool(fraction & (1 << (fraction_width - 1))),
            'inf': inf, 'zero': zero, 'finite': not nan and not inf}


def arguments(expression_text):
    parts, current, level = [], '', 0
    for char in expression_text:
        if char == ',' and level == 0:
            parts.append(current.strip())
            current = ''
            continue
        current += char
        if char == '(':
            level += 1
        elif char == ')':
            level -= 1
    parts.append(current.strip())
    assert level == 0
    return parts


def evaluate(value, definitions, values, width):
    if value in values:
        return values[value]
    if value == 'true':
        return True
    if value == 'false':
        return False
    if value.startswith('0b'):
        return int(value[2:], 2)
    if value not in definitions:
        raise AssertionError(f'布尔谓词含未知变量 {value}')
    rhs = definitions[value]
    if re.fullmatch(r'zz\d+|za|zb|zc', rhs):
        return evaluate(rhs, definitions, values, width)
    match = re.fullmatch(r'(\w+)\((.*)\)', rhs)
    assert match, f'未知布尔表达式 {rhs}'
    op, raw = match.groups()
    if op == 'zz5i64zDzKz5i':
        return int(raw)
    args = [evaluate(arg, definitions, values, width) for arg in arguments(raw)]
    if op == 'zbitvector_access':
        return (args[0] >> args[1]) & 1
    if op.startswith('zeq_anything'):
        return args[0] == args[1]
    if op == 'zstrict_and_bool':
        return bool(args[0]) and bool(args[1])
    if op == 'zstrict_or_bool':
        return bool(args[0]) or bool(args[1])
    if op == 'znot_bool':
        return not args[0]
    if op == 'zieee_operand_invalid':
        return classify(args[1], width)['snan'] or bool(args[0]) and classify(args[1], width)['nan']
    if op.startswith('zieee_is_'):
        category = op.removeprefix('zieee_is_').replace('zzero', 'zero')
        assert category in ('nan', 'inf', 'zero', 'finite')
        return classify(args[0], width)[category]
    raise AssertionError(f'未支持的原因谓词操作 {op}')


def expected_exception_guards(op, raw, width):
    a = classify(raw[0], width)
    b = classify(raw[1], width) if len(raw) > 1 else None
    c = classify(raw[2], width) if len(raw) > 2 else None
    if op == 'add':
        return (a['inf'] and b['inf'] and a['sign'] != b['sign'],
                a['finite'] and b['finite'])
    if op == 'sub':
        return (a['inf'] and b['inf'] and a['sign'] == b['sign'],
                a['finite'] and b['finite'])
    if op == 'mul':
        return (a['zero'] and b['inf'], a['inf'] and b['zero'],
                a['finite'] and b['finite'])
    if op == 'div':
        return (a['zero'] and b['zero'], a['inf'] and b['inf'],
                a['finite'] and not a['zero'] and b['zero'],
                a['finite'] and b['finite'] and not b['zero'])
    if op == 'sqrt':
        negative_nonzero = a['sign'] and not a['zero']
        return (not a['nan'] and negative_nonzero,
                a['finite'] and not negative_nonzero or a['zero'])
    if op == 'fma':
        product_inf = (a['inf'] and not b['nan'] and not b['zero'] or
                       b['inf'] and not a['nan'] and not a['zero'])
        return (a['zero'] and b['inf'], a['inf'] and b['zero'],
                product_inf and c['inf'] and ((a['sign'] != b['sign']) != c['sign']),
                a['finite'] and b['finite'] and c['finite'])
    raise AssertionError(op)


def functions(text):
    return {name: [line.strip() for line in body.splitlines() if line.strip()]
            for name, body in re.findall(r'(?ms)^fn ([^(\n]+)\([^\n]*\) \{\n(.*?)^\}', text)}


def defs(lines):
    return {match.group(1): match.group(2) for line in lines
            if (match := re.match(r'(\w+) = (.*?) `', line))}


def successors(lines, pc):
    line = lines[pc]
    target = re.search(r'\bgoto (\d+)', line)
    if line.startswith('jump '):
        return (pc + 1, int(target.group(1)))
    if line.startswith('goto '):
        return (int(target.group(1)),)
    if line == 'end;':
        return ()
    return (pc + 1,) if pc + 1 < len(lines) else ()


def reachable(lines, start, stop=None):
    seen, pending = set(), [start]
    while pending:
        pc = pending.pop()
        if pc in seen or pc == stop:
            continue
        assert 0 <= pc < len(lines), (start, pc)
        seen.add(pc)
        pending.extend(successors(lines, pc))
    return seen


def jump(lines, pc):
    match = re.match(r'jump (\w+) goto (\d+)', lines[pc])
    assert match, (pc, lines[pc])
    return match.group(1), pc + 1, int(match.group(2))


def uses(value, target, definitions, seen=None):
    if value == target:
        return True
    seen = set() if seen is None else seen
    if value in seen or value not in definitions:
        return False
    seen.add(value)
    return any(uses(token, target, definitions, seen.copy())
               for token in re.findall(r'\b(?:zz\d+|zflags)\b', definitions[value]))


def resolves_to(value, pattern, definitions):
    seen = set()
    while value in definitions and value not in seen:
        seen.add(value)
        value = definitions[value]
        if re.search(pattern, value):
            return True
        alias = re.fullmatch(r'zz\d+', value)
        if not alias:
            return False
    return False


def expression(value, definitions):
    seen = set()
    while value in definitions and value not in seen:
        seen.add(value)
        value = definitions[value]
        if not re.fullmatch(r'zz\d+', value):
            break
    return value


def int_value(value, definitions):
    match = re.fullmatch(r'zz5i64zDzKz5i\((\d+)\)', expression(value, definitions))
    assert match, value
    return int(match.group(1))


def slice_of(value, converted, high, low, definitions):
    match = re.fullmatch(r'zsubrange_bits\((\w+), (\w+), (\w+)\)',
                         expression(value, definitions))
    return bool(match and expression(match.group(1), definitions) == expression(converted, definitions) and
                int_value(match.group(2), definitions) == high and
                int_value(match.group(3), definitions) == low)


def field_values(line):
    assert ' = struct ' in line or line.startswith('return = struct '), line
    values = re.findall(r'\w+ = ([^,}]+)', line.split('{', 1)[1])
    assert len(values) == 2, line
    return [value.strip() for value in values]


def operand_invalid_from_source(definitions, source='za'):
    calls = [(var, re.fullmatch(r'zieee_operand_invalid\((\w+), (\w+)\)', rhs))
             for var, rhs in definitions.items() if rhs.startswith('zieee_operand_invalid(')]
    assert len(calls) == 1 and calls[0][1], '源异常分类调用数量变化'
    var, call = calls[0]
    assert call.group(1) == 'false' and expression(call.group(2), definitions) == source, \
        '源异常分类不再使用quiet=false和原始源'
    return var


def check_tiny_inexact(underflow, inexact, definitions, name):
    terms = re.fullmatch(r'zstrict_and_bool\((\w+), (\w+)\)', definitions[underflow])
    assert terms and inexact in terms.groups(), f'{name}: UF未结合NX'
    tiny = terms.group(2) if terms.group(1) == inexact else terms.group(1)
    assert tiny != inexact and definitions.get(tiny, '').startswith('zstrict_or_bool('), \
        f'{name}: UF未结合独立tiny边界'


def check_narrow(name, lines, width, signed):
    d = defs(lines)
    converted = next(var for var, rhs in d.items()
                     if re.fullmatch(r'zz\d+\.ztuplez3z5bv5_z5bv321', rhs))
    overflows = [(var, rhs) for var, rhs in d.items() if rhs.startswith('znot_bool(')
                 and any('zeq_anything' in d.get(token, '')
                         for token in re.findall(r'\bzz\d+\b', rhs))]
    assert len(overflows) == 1, f'{name}: 无损窄化谓词不唯一'
    overflow, _ = overflows[0]
    eq = d[re.fullmatch(r'znot_bool\((\w+)\)', d[overflow]).group(1)]
    match = re.fullmatch(r'zeq_anythingzIB(32|16|24)zK\((\w+), (\w+)\)', eq)
    assert match, f'{name}: overflow比较类型变化'
    left, right = match.group(2), match.group(3)
    if signed:
        assert match.group(1) == '32', f'{name}: signed比较位宽错误'
        assert left == converted or right == converted, f'{name}: overflow未比较转换结果'
        extended = right if left == converted else left
        ext = re.fullmatch(r'zsign_extend\((\w+), (\w+)\)', expression(extended, d))
        assert ext and int_value(ext.group(1), d) == 32 and slice_of(
            ext.group(2), converted, width - 1, 0, d), f'{name}: 不是低位符号扩展回比较'
    else:
        assert int(match.group(1)) == 32 - width, f'{name}: unsigned比较位宽错误'
        upper = left if expression(left, d).startswith('zsubrange_bits(') else right
        zeros = right if upper == left else left
        assert slice_of(upper, converted, 31, width, d), f'{name}: unsigned比较的上位来源错误'
        zero = re.fullmatch(r'zzzeros\((\w+)\)', expression(zeros, d))
        assert zero and int_value(zero.group(1), d) == 32 - width, f'{name}: unsigned零扩展位宽错误'
    branches = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    legacy = name == 'zriscv_f16ToI16_pure'
    assert len(branches) == (1 if legacy else 0), f'{name}: 目标Jump数量变化'
    upstream = re.search(r'(zz\d+) = zz\d+\.ztuplez3z5bv5_z5bv32[0] ', '\n'.join(lines))
    assert upstream, f'{name}: 上游flags来源缺失'
    flags = upstream.group(1)
    nv = [var for var, rhs in d.items() if rhs == 'znvFlag(())']
    assert len(nv) == 1, f'{name}: NV来源数量变化'
    if signed:
        limits = [(var, re.fullmatch(rf'zitezIB{width}zK\((\w+), (0x[0-9A-F]+), (0x[0-9A-F]+)\)', rhs))
                  for var, rhs in d.items() if rhs.startswith(f'zitezIB{width}zK(')]
        limits = [(var, match) for var, match in limits if match and
                  (match.group(2), match.group(3)) ==
                  (f'0x{1 << (width - 1):0{width // 4}X}', f'0x{(1 << (width - 1)) - 1:0{width // 4}X}')]
        assert len(limits) == 1, f'{name}: signed端点选择变化'
        limit, select = limits[0]
        sign = re.fullmatch(r'zeq_anythingzIB1zK\((\w+), 0b1\)', d[select.group(1)])
        bit = re.fullmatch(r'zbitvector_access\((\w+), (\w+)\)',
                           expression(sign.group(1), d)) if sign else None
        assert bit and expression(bit.group(1), d) == expression(converted, d) and \
            int_value(bit.group(2), d) == 31, f'{name}: 端点未按转换结果符号位选择'
    else:
        limits = [(var, re.fullmatch(r'zones\((\w+)\)', rhs)) for var, rhs in d.items()
                  if rhs.startswith('zones(')]
        limits = [(var, match) for var, match in limits if match and
                  int_value(match.group(1), d) == width]
        assert len(limits) == 1, f'{name}: unsigned端点不是全1'
        limit = limits[0][0]
    result = next((re.match(r'return = (\w+)', line).group(1) for line in lines
                   if line.startswith('return = ')), None)
    assert result, f'{name}: 缺少返回值'
    constructors = [(i, field_values(line)) for i, line in enumerate(lines)
                    if line.startswith(result + ' = struct ')]
    if legacy:
        guard, normal, saturated = jump(lines, branches[0])
        assert guard == overflow and len(constructors) == 2, f'{name}: 旧饱和Jump/出口变化'
        normal_values = next((values for i, values in constructors if i in reachable(lines, normal)), None)
        saturated_values = next((values for i, values in constructors if i in reachable(lines, saturated)), None)
        assert normal_values and saturated_values and normal_values[0] == flags and \
            slice_of(normal_values[1], converted, width - 1, 0, d), f'{name}: 正常低位/flags错误'
        assert saturated_values == [nv[0], limit], f'{name}: 饱和NV/端点错误'
    else:
        assert len(constructors) == 1, f'{name}: 数据流结果出口数量变化'
        flag_choice, value_choice = constructors[0][1]
        flag_select = re.fullmatch(r'zitezIB5zK\((\w+), (\w+), (\w+)\)',
                                   expression(flag_choice, d))
        value_select = re.fullmatch(rf'zitezIB{width}zK\((\w+), (\w+), (\w+)\)',
                                    expression(value_choice, d))
        assert flag_select and flag_select.groups() == (overflow, nv[0], flags), \
            f'{name}: flags未按overflow选择NV或原值'
        assert value_select and value_select.group(1) == overflow and \
            expression(value_select.group(2), d) == expression(limit, d) and \
            slice_of(value_select.group(3), converted, width - 1, 0, d), \
            f'{name}: 数值未按overflow选择端点或原低位'
    return len(branches)


def check_flags(lines):
    d = defs(lines)
    old = next(var for var, rhs in d.items() if rhs.startswith('z_get_Fcsr_FFLAGS('))
    joined = next(var for var, rhs in d.items() if rhs.startswith('zor_vec('))
    operands = re.fullmatch(r'zor_vec\((\w+), (\w+)\)', d[joined])
    assert operands and {expression(x, d) for x in operands.groups()} == {
        expression(old, d), 'zflags'}, 'flags: old|new来源变化'
    eq = next((var for var, rhs in d.items() if
               (match := re.fullmatch(r'zeq_anythingzIB5zK\((\w+), (\w+)\)', rhs)) and
               {expression(x, d) for x in match.groups()} ==
               {expression(old, d), expression(joined, d)}), None)
    assert eq is not None, 'flags: changed未比较old与old|flags'
    changed = next(var for var, rhs in d.items() if rhs == f'znot_bool({eq})')
    branches = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    guard = next((pc for pc in branches if jump(lines, pc)[0] == changed), None)
    assert guard is not None, 'flags: changed没有目标Jump'
    _, unchanged, changed_arm = jump(lines, guard)
    writes = {i for i, line in enumerate(lines) if line.startswith('zmstatus.zbits = ')}
    assert len(writes) == 1, 'flags: mstatus写回数变化'
    assert not writes & reachable(lines, unchanged) and writes & reachable(lines, changed_arm), \
        'flags: changed未支配Dirty写回'
    fs = next(i for i, line in enumerate(lines) if '= z_update_Mstatus_FS(' in line)
    sd = next(i for i, line in enumerate(lines) if '= z_update_Mstatus_SD(' in line)
    assert fs < sd < next(iter(writes)) and all(i in reachable(lines, changed_arm)
                                              for i in (fs, sd)), 'flags: FS/SD更新链错误'
    fs_value = re.search(r'z_update_Mstatus_FS\((\w+), (\w+)\)', lines[fs])
    assert fs_value and resolves_to(fs_value.group(2), r'zextStatus_to_bits\(zDirty\)', d), \
        'flags: FS未置Dirty'
    sd_value = re.search(r'(\w+) = z_update_Mstatus_SD\((\w+), (\w+)\)', lines[sd])
    assert sd_value and sd_value.group(2) == re.match(r'(\w+) = ', lines[fs]).group(1) and \
        sd_value.group(3) == '0b1', 'flags: SD未在FS更新后置1'
    assert lines[next(iter(writes))].startswith('zmstatus.zbits = ' + sd_value.group(1) + '.zbits'), \
        'flags: 写回未采用FS/SD更新结果'
    ext_f = next((pc for pc in branches if pc != guard and
                  'zhartSupports(zExt_F)' in d.get(jump(lines, pc)[0], '')), None)
    assert ext_f is not None and ext_f in reachable(lines, changed_arm) and \
        next(iter(writes)) in reachable(lines, jump(lines, ext_f)[2]) and \
        next(iter(writes)) not in reachable(lines, jump(lines, ext_f)[1]), \
        'flags: Ext_F真臂没有支配状态写回'
    callbacks = [i for i, line in enumerate(lines) if 'zcsr_name_write_callback(' in line]
    assert len(callbacks) == 2 and all(i in reachable(lines, unchanged) and
                                      i in reachable(lines, changed_arm) for i in callbacks), \
        'flags: 两回调不在合流后'
    return len(branches)


def check_exception(name, lines, role_count, minimum):
    check_operand_order(name, lines, role_count)
    d = defs(lines)
    match = re.fullmatch(r'zieee_(add|sub|mul|div|sqrt|fma)(16|32|64)_exceptions', name)
    assert match, name
    op, source_width = match.group(1), int(match.group(2))
    assert len(EXCEPTION_CALLS[op]) == minimum, f'{name}: 原因清单数量变化'
    jumps = [i for i, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) == 1, f'{name}: 仅finite/valid gate应保留目标Jump'
    condition, skipped, active = jump(lines, jumps[0])
    returns = [(i, re.fullmatch(r'return = zieee_exception_facts\((.*)\) `.*', line))
               for i, line in enumerate(lines) if line.startswith('return = ')]
    assert len(returns) == 2 and all(item for _, item in returns), f'{name}: facts出口数量变化'
    nonfinite = next((arguments(item.group(1)) for i, item in returns
                      if i in reachable(lines, skipped)), None)
    finite = next((arguments(item.group(1)) for i, item in returns
                   if i in reachable(lines, active)), None)
    assert nonfinite and finite and len(nonfinite) == len(finite) == 5, \
        f'{name}: 两臂facts未受finite gate控制'
    assert nonfinite[2:] == ['false'] * 3, f'{name}: 非有限出口提前产生OF/UF/NX'
    assert nonfinite[:2] == finite[:2], f'{name}: NV/DZ在两臂不一致'
    if op != 'div':
        assert nonfinite[1] == 'false', f'{name}: 非除法异常产生DZ'
    else:
        assert finite[1] != 'false', f'{name}: 除零事实丢失'
    rounded = [(i, re.match(r'(\w+) = zieee_f(?:16|32|64)_rounded_exceptions\(', line))
               for i, line in enumerate(lines) if '_rounded_exceptions(' in line]
    assert len(rounded) == 1 and rounded[0][1], f'{name}: 定向舍入事实数变化'
    rounded_var = rounded[0][1].group(1)
    assert rounded[0][0] in reachable(lines, active) and rounded[0][0] not in reachable(lines, skipped), \
        f'{name}: 定向舍入未受finite gate控制'
    for field, helper in zip(finite[2:], ('overflow', 'underflow', 'inexact')):
        assert d.get(field) == f'zieee_has_{helper}({rounded_var})', \
            f'{name}: {helper}字段未采用同一定向舍入事实'
    limited = [i for i, line in enumerate(lines) if re.search(
        r'= zfp(?:16|32|64)_(?:from_ieee|to_fp|add|sub|mul|div|sqrt|fma)\(', line)]
    assert limited and all(i in reachable(lines, active) and i not in reachable(lines, skipped)
                           for i in limited), f'{name}: 有限计算未受gate支配'
    roles = ('za', 'zb', 'zc')[:role_count]
    for raw in product(representative_values(source_width), repeat=role_count):
        values = dict(zip(roles, raw))
        guards = expected_exception_guards(op, raw, source_width)
        expected_valid = bool(guards[-1])
        expected_invalid = any(classify(value, source_width)['snan'] for value in raw) or \
            any(guards[:2 if op in ('mul', 'div') else 3 if op == 'fma' else 1])
        expected_dz = bool(guards[2]) if op == 'div' else False
        actual = (bool(evaluate(condition, d, values, source_width)),
                  bool(evaluate(nonfinite[0], d, values, source_width)),
                  bool(evaluate(nonfinite[1], d, values, source_width)))
        expected = (expected_valid, expected_invalid, expected_dz)
        assert actual == expected, (f'{name}: finite/NV/DZ事实错误 '
                                    f'{tuple(hex(x) for x in raw)} {actual} != {expected}')
    return len(jumps)


def check_operand_order(name, lines, role_count):
    calls = [i for i, line in enumerate(lines) if '= zieee_operand_invalid(' in line]
    jumps = [i for i, line in enumerate(lines) if line.startswith('jump ')]
    assert len(calls) == role_count, f'{name}: 源角色调用数变化'
    assert all(i in reachable(lines, 0) for i in calls), f'{name}: 源分类调用不可达'
    if jumps:
        assert calls[-1] < jumps[0], f'{name}: 源角色在行为Jump之后才分类'
        assert all(pc not in reachable(lines, 0, i) for i in calls for pc in jumps), \
            f'{name}: 某个行为Jump绕过源分类'
    return len(calls)


def check_integer_wrapper(name, lines, source_width, target_width, unsigned):
    d = defs(lines)
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert not jumps, f'{name}: 纯整数结果出现目标Jump'
    conversion = 'unsigned' if unsigned else 'signed'
    exceptions = [(var, rhs) for var, rhs in d.items()
                  if rhs.startswith(f'zieee_fp{source_width}_to_int_exceptions(')]
    assert len(exceptions) == 1, f'{name}: 转换异常来源数量变化'
    exc, exception_call = exceptions[0]
    expected_args = ('za', None, 'true' if unsigned else 'false',
                     'true' if target_width == 64 else 'false')
    call_args = arguments(exception_call.removeprefix(f'zieee_fp{source_width}_to_int_exceptions(')[:-1])
    assert len(call_args) == 4 and all(value is None or call_args[i] == value
                                       for i, value in enumerate(expected_args)), \
        f'{name}: 转换异常源/符号/宽度变化'
    candidate = [(var, rhs) for var, rhs in d.items()
                 if rhs.startswith(f'zfp{source_width}_to_{conversion}{target_width}(')]
    assert len(candidate) == 1 and call_args[1] in candidate[0][1], \
        f'{name}: 候选整数结果来源变化'
    returns = [field_values(line) for line in lines if line.startswith('return = struct ')]
    assert len(returns) == 1, f'{name}: 整数结果出口变化'
    packed, result = returns[0]
    assert d.get(packed) == f'zriscv_pack_ieee_flags({exc})', f'{name}: flags未采用转换异常'
    final = re.fullmatch(rf'zitezIB{target_width}zK\((\w+), (\w+), (\w+)\)', d.get(result, ''))
    assert final and d.get(final.group(1)) == f'zieee_has_invalid({exc})' and \
        expression(final.group(3), d) == expression(candidate[0][0], d), \
        f'{name}: invalid未在最终结果选择端点/候选值'
    positive = (1 << target_width) - 1 if unsigned else (1 << (target_width - 1)) - 1
    negative = 0 if unsigned else 1 << (target_width - 1)
    fmt = f'0x{{:0{target_width // 4}X}}'
    if source_width == 64:
        endpoint = re.fullmatch(rf'zitezIB{target_width}zK\((\w+), (\w+), (\w+)\)',
                                d.get(final.group(2), ''))
        assert endpoint and endpoint.group(2) == fmt.format(positive) and \
            endpoint.group(3) == fmt.format(negative), f'{name}: f64正负端点变化'
        choice = re.fullmatch(r'zstrict_or_bool\((\w+), (\w+)\)', d.get(endpoint.group(1), ''))
        assert choice, f'{name}: f64 NaN/非负条件变化'
        nan_terms = [x for x in choice.groups() if d.get(x, '').startswith('zieee_is_nan(')]
        assert len(nan_terms) == 1 and expression(arguments(d[nan_terms[0]][len('zieee_is_nan('):-1])[0], d) == 'za', \
            f'{name}: f64 NaN未分类原始源'
        nonnegative = choice.group(2) if choice.group(1) == nan_terms[0] else choice.group(1)
        sign_test = re.fullmatch(r'zeq_anythingzIB1zK\((\w+), 0b0\)', d.get(nonnegative, ''))
    else:
        nan = re.fullmatch(rf'zitezIB{target_width}zK\((\w+), (\w+), (\w+)\)',
                           d.get(final.group(2), ''))
        assert nan and d.get(nan.group(1), '').startswith('zieee_is_nan(') and \
            expression(arguments(d[nan.group(1)][len('zieee_is_nan('):-1])[0], d) == 'za' and \
            nan.group(2) == fmt.format(positive), f'{name}: NaN端点/来源变化'
        sign = re.fullmatch(rf'zitezIB{target_width}zK\((\w+), (\w+), (\w+)\)',
                            d.get(nan.group(3), ''))
        assert sign and sign.group(2) == fmt.format(negative) and \
            sign.group(3) == fmt.format(positive), f'{name}: 正负端点变化'
        sign_test = re.fullmatch(r'zeq_anythingzIB1zK\((\w+), 0b1\)', d.get(sign.group(1), ''))
    bit = re.fullmatch(r'zbitvector_access\((\w+), (\w+)\)',
                       expression(sign_test.group(1), d)) if sign_test else None
    assert bit and expression(bit.group(1), d) == 'za' and \
        int_value(bit.group(2), d) == source_width - 1, f'{name}: 符号未取原始源最高位'
    return len(jumps)


def check_rod_wrapper(name, lines, source_width, target_width):
    d = defs(lines)
    rm = 'zrm_bits' if source_width == 32 else 'zrm'
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) >= 3, f'{name}: ROD/普通/NaN出口不全'
    mode, ordinary, rod = jump(lines, jumps[0])
    compare = re.fullmatch(r'zeq_bits\((\w+), (\w+)\)', d[mode])
    assert compare and {expression(x, d) for x in compare.groups()} == {rm, '0b110'}, \
        f'{name}: ROD模式不是rm_bits==6'
    ordinary_calls = [i for i, line in enumerate(lines)
                      if f'= zriscv_valid_rm_to_ieee({rm})' in line]
    rod_calls = [i for i, line in enumerate(lines)
                 if f'= zieee_rod{source_width}_to_{target_width}(' in line]
    assert len(ordinary_calls) == len(rod_calls) == 1
    assert ordinary_calls[0] in reachable(lines, ordinary) and \
        ordinary_calls[0] not in reachable(lines, rod), f'{name}: 普通RM仍在ROD臂运行'
    assert rod_calls[0] in reachable(lines, rod) and \
        rod_calls[0] not in reachable(lines, ordinary), f'{name}: ROD helper未受模式Jump控制'
    returns = [i for i, line in enumerate(lines) if line.startswith('return = ')]
    assert len(returns) == 2 and any(i in reachable(lines, ordinary) for i in returns) and \
        any(i in reachable(lines, rod) for i in returns), f'{name}: 模式两臂没有独立flags/result返回'
    return len(jumps)


def check_rod_helper(name, lines, source_width, target_width):
    d = defs(lines)
    invalid = operand_invalid_from_source(d)
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) == 1, f'{name}: finite目标Jump变化'
    finite_cond, nonfinite, finite = jump(lines, jumps[0])
    assert d[finite_cond].startswith('zieee_is_finite(') and \
        expression(re.fullmatch(r'zieee_is_finite\((\w+)\)', d[finite_cond]).group(1), d) == 'za', \
        f'{name}: 非有限源gate变化'
    exact = [i for i, line in enumerate(lines) if f'= zieee_exact{target_width}_exceptions(' in line]
    assert len(exact) == 1 and exact[0] in reachable(lines, finite) and \
        exact[0] not in reachable(lines, nonfinite), f'{name}: exact阈值计算不受finite gate支配'
    empty = [(i, re.match(r'(\w+) = zieee_empty_exceptions\((\w+)\)', line))
             for i, line in enumerate(lines) if '= zieee_empty_exceptions(' in line]
    assert len(empty) == 1 and empty[0][1] and empty[0][0] in reachable(lines, nonfinite), \
        f'{name}: 非有限flags来源变化'
    flags = empty[0][1].group(1)
    assert expression(empty[0][1].group(2), d) == expression(invalid, d), \
        f'{name}: 非有限NV未保留源分类'
    exact_flags = [(i, re.match(r'(\w+) = zieee_exact' + str(target_width) + r'_exceptions\(', line))
                   for i, line in enumerate(lines) if f'= zieee_exact{target_width}_exceptions(' in line]
    assert len(exact_flags) == 1 and exact_flags[0][1] and exact_flags[0][0] in reachable(lines, finite), \
        f'{name}: 有限flags来源变化'
    assert any(line.startswith(flags + ' = ' + exact_flags[0][1].group(1) + ' `') and
               i in reachable(lines, finite) for i, line in enumerate(lines)), \
        f'{name}: 有限flags未汇入返回变量'
    inexact = next((var for var, rhs in d.items() if rhs == f'zieee_has_inexact({flags})'), None)
    assert inexact, f'{name}: 奇数化未由合流flags的NX控制'
    base = next(var for var, rhs in d.items() if rhs.startswith(f'zfp{target_width}_to_ieee('))
    jam = [(i, re.fullmatch(r'(\w+) = zor_vec\((\w+), (\w+)\) `.*', line))
           for i, line in enumerate(lines) if '= zor_vec(' in line]
    assert len(jam) == 1 and jam[0][1], f'{name}: ROD奇数化OR结构变化'
    jam_pc, operation = jam[0]
    assert jam_pc in reachable(lines, 0), f'{name}: jam值不可达'
    assert {expression(value, d) for value in operation.groups()[1:]} == {
        expression(base, d), f'0x{1:0{target_width // 4}X}'}, \
        f'{name}: jam未采用base|1'
    selects = [(var, re.fullmatch(rf'zitezIB{target_width}zK\((\w+), (\w+), (\w+)\)', rhs))
               for var, rhs in d.items() if rhs.startswith(f'zitezIB{target_width}zK(')]
    assert len(selects) == 1 and selects[0][1], f'{name}: NX值选择数量变化'
    choice, select = selects[0]
    assert select.group(1) == inexact and expression(select.group(2), d) == expression(operation.group(1), d) and \
        expression(select.group(3), d) == expression(base, d), \
        f'{name}: NX条件或jam/base方向变化'
    returns = [field_values(line) for line in lines if line.startswith('return = struct ')]
    assert len(returns) == 1 and returns[0] == [flags, choice], \
        f'{name}: flags或jam选择结果未返回'
    return len(jumps)


def check_rounded(name, lines):
    d = defs(lines)
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert not jumps, f'{name}: 纯flags出口出现目标Jump'
    result = re.fullmatch(r'return = zieee_exception_facts\(false, false, (\w+), (\w+), (\w+)\) `.*',
                          lines[-2])
    assert result, f'{name}: OF/UF/NX返回字段变化'
    overflow, underflow, inexact = result.groups()
    assert d[overflow].startswith('zstrict_or_bool('), f'{name}: OF条件未来自边界析取'
    check_tiny_inexact(underflow, inexact, d, name)
    nx = re.fullmatch(r'znot_bool\((\w+)\)', d[inexact])
    both = re.fullmatch(r'zstrict_and_bool\((\w+), (\w+)\)', d[nx.group(1)]) if nx else None
    assert both, f'{name}: NX不是lo/hi双比较的否定'
    target_width = re.search(r'f(16|32|64)_rounded', name).group(1)
    widened = next((var for var, rhs in d.items()
                    if rhs.startswith(f'zfp{target_width}_to_fp')), None)
    assert widened, f'{name}: 目标结果未扩宽'
    expected = {frozenset(('zlo', expression(widened, d))),
                frozenset(('zhi', expression(widened, d)))}
    observed = set()
    for predicate in both.groups():
        eq = re.fullmatch(r'zfp\d+_eq\((\w+), (\w+)\)', d.get(predicate, ''))
        assert eq, f'{name}: NX比较不是FP相等'
        observed.add(frozenset(expression(x, d) for x in eq.groups()))
    assert observed == expected, f'{name}: NX未分别比较lo/hi与目标结果'
    return len(jumps)


def check_exact_threshold(lines):
    d = defs(lines)
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert not jumps, 'exact_threshold: 纯flags出口出现目标Jump'
    result = re.fullmatch(r'return = zieee_exception_facts\(false, false, (\w+), (\w+), (\w+)\) `.*',
                          lines[-2])
    assert result, 'exact_threshold: OF/UF/NX返回字段变化'
    overflow, underflow, inexact = result.groups()
    assert d[overflow].startswith('zstrict_or_bool('), 'exact_threshold: OF条件变化'
    check_tiny_inexact(underflow, inexact, d, 'exact_threshold')
    exact = re.fullmatch(r'znot_bool\((\w+)\)', d[inexact])
    assert exact and d[exact.group(1)] == 'zfp128_eq(zx, zresult)', \
        'exact_threshold: NX未比较精确值与结果'
    return len(jumps)


def check_fp_to_int_core(lines):
    assert lines[0].startswith('jump zfinite goto '), 'fp_to_int_core: finite入口变化'
    _, invalid, finite = jump(lines, 0)
    assert lines[invalid].startswith('return = zieee_empty_exceptions(true)'), \
        'fp_to_int_core: 非有限路径没有直接NV'
    calculations = [i for i, line in enumerate(lines) if '= zfp128_from_ieee(' in line]
    assert calculations and all(i in reachable(lines, finite) and
                                i not in reachable(lines, invalid) for i in calculations), \
        'fp_to_int_core: 整数上下界在非有限路径提前计算'
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) == 2
    invalid_cond, invalid_arm, valid_arm = jump(lines, jumps[1])
    assert defs(lines)[invalid_cond].startswith('zstrict_and_bool(') and \
        lines[invalid_arm].startswith('return = zieee_empty_exceptions(true)'), \
        'fp_to_int_core: 整数边界NV出口变化'
    valid_return = next((line for i, line in enumerate(lines) if i in reachable(lines, valid_arm)
                         and line.startswith('return = zieee_exception_facts(')), None)
    result = re.fullmatch(r'return = zieee_exception_facts\(false, false, false, false, (\w+)\) `.*',
                          valid_return or '')
    d = defs(lines)
    assert result and re.fullmatch(r'znot_bool\((\w+)\)', d[result.group(1)]) and \
        d[re.fullmatch(r'znot_bool\((\w+)\)', d[result.group(1)]).group(1)] == \
        'zfp128_eq(zx, zrounded)', 'fp_to_int_core: 合法舍入NX来源或返回字段变化'
    return len(jumps)


def check_round(name, lines, width):
    d = defs(lines)
    calls = [i for i, line in enumerate(lines) if '= zieee_operand_invalid(' in line]
    assert len(calls) == 1 and calls[0] < 8, f'{name}: 源NaN分类变化'
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) == 1, f'{name}: finite分界变化'
    finite_cond, nonfinite, finite = jump(lines, jumps[0])
    assert re.fullmatch(r'zieee_is_finite\((\w+)\)', d[finite_cond]) and \
        expression(re.fullmatch(r'zieee_is_finite\((\w+)\)', d[finite_cond]).group(1), d) == 'za', \
        f'{name}: finite源变化'
    assert lines[nonfinite].startswith('return = zieee_empty_exceptions('), \
        f'{name}: 非有限出口变化'
    value = [i for i, line in enumerate(lines) if f'= zfp{width}_from_ieee(za)' in line]
    assert len(value) == 1 and value[0] in reachable(lines, finite) and \
        value[0] not in reachable(lines, nonfinite), f'{name}: 特殊源提前运行数值比较'
    invalid = operand_invalid_from_source(d)
    assert lines[nonfinite].startswith(f'return = zieee_empty_exceptions({invalid})'), \
        f'{name}: 非有限NV出口变化'
    finite_return = next((line for i, line in enumerate(lines) if i in reachable(lines, finite)
                          and line.startswith('return = zieee_exception_facts(')), None)
    result = re.fullmatch(r'return = zieee_exception_facts\((\w+), false, false, false, (\w+)\) `.*',
                          finite_return or '')
    assert result and result.group(1) == invalid, f'{name}: 有限NV返回字段变化'
    nx = re.fullmatch(r'zstrict_and_bool\(zraise_inexact, (\w+)\)', d[result.group(2)])
    not_equal = re.fullmatch(r'znot_bool\((\w+)\)', d[nx.group(1)]) if nx else None
    rounded_source = re.match(r'(\w+) = ', lines[value[0]]).group(1)
    assert not_equal and d[not_equal.group(1)] == f'zfp{width}_eq({rounded_source}, zresult)', \
        f'{name}: NX条件或出口变化'
    return len(jumps)


def check_conversion_gate(name, lines, source_width, exact_name):
    d = defs(lines)
    calls = [i for i, line in enumerate(lines) if '= zieee_operand_invalid(' in line]
    assert len(calls) == 1, f'{name}: NaN源分类变化'
    jumps = [pc for pc, line in enumerate(lines) if line.startswith('jump ')]
    assert len(jumps) == 1 and calls[0] < jumps[0], f'{name}: finite gate/源分类变化'
    condition, nonfinite, finite = jump(lines, jumps[0])
    assert re.fullmatch(r'zieee_is_finite\((\w+)\)', d[condition]) and \
        expression(re.fullmatch(r'zieee_is_finite\((\w+)\)', d[condition]).group(1), d) == 'za'
    invalid = operand_invalid_from_source(d)
    assert lines[nonfinite].startswith(f'return = zieee_empty_exceptions({invalid})'), \
        f'{name}: 非有限出口变化'
    exact = [i for i, line in enumerate(lines) if f'= {exact_name}(' in line]
    direct = [i for i, line in enumerate(lines) if line.startswith('return = ')
              and i in reachable(lines, finite)]
    assert len(exact) == len(direct) == 1 and all(
        i in reachable(lines, finite) and i not in reachable(lines, nonfinite)
        for i in (exact[0], direct[0])), f'{name}: exact/flags计算不受finite gate支配'
    exact_var = re.match(r'(\w+) = ', lines[exact[0]]).group(1)
    assert lines[direct[0]].startswith('return = ' + exact_var + ' `'), \
        f'{name}: 有限真臂未直接返回exact facts'
    if source_width in (32, 64):
        widened = [i for i, line in enumerate(lines) if f'= zfp{source_width}_from_ieee(za)' in line]
        if widened:
            assert all(i in reachable(lines, finite) and i not in reachable(lines, nonfinite)
                       for i in widened), f'{name}: 源扩宽提前运行'
    return len(jumps)


def check(text, path):
    f = functions(text)
    results = {}
    xlen = re.search(r'(?m)^val zrX : \(%i64\) ->  %bv(32|64)$', text)
    assert xlen, f'{path}: 无法核实XLEN'
    results['accrue_fflags'] = check_flags(f['zaccrue_fflags'])
    for name, (width, signed) in NARROW.items():
        results[name] = check_narrow(name, f[name], width, signed)
    for width in (16, 32, 64):
        for op, roles, jumps in (('add', 2, 2), ('sub', 2, 2), ('mul', 2, 3),
                                 ('div', 2, 4), ('sqrt', 1, 2), ('fma', 3, 4)):
            name = f'zieee_{op}{width}_exceptions'
            results[name] = check_exception(name, f[name], roles, jumps)
        for target in (32, 64):
            for unsigned in (False, True):
                name = f'zriscv_f{width}To{"Ui" if unsigned else "I"}{target}'
                if name not in f:
                    assert xlen.group(1) == '32' and width == 16 and target == 64, \
                        f'{path}: 非RV32例外包装函数缺失 {name}'
                    continue
                results[name] = check_integer_wrapper(name, f[name], width, target, unsigned)
    for source, target in ((32, 16), (64, 32)):
        wrapper = f'zriscv_f{source}ToF{target}'
        helper = f'zieee_rod{source}_to_{target}'
        results[wrapper] = check_rod_wrapper(wrapper, f[wrapper], source, target)
        results[helper] = check_rod_helper(helper, f[helper], source, target)
    for width in (16, 32, 64):
        name = f'zieee_f{width}_rounded_exceptions'
        results[name] = check_rounded(name, f[name])
    assert 'zieee_mask_exact_exceptions' not in f, f'{path}: 冗余mask helper仍存在'
    results['zieee_exact_threshold_exceptions'] = check_exact_threshold(
        f['zieee_exact_threshold_exceptions'])
    results['zieee_fp_to_int_core'] = check_fp_to_int_core(f['zieee_fp_to_int_core'])
    for width in (16, 32, 64):
        name = f'zieee_round{width}_exceptions'
        results[name] = check_round(name, f[name], width)
    for name, source, exact in (
            ('zieee_bf16_from_f32_exceptions', 32, 'zieee_exact_bf16_exceptions'),
            ('zieee_convert32_to_16_exceptions', 32, 'zieee_exact16_exceptions'),
            ('zieee_convert64_to_16_exceptions', 64, 'zieee_exact16_exceptions'),
            ('zieee_convert64_to_32_exceptions', 64, 'zieee_exact32_exceptions')):
        results[name] = check_conversion_gate(name, f[name], source, exact)
    print(f'PASS {path}: {len(results)}个目标函数的实际条件、出口与支配关系')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ir', type=Path, action='append')
    args = parser.parse_args()
    for path in args.ir or [ROOT / name for name in IRS]:
        check(path.read_text(), path)


if __name__ == '__main__':
    main()
