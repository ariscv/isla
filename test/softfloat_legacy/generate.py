"""把退役的 20 项旧专用分发断言转成独立 SoftFloat 参考向量。"""
import argparse
import json
import struct
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--oracle', type=Path, required=True, help='已构建的 SoftFloat oracle 可执行文件')
args = parser.parse_args()
ORACLE = args.oracle
OUT = ROOT / 'cases.tsv'
MAP = ROOT / 'mapping.tsv'


def f32(value):
    return int.from_bytes(struct.pack('>f', value), 'big')


def f64(value):
    return int.from_bytes(struct.pack('>d', value), 'big')


# (旧测试名, helper, oracle op, fmt, dst, rm, exact, 参数位串)
cases = [
    ('f32_add_basic', 'riscv_f32Add', 'add', 'f32', None, 0, None, [f32(1), f32(2)]),
    ('f32_add_inexact_nx', 'riscv_f32Mul', 'mul', 'f32', None, 0, None, [f32(1.0000001), f32(1.0000002)]),
    ('f32_add_inexact_nx', 'riscv_f32Mul', 'mul', 'f32', None, 0, None, [f32(2), f32(4)]),
    ('f32_add_overflow_of_nx', 'riscv_f32Add', 'add', 'f32', None, 0, None, [f32(3.4028234663852886e38)] * 2),
    ('f32_add_inf_inf_invalid', 'riscv_f32Add', 'add', 'f32', None, 0, None, [f32(float('inf')), f32(float('-inf'))]),
    ('f32_div_by_zero', 'riscv_f32Div', 'div', 'f32', None, 0, None, [f32(1), f32(0)]),
    ('f32_div_zero_zero_invalid', 'riscv_f32Div', 'div', 'f32', None, 0, None, [f32(0), f32(0)]),
    ('f32_mul_underflow_uf', 'riscv_f32Mul', 'mul', 'f32', None, 0, None, [1, f32(.75)]),
    ('f32_snan_quiet_nan_flags', 'riscv_f32Add', 'add', 'f32', None, 0, None, [0x7f800001, f32(1)]),
    ('f32_snan_quiet_nan_flags', 'riscv_f32Add', 'add', 'f32', None, 0, None, [0x7fc00001, f32(1)]),
    ('f32_sqrt_exact_and_inexact', 'riscv_f32Sqrt', 'sqrt', 'f32', None, 0, None, [f32(4)]),
    ('f32_sqrt_exact_and_inexact', 'riscv_f32Sqrt', 'sqrt', 'f32', None, 0, None, [f32(2)]),
    ('f32_sqrt_negative_invalid', 'riscv_f32Sqrt', 'sqrt', 'f32', None, 0, None, [f32(-4)]),
    ('f32_cmp_nan_semantics', 'riscv_f32Lt', 'lt', 'f32', None, None, None, [0x7fc00001, f32(1)]),
    ('f32_cmp_nan_semantics', 'riscv_f32Lt_quiet', 'lt_quiet', 'f32', None, None, None, [0x7fc00001, f32(1)]),
    ('f32_cmp_nan_semantics', 'riscv_f32Le', 'le', 'f32', None, None, None, [f32(1), f32(2)]),
    ('fma_basic', 'riscv_f32MulAdd', 'fma', 'f32', None, 0, None, [f32(2), f32(3), f32(1)]),
    ('f32_to_i32_overflow_and_boundary', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [f32(2147483648)]),
    ('f32_to_i32_overflow_and_boundary', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [f32(2147483520)]),
    ('f32_to_i32_overflow_and_boundary', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [f32(-2147483904)]),
    ('f32_to_i32_overflow_and_boundary', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [f32(-2147483648)]),
    ('f32_to_i32_inexact_nx', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [f32(-1.5)]),
    ('f32_to_i32_inexact_nx', 'riscv_f32ToI32', 'fp_to_int', 'f32', 'i32', 0, None, [0x7fc00000]),
    ('i32_to_f32_inexact_nx', 'riscv_i32ToF32', 'int_to_fp', 'i32', 'f32', 0, None, [0x7fffffff]),
    ('i32_to_f32_inexact_nx', 'riscv_i32ToF32', 'int_to_fp', 'i32', 'f32', 0, None, [1 << 23]),
    ('i64_to_f16_overflow_of', 'riscv_i64ToF16', 'int_to_fp', 'i64', 'f16', 0, None, [65520]),
    ('i64_to_f16_overflow_of', 'riscv_i64ToF16', 'int_to_fp', 'i64', 'f16', 1, None, [65520]),
    ('i64_to_f16_overflow_of', 'riscv_i64ToF16', 'int_to_fp', 'i64', 'f16', 1, None, [65536]),
    ('f64_to_f32_narrowing_nx', 'riscv_f64ToF32', 'fp_to_fp', 'f64', 'f32', 0, None, [f64(1.5)]),
    ('f64_to_f32_narrowing_nx', 'riscv_f64ToF32', 'fp_to_fp', 'f64', 'f32', 0, None, [f64(1/3)]),
    ('f32_round_to_int', 'riscv_f32roundToInt', 'round', 'f32', None, 0, 1, [f32(2.5)]),
    ('f32_round_to_int', 'riscv_f32roundToInt', 'round', 'f32', None, 0, 1, [f32(2)]),
    ('f32_round_to_int', 'riscv_f32roundToInt', 'round', 'f32', None, 0, 0, [f32(2.5)]),
    ('f32_to_bf16', 'riscv_f32ToBF16', 'fp_to_fp', 'f32', 'bf16', 0, None, [f32(1)]),
    ('f16_add_basic', 'riscv_f16Add', 'add', 'f16', None, 0, None, [0x3c00, 0x3c00]),
]

lines = []
mapping = ['old_test\tnew_helper\toriginal_bits\toracle_result\toracle_flags']
for test, helper, op, fmt, dst, rm, exact, values in cases:
    command = [str(ORACLE), '--op', op, '--fmt', fmt]
    if dst is not None:
        command += ['--dst', dst]
    if rm is not None:
        command += ['--rm', str(rm)]
    if exact is not None:
        command += ['--exact', str(exact)]
    for key, value in zip('abc', values):
        command += ['--' + key, hex(value)]
    expected = json.loads(subprocess.check_output(command, text=True))
    width = 32 if fmt in ('f32', 'i32') else 64 if fmt in ('f64', 'i64') else 16
    args = ([] if rm is None else [f'3:{rm:x}']) + [f'{width}:{value:x}' for value in values]
    if exact is not None:
        args += [f'1:{exact:x}']
    result_width = 1 if expected['dst'] == 'bool' else {'f16': 16, 'bf16': 16, 'f32': 32, 'f64': 64, 'i32': 32, 'u32': 32, 'i64': 64, 'u64': 64}[expected['dst']]
    lines.append('\t'.join([helper, ','.join(args), expected['flags'], expected['result_bits'], str(result_width)]))
    mapping.append('\t'.join([test, helper, ','.join(args), expected['result_bits'], expected['flags']]))

assert len({case[0] for case in cases}) == 20
OUT.write_text('\n'.join(lines) + '\n')
MAP.write_text('\n'.join(mapping) + '\n')
print(f'generated {len(cases)} cases covering {len({case[0] for case in cases})} retired tests')
