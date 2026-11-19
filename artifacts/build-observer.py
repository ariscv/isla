#!/usr/bin/env python3
"""用冻结 isarch 的 ELF 符号范围编译外部 Z3 指标采集器。"""
from pathlib import Path
import subprocess
import sys

directory = Path(__file__).resolve().parent
binary = Path(sys.argv[1]).resolve()
z3 = Path(sys.argv[2]).resolve()
symbols = {
    "symbolic_length::fork_symbolic_value::": 1,
    "symbolic_length::retry_partition::": 2,
    "region_merge::concrete_consumer::": 2,
}
symbol_table = subprocess.check_output(["nm", "-n", "-S", binary], text=True)
table = subprocess.check_output(["c++filt"], input=symbol_table, text=True)
rows = {}
for line in table.splitlines():
    for prefix, kind in symbols.items():
        if prefix in line:
            start, size, _, name = line.split(maxsplit=3)
            value, length = int(start, 16), int(size, 16)
            assert prefix not in rows and length > 0, name
            rows[prefix] = f"{{0x{value:x}, 0x{value+length:x}, {kind}}}, /* {name} */"
assert set(rows) == set(symbols), rows
(directory / "scope-ranges.h").write_text("\n".join(rows.values()) + "\n")
subprocess.run(["cc", "-std=gnu11", "-Wall", "-Wextra", "-Werror", "-O2", "-shared", "-fPIC", "-pthread",
                "-I", z3 / "include", "-o", directory / "observe-z3.so", directory / "observe-z3.c", "-ldl"], check=True)
