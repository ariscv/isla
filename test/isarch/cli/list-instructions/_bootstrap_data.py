#!/usr/bin/env python3
"""
一次性引导工具：从 sail-riscv 源码 + 当前 assembly_names.txt 生成 expected_data/ 下的 Python 模块。
每个模块对应 sail-riscv/model 下的一个扩展目录，包含 INSTRUCTIONS 字典。

用法: python3 _bootstrap_data.py <sail_riscv_dir> <assembly_names_txt> <output_dir>
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path


def find_clause_to_dir(sail_model_dir: Path) -> dict:
    """扫描 sail 文件，返回 {clause_name: extension_dir_name}"""
    mapping = {}
    for f in sorted(sail_model_dir.rglob("*.sail")):
        for m in re.finditer(r"union\s+clause\s+instruction\s*=\s*(\w+)\s*:", f.read_text(errors="replace")):
            clause = m.group(1)
            # 相对路径: extensions/I/base_insts.sail → I
            rel = f.relative_to(sail_model_dir)
            parts = rel.parts
            # extensions/I/base_insts.sail → I; mops/Zcmop/... → Zcmop; sys/... → sys
            if len(parts) >= 2 and parts[0] in ("extensions", "mops"):
                ext_dir = parts[1]
            elif len(parts) >= 1:
                ext_dir = parts[0]
            else:
                ext_dir = "misc"
            mapping[clause] = ext_dir
    return mapping


def parse_assembly_names(txt_path: str) -> dict:
    """解析 assembly_names.txt → {clause: [asm_names]}"""
    result = {}
    with open(txt_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(None, 2)
            clause = parts[0]
            if len(parts) >= 3 and parts[1] == "ok":
                result[clause] = parts[2].split(",")
            else:
                result[clause] = []
    return result


def dir_to_module_name(dir_name: str) -> str:
    """扩展目录名 → Python 模块名 (小写，冲突加后缀)"""
    name = dir_name.lower().replace("-", "_")
    # 避免与 Python 关键字冲突
    if name in ("if", "is", "in", "as", "or", "and", "not"):
        name += "_ext"
    return name


def generate_modules(clause_to_dir: dict, asm_data: dict, output_dir: Path):
    """按扩展目录分组生成 Python 模块文件"""
    by_dir: dict = defaultdict(dict)
    for clause, ext_dir in sorted(clause_to_dir.items()):
        asms = asm_data.get(clause, [])
        by_dir[ext_dir][clause] = asms

    # 生成各模块
    module_names = []
    for ext_dir in sorted(by_dir.keys()):
        clauses = by_dir[ext_dir]
        mod_name = dir_to_module_name(ext_dir)
        module_names.append(mod_name)

        filepath = output_dir / f"{mod_name}.py"
        with open(filepath, "w") as f:
            f.write(f'# sail-riscv extension: {ext_dir}\n')
            f.write(f'# {len(clauses)} instruction clauses\n\n')
            f.write("INSTRUCTIONS = {\n")
            for clause, asms in sorted(clauses.items()):
                if asms:
                    f.write(f'    "{clause}": [\n')
                    for a in asms:
                        f.write(f'        "{a}",\n')
                    f.write(f'    ],\n')
                else:
                    f.write(f'    "{clause}": [],\n')
            f.write("}\n")
        print(f"  {mod_name}.py: {len(clauses)} clauses ({ext_dir})")

    # 生成 __init__.py
    init_path = output_dir / "__init__.py"
    with open(init_path, "w") as f:
        f.write("# 自动生成的指令预期数据注册表\n")
        f.write("# 各模块按 sail-riscv 扩展目录组织\n\n")
        for mod in module_names:
            f.write(f"from .{mod} import INSTRUCTIONS as {mod}\n")
        f.write("\n\n")
        f.write("_ALL_MODULES = [\n")
        for mod in module_names:
            f.write(f"    {mod},\n")
        f.write("]\n\n\n")
        f.write("def get_all_instructions():\n")
        f.write('    """返回 {clause_name: [asm_names]} 的合并字典"""\n')
        f.write("    result = {}\n")
        f.write("    for mod in _ALL_MODULES:\n")
        f.write("        result.update(mod)\n")
        f.write("    return result\n")

    print(f"\n  __init__.py: 聚合 {len(module_names)} 个模块")
    return module_names


if __name__ == "__main__":
    if len(sys.argv) != 4:
        print(f"用法: {sys.argv[0]} <sail_riscv_dir> <assembly_names.txt> <output_dir>", file=sys.stderr)
        sys.exit(1)

    sail_dir = Path(sys.argv[1])
    asm_file = sys.argv[2]
    output_dir = Path(sys.argv[3])

    model_dir = sail_dir / "model"
    if not model_dir.is_dir():
        print(f"错误: {model_dir} 不存在", file=sys.stderr)
        sys.exit(1)

    clause_to_dir = find_clause_to_dir(model_dir)
    asm_data = parse_assembly_names(asm_file)
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"从 {model_dir} 和 {asm_file} 生成 expected_data 模块...")
    generate_modules(clause_to_dir, asm_data, output_dir)
    print("完成。")
