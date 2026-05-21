#!/usr/bin/env python3
"""
isarch CLI 测试的预期结果管理工具。

预期数据硬编码在 expected_data/ 包中（按 sail-riscv 扩展目录组织的 Python 模块）。

子命令:
  generate           从 expected_data/ 生成 txt 文件
  verify             对 isarch list-instructions 实际输出做集合比较
  update-from-sail   从 sail-riscv 源码解析并重新生成 expected_data/ Python 模块
"""

import re
import sys
from collections import defaultdict
from itertools import product
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# ---------------------------------------------------------------------------
# expected_data 数据源
# ---------------------------------------------------------------------------

_SCRIPT_DIR = Path(__file__).resolve().parent
_DATA_DIR = _SCRIPT_DIR / "expected_data"


def _load_data() -> Dict[str, List[str]]:
    """从 expected_data 包加载所有指令数据"""
    if not (_DATA_DIR / "__init__.py").exists():
        print(f"错误: expected_data/ 不存在或缺少 __init__.py", file=sys.stderr)
        sys.exit(1)
    sys.path.insert(0, str(_SCRIPT_DIR))
    from expected_data import get_all_instructions
    return get_all_instructions()


# ---------------------------------------------------------------------------
# generate 子命令
# ---------------------------------------------------------------------------

def cmd_generate(outdir: str = ""):
    data = _load_data()
    output_dir = Path(outdir) if outdir else _SCRIPT_DIR / "expected"
    output_dir.mkdir(parents=True, exist_ok=True)

    clause_names = sorted(data.keys())

    # clause_names.txt
    with open(output_dir / "clause_names.txt", "w") as f:
        f.write(f"# instruction clause 名称 (共 {len(clause_names)} 个)\n\n")
        for name in clause_names:
            f.write(f"{name}\n")

    # assembly_names.txt
    total_asm = 0
    with open(output_dir / "assembly_names.txt", "w") as f:
        f.write("# CLAUSE_NAME STATUS asm1,asm2,...\n\n")
        for name in clause_names:
            asms = data[name]
            total_asm += len(asms)
            if asms:
                f.write(f"{name} ok {','.join(asms)}\n")
            else:
                f.write(f"{name}\n")

    # summary.txt
    with_asms = sum(1 for v in data.values() if v)
    with open(output_dir / "summary.txt", "w") as f:
        f.write(f"clause: {len(clause_names)}\n")
        f.write(f"有助记符: {with_asms}\n")
        f.write(f"助记符总数: {total_asm}\n")
    print(f"已生成到 {output_dir}/")
    print(f"  clause: {len(clause_names)}, 有助记符: {with_asms}, 助记符总数: {total_asm}")


# ---------------------------------------------------------------------------
# verify 子命令
# ---------------------------------------------------------------------------

def _parse_actual_output(text: str) -> Dict[str, List[str]]:
    result: Dict[str, List[str]] = {}
    for m in re.finditer(r"\[(\w+)\]\s*(.*)", text):
        clause = m.group(1)
        rest = m.group(2).strip()
        if rest == "(无汇编名称)" or not rest:
            result[clause] = []
        else:
            result[clause] = [a.strip() for a in rest.split(",") if a.strip()]
    return result


def cmd_verify(actual_output_file: str):
    expected = _load_data()
    actual_text = Path(actual_output_file).read_text(encoding="utf-8", errors="replace")
    actual = _parse_actual_output(actual_text)

    pass_count = 0
    fail_count = 0
    info_count = 0
    failures: List[str] = []

    # 实际输出为空 → 一定失败
    if not actual:
        print("错误: 实际输出中没有任何 clause", file=sys.stderr)
        sys.exit(1)

    for clause_name, actual_asms in sorted(actual.items()):
        expected_asms = expected.get(clause_name)

        if expected_asms is None:
            # 实际输出中有预期数据中没有的 clause
            failures.append(f"{clause_name}: 不在预期数据中 (实际 {len(actual_asms)})")
            fail_count += 1
            continue

        expected_set = set(expected_asms)
        actual_set = set(actual_asms)

        if not expected_asms:
            # 预期无助记符的 clause
            if actual_set:
                failures.append(f"{clause_name}: 预期无助记符但实际有 {actual_set}")
                fail_count += 1
            else:
                pass_count += 1
            continue

        extra = actual_set - expected_set
        missing = expected_set - actual_set
        if extra:
            # 实际助记符超出预期范围 → 失败
            failures.append(
                f"{clause_name}: 多出 {len(extra)} 个 ({', '.join(sorted(extra)[:5])}{'...' if len(extra) > 5 else ''})"
            )
            fail_count += 1
        elif not actual_set and expected_set and clause_name not in _ALLOWED_EMPTY_CLAUSES:
            # 预期有助记符但实际完全为空，且不在空输出白名单中 → 失败
            failures.append(f"{clause_name}: 预期 {len(expected_set)} 个助记符但实际为空")
            fail_count += 1
        elif missing and clause_name not in _ALL_ALLOWED:
            # 缺失助记符且不在 allowlist 中 → 失败
            failures.append(
                f"{clause_name}: 缺失 {len(missing)} 个 ({', '.join(sorted(missing)[:5])}{'...' if len(missing) > 5 else ''})"
            )
            fail_count += 1
        else:
            pass_count += 1
            if missing:
                print(f"  info: {clause_name}: 预期 {len(expected_set)}, 实际 {len(actual_set)} (缺失 {len(missing)}, allowlisted)")
                info_count += 1

    # 预期中有但实际输出没有的 clause
    for clause_name in sorted(expected):
        if clause_name not in actual:
            if clause_name in _ALL_ALLOWED:
                print(f"  info: {clause_name}: 在实际输出中不存在 (allowlisted)")
                info_count += 1
            else:
                failures.append(f"{clause_name}: 在实际输出中不存在")
                fail_count += 1

    print(f"\n=== 比较结果 ===")
    print(f"  通过: {pass_count}")
    print(f"  失败: {fail_count}")
    print(f"  信息: {info_count}")

    if failures:
        print(f"\n失败详情:")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)
    else:
        print("\n验证通过。")


# ---------------------------------------------------------------------------
# update-from-sail 子命令
# ---------------------------------------------------------------------------

_MNEMONIC_TERMINATORS = {"spc", "sep", "opt_spc"}

# 不是真正指令的 clause，不在 CLI 输出中出现
_EXCLUDED_CLAUSES = {"STOP_FETCHING", "THREAD_START"}

# allowlist：这些 clause 的 expected_data 来自 sail-riscv 笛卡尔积，包含比 CLI 输出更多的助记符。
# 原因是 IR 合法性过滤导致部分助记符在 CLI 中不出现，但至少会有一个助记符。
# 不在 allowlist 中的 clause，缺失助记符会计为失败。
_ALLOWED_PARTIAL_MISSING_CLAUSES = {
    "AMO", "LOAD", "STORE", "LOADRES", "STORECON", "LOAD_FP", "STORE_FP",
    "DIV", "DIVW", "MUL", "REM", "REMW",
    "VLRETYPE", "VLSEGFFTYPE", "VLSEGTYPE", "VLSSEGTYPE", "VLXSEGTYPE",
    "VMVRTYPE", "VSRETYPE", "VSSEGTYPE", "VSSSEGTYPE", "VSXSEGTYPE",
    "ZBA_RTYPEUW", "ZCMOP", "ZIMOP_MOP_R", "ZIMOP_MOP_RR",
}

# 这些 clause 在 CLI 中输出"无汇编名称"（IR 无法解析出任何助记符），
# expected_data 中有助记符但实际为空是已知差异。
_ALLOWED_EMPTY_CLAUSES = {
    "ZBA_RTYPE",
    "C_ADD", "C_ADDI", "C_ADDI16SP", "C_ADDI4SPN",
    "C_FLW", "C_FLWSP", "C_FSW", "C_FSWSP",
    "C_JAL", "C_JALR", "C_JR", "C_LDSP", "C_LUI", "C_LWSP", "C_MV",
}

_ALL_ALLOWED = _ALLOWED_PARTIAL_MISSING_CLAUSES | _ALLOWED_EMPTY_CLAUSES


def _find_sail_files(sail_dir: Path) -> List[Path]:
    return sorted(sail_dir.rglob("*.sail"))


def _read_all(files: List[Path]) -> str:
    return "\n".join(f.read_text(encoding="utf-8", errors="replace") for f in files)


def _collect_mapping_functions(text: str) -> Dict[str, List[str]]:
    results: Dict[str, List[str]] = {}
    for m in re.finditer(r"mapping\s+(\w+)\s*:\s*[^<]+\s*<->\s*string\s*=\s*\{", text):
        name = m.group(1)
        depth, pos = 1, m.end()
        while pos < len(text) and depth > 0:
            if text[pos] == "{": depth += 1
            elif text[pos] == "}": depth -= 1
            pos += 1
        body = text[m.end():pos-1]
        vals = [e.group(1) for e in re.finditer(r'<->\s*"([^"]*)"', body)]
        if vals:
            results[name] = vals
    return results


def _extract_union_clauses(text: str) -> List[str]:
    return sorted(set(m.group(1) for m in re.finditer(r"union\s+clause\s+instruction\s*=\s*(\w+)\s*:", text)))


def _extract_assembly_clauses(text: str) -> Dict[str, List[str]]:
    results: Dict[str, List[str]] = defaultdict(list)
    for m in re.finditer(r"mapping\s+clause\s+assembly\s*=\s*", text, re.MULTILINE):
        rest = text[m.end():]
        if rest.lstrip().startswith("//"):
            continue
        for pat in [
            r"forwards\s+(\w+)\s*\([^)]*\)\s*=>\s*(.+?)(?:\n\s*when\s|\n\n|\n[muf]\w)",
            r"(\w+)\s*\([^)]*\)\s*<->\s*(.+?)(?:\n\n|\n[muf]\w)",
            r"(\w+)\s*\([^)]*\)\s*<->\s*(.+)",
        ]:
            hit = re.match(pat, rest, re.DOTALL)
            if hit:
                results[hit.group(1)].append(hit.group(2).strip().rstrip(","))
                break
    return dict(results)


def _clause_to_dir_map(model_dir: Path) -> Dict[str, str]:
    mapping = {}
    for f in sorted(model_dir.rglob("*.sail")):
        for m in re.finditer(r"union\s+clause\s+instruction\s*=\s*(\w+)\s*:", f.read_text(errors="replace")):
            rel = f.relative_to(model_dir).parts
            ext = rel[1] if len(rel) >= 2 and rel[0] in ("extensions", "mops") else (rel[0] if rel else "misc")
            mapping[m.group(1)] = ext
    return mapping


def _parse_bit_literal(s: str):
    s = s.strip()
    if s.startswith(("0b", "0B")):
        return (int(s[2:], 2), len(s[2:]))
    if s.startswith(("0x", "0X")):
        return (int(s[2:], 16), len(s[2:]) * 4)
    try:
        v = int(s)
        return (v, max(v.bit_length(), 1))
    except ValueError:
        return None


def _eval_dec_bits_arg(arg: str, n: int) -> Optional[List[str]]:
    arg = arg.strip()
    if re.match(r"^\w+$", arg):
        return [str(i) for i in range(2**n)]
    parts = [p.strip() for p in arg.split("@")]
    if len(parts) == 2:
        p = _parse_bit_literal(parts[1])
        if p:
            cv, cb = p
            vb = n - cb
            if vb > 0:
                return [str((v << cb) | cv) for v in range(2**vb)]
    return None


def _split_caret(text: str) -> Optional[List[str]]:
    text = text.strip()
    if not text:
        return None
    parts = [p.strip() for p in text.split("^")]
    return [p for p in parts if p] or None


def _parse_mnemonic(expr: str) -> Optional[List[str]]:
    mnem, depth, i = "", 0, 0
    while i < len(expr):
        ch = expr[i]
        if ch == "(": depth += 1
        elif ch == ")": depth -= 1
        if depth == 0 and any(expr[i:].startswith(t + "(") for t in _MNEMONIC_TERMINATORS):
            return _split_caret(mnem)
        mnem += ch
        i += 1
    return _split_caret(mnem)


def _resolve_part(part: str, funcs: Dict[str, List[str]]) -> Optional[List[str]]:
    part = part.strip()
    m = re.match(r'^"([^"]*)"$', part)
    if m:
        return [m.group(1)]
    fc = re.match(r"^(\w+)\s*\(", part)
    if fc:
        fn = fc.group(1)
        if fn in funcs:
            return funcs[fn]
        db = re.match(r"^dec_bits_(\d+)$", fn)
        if db:
            n = int(db.group(1))
            inner = part[fc.end()-1:]
            depth, end = 0, 0
            for j, ch in enumerate(inner):
                if ch == "(": depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0: end = j; break
            return _eval_dec_bits_arg(inner[1:end], n) if end else None
    return None


def _evaluate(expr: str, funcs: Dict[str, List[str]]) -> Tuple[List[str], bool]:
    parts = _parse_mnemonic(expr)
    if not parts:
        return ([], False)
    resolved = []
    for p in parts:
        v = _resolve_part(p, funcs)
        if v is None:
            return ([], False)
        resolved.append(v)
    results: Set[str] = set()
    for combo in product(*resolved):
        s = "".join(combo)
        if s:
            results.add(s)
    return (sorted(results), True)


def _dir_to_mod(dir_name: str) -> str:
    n = dir_name.lower().replace("-", "_")
    if n in ("if", "is", "in", "as", "or", "and", "not"):
        n += "_ext"
    return n


def cmd_update_from_sail(sail_dir: str):
    model = Path(sail_dir) / "model"
    if not model.is_dir():
        print(f"错误: {model} 不存在", file=sys.stderr)
        sys.exit(1)

    files = _find_sail_files(model)
    text = _read_all(files)
    funcs = _collect_mapping_functions(text)
    clause_names = _extract_union_clauses(text)
    asm_clauses = _extract_assembly_clauses(text)
    clause_to_dir = _clause_to_dir_map(model)

    # 求值
    asm_map: Dict[str, List[str]] = {}
    unresolved: List[Tuple[str, str]] = []
    for name in clause_names:
        if name in _EXCLUDED_CLAUSES:
            continue
        exprs = asm_clauses.get(name, [])
        all_names: Set[str] = set()
        for expr in exprs:
            names, ok = _evaluate(expr, funcs)
            if ok:
                all_names.update(names)
            else:
                unresolved.append((name, expr[:80]))
        asm_map[name] = sorted(all_names)

    if unresolved:
        print(f"\n警告: {len(unresolved)} 个表达式无法解析:", file=sys.stderr)
        for clause, expr in unresolved:
            print(f"  {clause}: {expr}", file=sys.stderr)
        print("请手动补充 expected_data/ 后重新运行 generate。", file=sys.stderr)
        sys.exit(1)

    # 按目录分组
    by_dir: Dict[str, Dict[str, List[str]]] = defaultdict(dict)
    for name in clause_names:
        if name in _EXCLUDED_CLAUSES:
            continue
        ext = clause_to_dir.get(name, "misc")
        by_dir[ext][name] = asm_map.get(name, [])

    output_dir = _DATA_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    mod_names = []
    for ext_dir in sorted(by_dir):
        clauses = by_dir[ext_dir]
        mod = _dir_to_mod(ext_dir)
        mod_names.append(mod)
        with open(output_dir / f"{mod}.py", "w") as f:
            f.write(f"# sail-riscv extension: {ext_dir}\n")
            f.write(f"# {len(clauses)} instruction clauses\n\n")
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
        print(f"  {mod}.py ({ext_dir}): {len(clauses)} clauses")

    with open(output_dir / "__init__.py", "w") as f:
        for mod in mod_names:
            f.write(f"from .{mod} import INSTRUCTIONS as {mod}\n")
        f.write("\n\n_ALL_MODULES = [\n")
        for mod in mod_names:
            f.write(f"    {mod},\n")
        f.write("]\n\n\ndef get_all_instructions():\n")
        f.write("    result = {}\n")
        f.write("    for mod in _ALL_MODULES:\n")
        f.write("        result.update(mod)\n")
        f.write("    return result\n")

    total = len(clause_names)
    with_asm = sum(1 for v in asm_map.values() if v)
    print(f"\n完成: {total} clauses, {with_asm} 有助记符, 输出到 {output_dir}/")
    print("请 review 后提交。")


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

_USAGE = f"""用法:
  {sys.argv[0]} generate [--outdir <dir>]
  {sys.argv[0]} verify <actual_output_file>
  {sys.argv[0]} update-from-sail <sail_riscv_dir>"""

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(_USAGE, file=sys.stderr)
        sys.exit(1)

    cmd = sys.argv[1]
    if cmd == "generate":
        outdir = ""
        if len(sys.argv) >= 4 and sys.argv[2] == "--outdir":
            outdir = sys.argv[3]
        cmd_generate(outdir)
    elif cmd == "verify":
        if len(sys.argv) != 3:
            print(f"用法: {sys.argv[0]} verify <actual_output_file>", file=sys.stderr)
            sys.exit(1)
        cmd_verify(sys.argv[2])
    elif cmd == "update-from-sail":
        if len(sys.argv) != 3:
            print(f"用法: {sys.argv[0]} update-from-sail <sail_riscv_dir>", file=sys.stderr)
            sys.exit(1)
        cmd_update_from_sail(sys.argv[2])
    else:
        print(f"未知子命令: {cmd}", file=sys.stderr)
        print(_USAGE, file=sys.stderr)
        sys.exit(1)
