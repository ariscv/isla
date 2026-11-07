#!/usr/bin/env python3
"""读取原路径 SMT 和守卫定义，计算 F16 投影位组合的精确数。"""

import argparse
import ast
from functools import lru_cache
import json
from pathlib import Path
import re
import sys
import time
import z3
from exact_bdd import count_formula, eliminate_memory, variables


def parse_debug(text, resolve):
    text = re.sub(r"Var\(Sym \{ id: (\d+) \}\)", r"V(\1)", text)
    text = re.sub(r"Bits64\(B64 \{ len: (\d+), bits: (\d+) \}\)", r"B(\2,\1)", text)
    text = text.replace("true", "True").replace("false", "False")
    functions = {
        "V": resolve,
        "B": z3.BitVecVal,
        "Bits": lambda bits: z3.BitVecVal(
            sum(int(v) << i for i, v in enumerate(bits)), len(bits)
        ),
        "Bool": z3.BoolVal,
        "Extract": z3.Extract,
        "Concat": z3.Concat,
        "Eq": lambda a, b: a == b,
        "Neq": lambda a, b: a != b,
        "Not": z3.Not,
        "And": z3.And,
        "Or": z3.Or,
        "Ite": z3.If,
        "ZeroExtend": z3.ZeroExt,
        "SignExtend": z3.SignExt,
        "Bvand": lambda a, b: a & b,
        "Bvor": lambda a, b: a | b,
        "Bvxor": lambda a, b: a ^ b,
        "Bvnot": lambda a: ~a,
        "Bvadd": lambda a, b: a + b,
        "Bvsub": lambda a, b: a - b,
        "Bvshl": lambda a, b: a << b,
        "Bvsrem": z3.SRem,
        "Bvule": z3.ULE,
        "Bvuge": z3.UGE,
        "Store": z3.Store,
    }
    tree = ast.parse(text, mode="eval")
    for node in ast.walk(tree):
        assert isinstance(
            node, (ast.Expression, ast.Call, ast.Name, ast.Load, ast.Constant, ast.List)
        ), ast.dump(node)
        if isinstance(node, ast.Name):
            assert node.id in functions, node.id
    return eval(
        compile(tree, "<原始守卫定义>", "eval"), {"__builtins__": {}}, functions
    )


def prepare(smt_path, report):
    original = z3.And(*z3.parse_smt2_file(str(smt_path)))
    declarations = {str(v): v for v in variables(original)}

    @lru_cache(maxsize=None)
    def resolve(number):
        name = f"v{number}"
        if name in report["definitions"]:
            return parse_debug(report["definitions"][name], resolve)
        assert f"k!{number}" in declarations, f"原路径未声明守卫输入 {name}"
        return declarations[f"k!{number}"]

    projected = [parse_debug(text, resolve) for text in report["projected_bits"]]
    assert all(z3.is_eq(p) and z3.is_bv(p.arg(0)) for p in projected)
    keys = []
    for p in projected:
        extract = next(
            child for child in p.children() if child.decl().kind() == z3.Z3_OP_EXTRACT
        )
        assert (
            extract.decl().kind() == z3.Z3_OP_EXTRACT
            and extract.params()[0] == extract.params()[1]
        )
        assert z3.is_const(extract.arg(0)), extract
        keys.append((str(extract.arg(0)), extract.params()[0]))
    assert len(keys) == len(set(keys))
    record_by_id = {r["record_id"]: r for r in report["guard_records"]}

    @lru_cache(maxsize=None)
    def context(record_id):
        record = record_by_id[record_id]
        parent = record["parent_record"]
        if parent is None:
            return z3.BoolVal(True)
        condition = resolve(record_by_id[parent]["condition"])
        if record["arm"] == "else":
            condition = z3.Not(condition)
        else:
            assert record["arm"] == "then"
        return z3.And(context(parent), condition)

    guards = [
        z3.And(context(i), resolve(record_by_id[i]["condition"]))
        for i in report["record_ids"]
    ]
    reduced, memory = eliminate_memory(original)
    # 每个原自由 BV 位对应一个显式布尔量，避免 bit-blast 隐式引入不可追溯变量。
    all_vars = {str(v): v for e in [reduced, *guards] for v in variables(e)}
    substitutions = []
    for name, value in all_vars.items():
        if z3.is_bv(value):
            bits = [
                z3.If(z3.Bool(f"{name}__{bit}"), z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
                for bit in reversed(range(value.size()))
            ]
            substitutions.append(
                (value, z3.Concat(*bits) if len(bits) > 1 else bits[0])
            )
        else:
            assert z3.is_bool(value), value

    def blast(e):
        goal = z3.Goal()
        goal.add(z3.substitute(e, *substitutions))
        result = z3.Then("simplify", "bit-blast", "simplify")(goal)
        assert len(result) == 1
        return z3.And(*list(result[0]))

    boolean = blast(reduced)
    target = [z3.Bool(f"{name}__{bit}") for name, bit in keys]
    # 守卫可能依赖未投影位。只在实际按位依赖完全包含时，才能直接对投影位求和。
    selected = {str(b) for b in target}
    guard_functions = []
    for guard in guards:
        bg = blast(guard)
        missing = {str(v) for v in variables(bg)} - selected
        assert not missing, f"守卫还依赖未计数位 {missing}"
        guard_functions.append(bg)
    return original, reduced, boolean, target, guard_functions, memory


def count_path(folder, signature):
    start = time.monotonic()
    report = json.loads((folder / "reports" / f"glue-{signature}.json").read_text())
    original, reduced, boolean, targets, guards, memory = prepare(
        folder / "smt" / f"path-{signature}.smt2", report
    )

    # PPN 相同位在不同 PTE 中相邻，有利于复用地址相等的剩余子问题。
    def key(name):
        if "__" in name:
            symbol, bit = name.split("__")
            return (0, -int(bit), int(symbol[2:]))
        return (1, 0, name)

    names = {str(v) for v in variables(boolean)}
    order = sorted(names, key=key)
    stats = {}
    value = count_formula(boolean, targets, order, stats)
    return dict(
        signature=str(signature),
        exact=str(value),
        projected_bits=len(targets),
        guards=len(guards),
        guard_classes=report["class_count"],
        guard_functional=True,
        memory=memory,
        seconds=time.monotonic() - start,
        **stats,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder", type=Path)
    parser.add_argument("--signature")
    args = parser.parse_args()
    sys.setrecursionlimit(20000)
    destination = args.folder / "exact"
    destination.mkdir(exist_ok=True)
    paths = (
        [args.signature]
        if args.signature
        else [p.stem[5:] for p in (args.folder / "smt").glob("path-*.smt2")]
    )
    for signature in paths:
        result = count_path(args.folder, signature)
        (destination / f"{signature}.json").write_text(
            json.dumps(result, indent=2) + "\n"
        )
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
