#!/usr/bin/env python3
"""按位化简后用共享决策图计数；隐藏位作存在量化，不逐个抽取模型。"""

from functools import lru_cache
import z3


def conjuncts(expression):
    if z3.is_and(expression):
        return [x for child in expression.children() for x in conjuncts(child)]
    return [expression]


def variables(expression):
    found = {}
    pending = [expression]
    seen = set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_const(node) and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            found[node.get_id()] = node
        pending.extend(node.children())
    return list(found.values())


def eliminate_memory(expression, prove=False):
    """同一字节数组的对齐八字节读取，精确转成有限读取间的一致性约束。"""
    assertions = conjuncts(expression)
    remaining = []
    reads = []
    for assertion in assertions:
        read = None
        if z3.is_eq(assertion):
            for value, packed in [
                assertion.children(),
                list(reversed(assertion.children())),
            ]:
                if not (z3.is_const(value) and z3.is_bv(value) and value.size() == 64):
                    continue

                def leaves(node):
                    if node.decl().kind() == z3.Z3_OP_CONCAT:
                        return [x for c in node.children() for x in leaves(c)]
                    return [node]

                parts = leaves(packed)
                if len(parts) != 8 or not all(z3.is_select(x) for x in parts):
                    continue
                array = parts[-1].arg(0)
                base = parts[-1].arg(1)
                assert z3.is_const(array) and array.sort().domain() == z3.BitVecSort(64)
                assert all(x.arg(0).eq(array) for x in parts)
                assert z3.is_true(z3.simplify(z3.Extract(2, 0, base) == 0)), base
                for offset, part in enumerate(reversed(parts)):
                    assert z3.is_true(z3.simplify(part.arg(1) == base + offset)), part
                read = (array, base, value)
                break
        if read is None:
            remaining.append(assertion)
        else:
            reads.append(read)
    assert all(not z3.is_array(v) for x in remaining for v in variables(x)), (
        "存在未处理的数组约束"
    )
    for i, (array, addr, value) in enumerate(reads):
        for other, other_addr, other_value in reads[:i]:
            assert array.eq(other), "暂不处理多个独立数组"
            remaining.append(z3.Implies(addr == other_addr, value == other_value))
    reduced = z3.And(*remaining)
    info = dict(reads=len(reads), consistency_pairs=len(reads) * (len(reads) - 1) // 2)
    if prove:
        assert reads
        array = reads[0][0]
        witness = z3.K(z3.BitVecSort(64), z3.BitVecVal(0, 8))
        for _, addr, value in reads:
            for byte in range(8):
                witness = z3.Store(
                    witness, addr + byte, z3.Extract(byte * 8 + 7, byte * 8, value)
                )
        forward = z3.Solver()
        forward.set(timeout=30000)
        forward.add(expression, z3.Not(reduced))
        assert forward.check() == z3.unsat, "原数组约束未能推出有限读取一致性"
        backward = z3.Solver()
        backward.set(timeout=30000)
        backward.add(reduced, z3.Not(z3.substitute(expression, (array, witness))))
        assert backward.check() == z3.unsat, "显式数组见证未能满足原约束"
        info["original_implies_reduced"] = "unsat_counterexample"
        info["reduced_has_explicit_array_witness"] = "unsat_counterexample"
    return reduced, info


class BDD:
    """同一变量顺序下复用相同子问题；0/1 是不满足/满足终点。"""

    def __init__(self, names, node_cap=2000000):
        self.names = list(names)
        self.rank = {name: i for i, name in enumerate(names)}
        self.nodes = [(len(names), 0, 0), (len(names), 1, 1)]
        self.unique = {}
        self.node_cap = node_cap
        self.apply = lru_cache(maxsize=1000000)(self._apply)
        self.neg = lru_cache(maxsize=1000000)(self._neg)

    def mk(self, var, low, high):
        if low == high:
            return low
        key = (var, low, high)
        if key not in self.unique:
            if len(self.nodes) >= self.node_cap:
                raise MemoryError(f"决策图达到 {self.node_cap} 节点额度")
            self.unique[key] = len(self.nodes)
            self.nodes.append(key)
        return self.unique[key]

    def _neg(self, node):
        if node < 2:
            return 1 - node
        var, low, high = self.nodes[node]
        return self.mk(var, self.neg(low), self.neg(high))

    def _apply(self, op, left, right):
        if left > right:
            return self.apply(op, right, left)
        if op == "and":
            if left == 0 or right == 0:
                return 0
            if left == 1:
                return right
            if left == right:
                return left
        elif op == "or":
            if left == 1 or right == 1:
                return 1
            if left == 0:
                return right
            if left == right:
                return left
        elif op == "xor":
            if left == 0:
                return right
            if left == 1:
                return self.neg(right)
            if left == right:
                return 0
        else:
            raise AssertionError(op)
        lv, ll, lh = self.nodes[left]
        rv, rl, rh = self.nodes[right]
        var = min(lv, rv)
        return self.mk(
            var,
            self.apply(op, ll if lv == var else left, rl if rv == var else right),
            self.apply(op, lh if lv == var else left, rh if rv == var else right),
        )

    def build(self, expression):
        @lru_cache(maxsize=None)
        def visit(node):
            if z3.is_true(node):
                return 1
            if z3.is_false(node):
                return 0
            if z3.is_const(node):
                assert z3.is_bool(node)
                return self.mk(self.rank[str(node)], 0, 1)
            kind = node.decl().kind()
            children = node.children()
            if kind == z3.Z3_OP_NOT:
                return self.neg(visit(children[0]))
            if kind in [z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_XOR]:
                op = {z3.Z3_OP_AND: "and", z3.Z3_OP_OR: "or", z3.Z3_OP_XOR: "xor"}[kind]
                result = 1 if op == "and" else 0
                for child in children:
                    result = self.apply(op, result, visit(child))
                return result
            if kind in [z3.Z3_OP_EQ, z3.Z3_OP_IFF]:
                return self.neg(
                    self.apply("xor", visit(children[0]), visit(children[1]))
                )
            if kind == z3.Z3_OP_IMPLIES:
                return self.apply(
                    "or", self.neg(visit(children[0])), visit(children[1])
                )
            if kind == z3.Z3_OP_ITE:
                c, a, b = map(visit, children)
                return self.apply(
                    "or", self.apply("and", c, a), self.apply("and", self.neg(c), b)
                )
            raise AssertionError(node)

        return visit(expression)

    def exists(self, node, hidden):
        @lru_cache(maxsize=None)
        def visit(n):
            if n < 2:
                return n
            var, low, high = self.nodes[n]
            low, high = visit(low), visit(high)
            return (
                self.apply("or", low, high)
                if var in hidden
                else self.mk(var, low, high)
            )

        return visit(node)

    def count(self, node, targets):
        ranks = sorted(targets)
        positions = {rank: i for i, rank in enumerate(ranks)}

        @lru_cache(maxsize=None)
        def visit(n, level):
            if n < 2:
                return n * (1 << (len(ranks) - level))
            var, low, high = self.nodes[n]
            pos = positions[var]
            return (1 << (pos - level)) * (visit(low, pos + 1) + visit(high, pos + 1))

        return visit(node, 0)


def count_formula(expression, targets, order=None, stats=None):
    """先拆完全不相连的布尔分量，再各自计数并相乘。"""
    expression = z3.simplify(expression)
    target_names = {str(v) for v in targets}
    clauses = conjuncts(expression)
    supports = [{str(v) for v in variables(c)} for c in clauses]
    parent = list(range(len(clauses)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    owner = {}
    for i, support in enumerate(supports):
        for name in support:
            if name in owner:
                parent[find(i)] = find(owner[name])
            owner[name] = i
    groups = {}
    for i in range(len(clauses)):
        groups.setdefault(find(i), []).append(i)
    total = 1 << len(target_names - set(owner))
    details = []
    ordered = {name: i for i, name in enumerate(order or sorted(owner))}
    for indices in groups.values():
        names = set().union(*(supports[i] for i in indices))
        selected = target_names & names
        if not selected:
            solver = z3.Solver()
            solver.set(timeout=30000)
            solver.add(*[clauses[i] for i in indices])
            result = solver.check()
            assert result in [z3.sat, z3.unsat], result
            if result == z3.unsat:
                return 0
            continue
        names = sorted(names, key=lambda name: ordered[name])
        bdd = BDD(names)
        root = bdd.build(z3.And(*[clauses[i] for i in indices]))
        hidden = {bdd.rank[name] for name in names if name not in selected}
        root = bdd.exists(root, hidden)
        value = bdd.count(root, {bdd.rank[name] for name in selected})
        total *= value
        details.append(
            dict(
                bits=len(selected),
                hidden=len(hidden),
                nodes=len(bdd.nodes),
                count=str(value),
            )
        )
        bdd.apply.cache_clear()
        bdd.neg.cache_clear()
    if stats is not None:
        stats.update(
            components=details, unconstrained_bits=len(target_names - set(owner))
        )
    return total
