"""计数工具的先行测试；只穷举极小人工公式核对计数。"""

import itertools
import unittest
import z3
from exact_bdd import count_formula, eliminate_memory


class ExactCountTests(unittest.TestCase):
    def test_自由位与隐藏变量(self):
        a, b, h = z3.Bools("a b h")
        self.assertEqual(count_formula(z3.Xor(a, h), [a, b]), 4)
        self.assertEqual(count_formula(z3.And(a == h, b != h), [a, b]), 2)
        self.assertEqual(count_formula(z3.BoolVal(False), [a, b]), 0)

    def test_独立分量相乘(self):
        a, b, c, d = z3.Bools("a b c d")
        self.assertEqual(
            count_formula(z3.And(z3.Or(a, b), z3.Xor(c, d)), [a, b, c, d]), 6
        )

    def test_小公式与直接定义一致(self):
        a, b, c, d = z3.Bools("a b c d")
        f = z3.And(z3.Implies(a, b), z3.Or(c, d), z3.Xor(b, c))
        expected = sum(
            z3.is_true(
                z3.simplify(z3.substitute(f, *zip([a, b, c, d], map(z3.BoolVal, vs))))
            )
            for vs in itertools.product([False, True], repeat=4)
        )
        self.assertEqual(count_formula(f, [a, b, c, d]), expected)

    def test_位运算与隐藏位的解析结果(self):
        a, b = z3.BitVecs("small_a small_b", 4)
        abits = [z3.Bool(f"a{i}") for i in range(4)]
        bbits = [z3.Bool(f"b{i}") for i in range(4)]

        def word(bits):
            return z3.Concat(
                *[
                    z3.If(bit, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
                    for bit in reversed(bits)
                ]
            )

        formula = z3.And((a & 3) == (b & 3), z3.ULT(a, 10), z3.UGE(b, 4))
        goal = z3.Goal()
        goal.add(z3.substitute(formula, (a, word(abits)), (b, word(bbits))))
        boolean = z3.And(*list(z3.Then("simplify", "bit-blast", "simplify")(goal)[0]))
        # a 的 0..9 各有合法 b；低两位组合均有见证。
        self.assertEqual(count_formula(boolean, abits), 10)
        self.assertEqual(count_formula(boolean, abits[:2]), 4)
        order = list(reversed([str(x) for x in abits + bbits]))
        self.assertEqual(count_formula(boolean, abits, order), 10)

    def test_同址读取必须一致(self):
        mem = z3.Array("m", z3.BitVecSort(64), z3.BitVecSort(8))
        a, b = z3.BitVecs("a b", 64)

        def word(addr):
            return z3.Concat(*[z3.Select(mem, addr + i) for i in range(7, -1, -1)])

        original = z3.And(
            a == word(z3.BitVecVal(4096, 64)), b == word(z3.BitVecVal(4096, 64)), a != b
        )
        translated, info = eliminate_memory(original, prove=True)
        solver = z3.Solver()
        solver.add(translated)
        self.assertEqual(solver.check(), z3.unsat)
        self.assertEqual(info["reads"], 2)
        consistent = z3.And(
            a == word(z3.BitVecVal(4096, 64)), b == word(z3.BitVecVal(4096, 64))
        )
        translated, info = eliminate_memory(consistent, prove=True)
        solver = z3.Solver()
        solver.add(translated, a == 123)
        self.assertEqual(solver.check(), z3.sat)
        self.assertEqual(solver.model().eval(b).as_long(), 123)


if __name__ == "__main__":
    unittest.main()
