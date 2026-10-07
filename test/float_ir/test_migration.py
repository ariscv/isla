"""防止IR装配吞掉参数引用差异或元组字段顺序冲突。"""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('float_migration', ROOT / 'scripts/migrate_float_ir.py')
migration = importlib.util.module_from_spec(spec)
spec.loader.exec_module(migration)


class MigrationConflictTests(unittest.TestCase):
    def test_reused_function_cannot_swap_argument_identity(self):
        interface = 'val zriscv_demo : (%bv8, %bv8) -> %bv8\n\n'
        source = interface + '''val zhelper : (%bv8, %bv8) -> %bv8
fn zhelper(z3zE1, z3zE2) {
  return = z3zE1;
  end;
}
fn zriscv_demo(za, zb) {
  return = zhelper(za, zb);
  end;
}
files "demo.sail"
'''
        target = interface + '''val zhelper : (%bv8, %bv8) -> %bv8
fn zhelper(z3zE3, z3zE4) {
  return = z3zE4;
  end;
}
files "demo.sail"
'''
        with self.assertRaisesRegex(AssertionError, '同名定义冲突'):
            migration.assemble(source, target, set())

    def test_reused_tuple_cannot_change_field_order(self):
        common = '''struct zpair {
  zleft: %bv8,
  zright: %bv8
}
#tuplestruct zpair zleft zright
val zriscv_demo : (%bv8, %bv8) -> %struct zpair
'''
        source = common + '''fn zriscv_demo(za, zb) {
  return = struct zpair {zleft = za, zright = zb};
  end;
}
files "demo.sail"
'''
        target = common.replace('#tuplestruct zpair zleft zright', '#tuplestruct zpair zright zleft') + 'files "demo.sail"\n'
        with self.assertRaisesRegex(AssertionError, '元组字段顺序冲突'):
            migration.assemble(source, target, set())


if __name__ == '__main__':
    unittest.main()
