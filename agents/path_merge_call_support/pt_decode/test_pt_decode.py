"""P1：先定义页表解码、严格输入和分布比较的可观察行为。"""
import json
import contextlib
import io
from pathlib import Path
import tempfile
import unittest

from pt_decode import (
    Config, DecodeError, aggregate, compare_distributions, decode_pte,
    decode_sample, effective_address, load_samples, parse_satp, read_word,
    shape_key, classify_pte, memory_bytes,
    result_category,
)


def bits(value, width=64):
    return {"bits": f"{value:0{width}b}"}


def cells(address, value):
    return [{"address": address+i, "value": (value >> (i*8)) & 255, "bytes": 1}
            for i in range(8)]


def sample(words, result="Retire_Success", exception=None, mode=8, va=0x20000000):
    instruction = {f"tuple#%bv12_%bv5_%bv5_%bool_%i64{i}": v for i, v in enumerate(
        [bits(0, 12), bits(1, 5), bits(2, 5), {"bool": False}, {"i64": "8"}])}
    outcome = {"ctor": result, "value": {"unit": True}}
    if exception:
        outcome["value"] = {"struct": {
            "tuple#%bv64_%union zExceptionType0": bits(va),
            "tuple#%bv64_%union zExceptionType1": {"ctor": exception, "value": {"unit": True}}}}
    return dict(schema_version=1, sample_id=0, mode="fork", path_signature=0,
                class_id=None, truncated=False, pre_registers={
                    "satp": bits((mode << 60) | 0x80200), "x1": bits(va),
                    "mstatus": {"struct": {"bits": bits(0)}},
                    "cur_privilege": {"enum": "Supervisor"},
                    "$instruction": {"ctor": "LOAD", "value": {"struct": instruction}}},
                post_registers={}, isa_state={}, pre_memory=[c for a, v in words for c in cells(a, v)],
                post_memory=[], result=outcome, ret_val="测试结果")


CFG = Config(svrsw60t59b=False, dirty_update=False)
ROOT = 0x80200000


def store_sample(words, result="Retire_Success", exception=None, mode=8, va=0x20000000):
    s = sample(words, result, exception, mode, va)
    # base_insts.sail: STORE(imm, rs2, rs1, width)，与真实样本一致。
    s["pre_registers"]["$instruction"] = {"ctor": "STORE", "value": {"struct": {
        f"tuple#%bv12_%bv5_%bv5_%i64{i}": v for i, v in enumerate(
            [bits(0, 12), bits(2, 5), bits(1, 5), {"i64": "8"}])}}}
    return s


class StoreTests(unittest.TestCase):
    def test_store_tuple_address_and_assembly(self):
        s = store_sample([])
        fields = s["pre_registers"]["$instruction"]["value"]["struct"]
        fields["tuple#%bv12_%bv5_%bv5_%i640"] = bits(0xff8, 12)
        self.assertEqual(effective_address(s), 0x1ffffff8)
        fields["tuple#%bv12_%bv5_%bv5_%i642"] = bits(0, 5)
        self.assertEqual(effective_address(s), (1 << 64)-8)
        del s["pre_registers"]["$instruction"]
        s["isa_state"]["$instruction"] = "sd x2, -0x8(x1)"
        self.assertEqual(effective_address(s), 0x1ffffff8)

    def test_store_bad_instruction_rejected_even_with_va(self):
        for field, value in [("tuple#%bv12_%bv5_%bv5_%i643", {"i64": "4"}),
                             ("new", bits(0))]:
            s = store_sample([(ROOT, 0)], "Memory_Exception", "E_SAMO_Page_Fault")
            s["pre_registers"]["$instruction"]["value"]["struct"][field] = value
            with self.assertRaises(DecodeError):
                decode_sample(s, CFG, va=0x20000000)
        s["pre_registers"]["$instruction"]["ctor"] = "UNKNOWN"
        with self.assertRaises(DecodeError):
            decode_sample(s, CFG, va=0x20000000)

    def test_store_exception_family_is_strict(self):
        for suffix in ["Page_Fault", "Access_Fault", "Addr_Align"]:
            s = store_sample([], "Memory_Exception", f"E_SAMO_{suffix}")
            self.assertEqual(result_category(s["result"], 0x20000000, "store")[1], f"E_SAMO_{suffix}")
            with self.assertRaises(DecodeError):
                result_category(s["result"], 0x20000000, "load")
        with self.assertRaises(DecodeError):
            result_category(sample([])["result"], 0x20000000, "unknown")

    def test_store_permissions_and_ad_bits(self):
        for flags, reason in [(0x43, "store_permission"), (0x49, "store_permission"),
                              (0x47, "dirty_update_disabled"), (7, "accessed_update_disabled"),
                              (0xd7, "privilege_permission")]:
            s = store_sample([(ROOT, flags)], "Memory_Exception", "E_SAMO_Page_Fault")
            s["pre_registers"]["mstatus"]["struct"]["bits"] = bits(1 << 19)
            self.assertEqual(decode_sample(s, CFG)["failure_reason"], reason)
        # LOAD 无须 D=1，STORE 的 SUM/User/MPRV 仍复用同一权限流程。
        for privilege, status in [("Supervisor", 1 << 18), ("User", 0),
                                  ("Machine", (1 << 17) | (1 << 11) | (1 << 18))]:
            s = store_sample([(ROOT, 0xd7), (0x20000000, 99)])
            s["post_memory"] = cells(0x20000000, 0)
            s["pre_registers"]["cur_privilege"] = {"enum": privilege}
            s["pre_registers"]["mstatus"]["struct"]["bits"] = bits(status)
            self.assertIsNone(decode_sample(s, CFG)["failure_reason"])

    def test_store_unknown_preimage_and_post_data(self):
        s = store_sample([(ROOT, 0xc7)])
        s["pre_memory"] += [dict(c, value=None) for c in cells(0x20000000, 0)]
        s["post_memory"] = cells(0x20000000, 123)
        d = decode_sample(s, CFG)
        self.assertEqual(d["paddr_if_success"], 0x20000000)
        self.assertEqual(d["entries"][-1]["value"], "0x000000000000007b")
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/"samples.jsonl"
            p.write_text(json.dumps(s)+'\n')
            self.assertEqual(len(list(load_samples(p))), 1)
        s["post_memory"] = []
        with self.assertRaisesRegex(DecodeError, "missing_memory"):
            decode_sample(s, CFG)

    def test_store_null_pte_and_unrelated_null_rejected(self):
        s = store_sample([(ROOT, 0)])
        s["pre_memory"][0]["value"] = None
        with self.assertRaisesRegex(DecodeError, "未知.*初值"):
            decode_sample(s, CFG)
        s = store_sample([(ROOT, 0)], "Memory_Exception", "E_SAMO_Page_Fault")
        s["pre_memory"] += [dict(c, value=None) for c in cells(0x1000, 0)]
        with self.assertRaisesRegex(DecodeError, "无法归属"):
            decode_sample(s, CFG)

    def test_store_pma_uses_read_for_pte_and_write_for_data(self):
        for readable, writable, expected in [(True, False, "data_write_pma_access_fault"),
                                               (False, True, "pte_read_pma_access_fault")]:
            words = [(ROOT, 0xc7)] if readable else []
            s = store_sample(words, "Memory_Exception", "E_SAMO_Access_Fault")
            s["pre_registers"]["pma_regions"] = {"list": [{"struct": {
                "base": bits(0), "size": bits(1 << 63), "include_in_device_tree": {"bool": True},
                "attributes": {"struct": {"readable": {"bool": readable},
                                            "writable": {"bool": writable}}}}}]}
            self.assertEqual(decode_sample(s, CFG)["failure_reason"], expected)
        s = store_sample([(0x20000000, 0)], mode=0)
        s["post_memory"] = cells(0x20000000, 1)
        s["pre_registers"]["pma_regions"] = {"list": [{"struct": {
            "base": bits(0), "size": bits(1 << 63), "include_in_device_tree": {"bool": True},
            "attributes": {"struct": {"readable": {"bool": False}, "writable": {"bool": True}}}}}]}
        self.assertIsNone(decode_sample(s, CFG)["failure_reason"])

    def test_store_sv48_full_walk_and_canonical_va(self):
        words = [(ROOT, (0x80300 << 10) | 1), (0x80300000, (0x80400 << 10) | 1),
                 (0x80400800, (0x80500 << 10) | 1), (0x80500000, (0x80600 << 10) | 0xc7),
                 (0x80600000, 77)]
        s = store_sample(words, mode=9)
        s["post_memory"] = cells(0x80600000, 42)
        d = decode_sample(s, CFG)
        self.assertEqual((d["mode"], d["vpn"], d["paddr_if_success"]), ("Sv48", [0, 256, 0, 0], 0x80600000))
        self.assertEqual([e["level"] for e in d["entries"][:-1]], [3, 2, 1, 0])
        s = store_sample([], "Memory_Exception", "E_SAMO_Page_Fault", mode=9, va=1 << 47)
        self.assertEqual(decode_sample(s, CFG)["failure_reason"], "noncanonical_va")

    def test_store_enabled_ad_update_requires_exact_post_memory(self):
        cfg = Config(svrsw60t59b=False, dirty_update=True)
        for flags in [7, 0x47, 0x87]:
            s = store_sample([(ROOT, flags), (0x20000000, 0)])
            s["post_memory"] = cells(0x20000000, 0)
            with self.assertRaisesRegex(DecodeError, "missing_memory"):
                decode_sample(s, cfg)
            s["post_memory"] += cells(ROOT, 0xc7)
            self.assertIsNone(decode_sample(s, cfg)["failure_reason"])
            s["post_memory"] = cells(ROOT, 0x47)+cells(0x20000000, 0)
            with self.assertRaisesRegex(DecodeError, "A/D 位更新"):
                decode_sample(s, cfg)

    def test_store_alignment_needs_explicit_platform_configuration(self):
        s = store_sample([], "Memory_Exception", "E_SAMO_Addr_Align", va=0x20000001)
        with self.assertRaisesRegex(DecodeError, "misaligned-access"):
            decode_sample(s, CFG)
        cfg = Config(svrsw60t59b=False, dirty_update=False, misaligned_access=False)
        self.assertEqual(decode_sample(s, cfg)["failure_reason"], "address_misaligned")
        s = store_sample([], "Memory_Exception", "E_SAMO_Addr_Align")
        with self.assertRaises(DecodeError):
            decode_sample(s, cfg)

    def test_explicit_access_and_address_without_instruction(self):
        s = store_sample([(ROOT, 0)], "Memory_Exception", "E_SAMO_Page_Fault")
        del s["pre_registers"]["$instruction"]
        with self.assertRaisesRegex(DecodeError, "访问类型"):
            decode_sample(s, CFG, va=0x20000000)
        d = decode_sample(s, CFG, va=0x20000000, access="store")
        self.assertEqual(d["exception_type"], "E_SAMO_Page_Fault")
        s = store_sample([(ROOT, 0)], "Memory_Exception", "E_SAMO_Page_Fault")
        with self.assertRaisesRegex(DecodeError, "--access.*不符"):
            decode_sample(s, CFG, va=0x20000000, access="load")
        del s["pre_registers"]["x1"]
        self.assertEqual(decode_sample(s, CFG, va=0x20000000)["va"], 0x20000000)

    def test_store_cli_alignment_and_automatic_address(self):
        from pt_decode import main
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            args = ["--fork", str(root/'fork.jsonl'), "--merge", str(root/'merge.jsonl'),
                    "--out", str(root/'out'), "--svrsw60t59b", "disabled", "--dirty-update", "disabled"]
            for aligned in [True, False]:
                va = 0x20000000 if aligned else 0x20000001
                s = store_sample([(ROOT, 0)] if aligned else [], "Memory_Exception",
                                 "E_SAMO_Page_Fault" if aligned else "E_SAMO_Addr_Align", va=va)
                for side in ["fork", "merge"]:
                    s["mode"] = side
                    (root/f'{side}.jsonl').write_text(json.dumps(s)+'\n')
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(main(args+["--misaligned-access", "disabled"]), 0)
                table = json.loads((root/'out/page_tables.json').read_text())["page_tables"][0]
                self.assertEqual((table["access"], table["va"]), ("store", va))

    def test_load_and_store_success_have_different_shapes(self):
        load = decode_sample(sample([(ROOT, 0xc7), (0x20000000, 0)]), CFG)
        s = store_sample([(ROOT, 0xc7), (0x20000000, 0)])
        s["post_memory"] = cells(0x20000000, 0)
        self.assertNotEqual(shape_key(load), shape_key(decode_sample(s, CFG)))


class FieldsTests(unittest.TestCase):
    def test_modes_and_vpns(self):
        for mode, levels in [(8, 3), (9, 4), (10, 5)]:
            s = parse_satp((mode << 60) | (0x1234 << 44) | 0x80200)
            self.assertEqual((s["levels"], s["asid"], s["root_paddr"]), (levels, 0x1234, ROOT))
            va = sum((i+1) << (12+9*i) for i in range(levels))
            d = decode_sample(sample([(ROOT+levels*8, 0)], "Memory_Exception", "E_Load_Page_Fault", mode, va), CFG)
            self.assertEqual(d["vpn"], list(range(1, levels+1)))
        self.assertEqual(parse_satp(0)["levels"], 0)
        with self.assertRaises(DecodeError):
            parse_satp(7 << 60)

    def test_pte_all_bit_positions(self):
        positions = {"V": (0, 1), "R": (1, 1), "W": (2, 1), "X": (3, 1),
                     "U": (4, 1), "G": (5, 1), "A": (6, 1), "D": (7, 1),
                     "RSW": (8, 2), "PPN": (10, 44), "reserved": (54, 5),
                     "RSW_60t59b": (59, 2), "PBMT": (61, 2), "N": (63, 1)}
        for name, (lo, width) in positions.items():
            for bit in range(lo, lo+width):
                decoded = decode_pte(1 << bit)
                self.assertEqual(decoded[name], 1 << (bit-lo))
                self.assertEqual(sum(v != 0 for v in decoded.values()), 1)

    def test_invalid_priority_and_extension(self):
        for value, reason in [(0, "v_zero"), (5, "write_without_read"),
                              (3 | (1 << 63), "n_disabled"),
                              (3 | (1 << 61), "pbmt_disabled"),
                              (3 | (1 << 59), "rsw60t59b_disabled"),
                              (3 | (1 << 54), "reserved_nonzero")]:
            self.assertEqual(classify_pte(value, 0, CFG)["failure_reason"], reason)
        self.assertEqual(classify_pte(3 | (1 << 60), 0,
                         Config(svrsw60t59b=True, dirty_update=False))["role"], "leaf")

    def test_pointer_leaf_and_superpage(self):
        self.assertEqual(classify_pte(1 | 0xd0, 1, CFG)["role"], "pointer")  # Sail 不拒绝指针 U/A/D
        self.assertEqual(classify_pte(1, 0, CFG)["failure_reason"], "pointer_at_level0")
        self.assertEqual(classify_pte(0x403, 2, CFG)["failure_reason"], "superpage_misaligned")
        for level in range(5):
            self.assertEqual(classify_pte(0x43, level, CFG)["page_size"], 1 << (12+9*level))

    def test_little_endian_and_missing(self):
        mem = memory_bytes(list(reversed(cells(0x1000, 0xfedcba9876543210))))
        self.assertEqual(read_word(mem, 0x1000), 0xfedcba9876543210)
        del mem[0x1003]
        with self.assertRaisesRegex(DecodeError, "missing_memory.*1003"):
            read_word(mem, 0x1000)
        for bad in [cells(0, 0)+cells(0, 0), [{"address": 0, "value": None, "bytes": 1}],
                    [{"address": 0, "value": 256, "bytes": 1}],
                    [{"address": 0, "value": 0, "bytes": 8}],
                    [{"address": 0, "value": 0, "bytes": 1, "extra": 0}]]:
            with self.assertRaises(DecodeError):
                memory_bytes(bad)


class AddressTests(unittest.TestCase):
    def test_load_instruction_signed_offset_and_x0(self):
        s = sample([])
        ins = s["pre_registers"]["$instruction"]["value"]["struct"]
        ins["tuple#%bv12_%bv5_%bv5_%bool_%i640"] = bits(0xff8, 12)
        self.assertEqual(effective_address(s), 0x1ffffff8)
        ins["tuple#%bv12_%bv5_%bv5_%bool_%i641"] = bits(0, 5)
        self.assertEqual(effective_address(s), (1 << 64)-8)

    def test_overrides_and_assembly(self):
        s = sample([])
        del s["pre_registers"]["$instruction"]
        with self.assertRaisesRegex(DecodeError, "--va"):
            effective_address(s)
        self.assertEqual(effective_address(s, va=0x123), 0x123)
        self.assertEqual(effective_address(s, va_register="x1", offset=-16), 0x1ffffff0)
        s["isa_state"]["$instruction"] = "ld x2, -0x8(x1)"
        self.assertEqual(effective_address(s), 0x1ffffff8)

    def test_unknown_instruction_field_rejected(self):
        s = sample([])
        s["pre_registers"]["$instruction"]["value"]["struct"]["new"] = bits(0)
        with self.assertRaises(DecodeError):
            effective_address(s)

    def test_missing_base_and_bad_width_rejected(self):
        s = sample([])
        del s["pre_registers"]["x1"]
        with self.assertRaisesRegex(DecodeError, "x1"):
            effective_address(s)
        s = sample([])
        s["pre_registers"]["$instruction"]["value"]["struct"]["tuple#%bv12_%bv5_%bv5_%bool_%i644"] = {"i64": "4"}
        with self.assertRaises(DecodeError):
            effective_address(s)


class WalkTests(unittest.TestCase):
    def test_three_levels_and_data(self):
        d = decode_sample(sample([(ROOT, (0x80300 << 10) | 1),
                                  (0x80300800, (0x80400 << 10) | 1),
                                  (0x80400000, (0x80500 << 10) | 0x43),
                                  (0x80500000, 0x123)]), CFG)
        self.assertEqual(d["paddr_if_success"], 0x80500000)
        self.assertEqual(d["leaf_level"], 0)
        self.assertEqual([e["role"] for e in d["entries"]], ["pointer", "pointer", "leaf", "data"])

    def test_superpage_pa(self):
        d = decode_sample(sample([(ROOT, (0x80000 << 10) | 0x43), (0xa0000000, 0)]), CFG)
        self.assertEqual((d["page_size"], d["paddr_if_success"]), (1 << 30, 0xa0000000))

    def test_permissions_and_a_bit(self):
        for value, reason in [(0x49, "load_permission"), (0x53, "privilege_permission"), (3, "accessed_update_disabled")]:
            d = decode_sample(sample([(ROOT, value)], "Memory_Exception", "E_Load_Page_Fault"), CFG)
            self.assertEqual(d["failure_reason"], reason)
        s = sample([(ROOT, 0x49), (0x20000000, 0)])
        s["pre_registers"]["mstatus"]["struct"]["bits"] = bits(1 << 19)
        self.assertIsNone(decode_sample(s, CFG)["failure_reason"])

    def test_missing_pte_not_excused_by_exception_alone(self):
        for exception in ["E_Load_Page_Fault", "E_Load_Access_Fault"]:
            with self.assertRaisesRegex(DecodeError, "missing_memory"):
                decode_sample(sample([(ROOT, (0x80300 << 10) | 1)], "Memory_Exception", exception), CFG)

    def test_pma_proves_early_access_fault(self):
        s = sample([(ROOT, (0x10000 << 10) | 1)], "Memory_Exception", "E_Load_Access_Fault")
        s["pre_registers"]["pma_regions"] = {"list": [{"struct": {
            "base": bits(ROOT), "size": bits(0x1000), "include_in_device_tree": {"bool": True},
            "attributes": {"struct": {"readable": {"bool": True}}}}}]}
        d = decode_sample(s, CFG)
        self.assertEqual(d["failure_reason"], "pte_read_pma_access_fault")
        self.assertEqual(d["termination"]["paddr"], 0x10000800)

    def test_result_contradiction_rejected(self):
        with self.assertRaisesRegex(DecodeError, "result_mismatch"):
            decode_sample(sample([(ROOT, 0)]), CFG)

    def test_bare_and_noncanonical(self):
        d = decode_sample(sample([(0x20000000, 1)], mode=0), CFG)
        self.assertEqual(d["paddr_if_success"], 0x20000000)
        s = sample([], "Memory_Exception", "E_Load_Page_Fault", va=1 << 39)
        self.assertEqual(decode_sample(s, CFG)["failure_reason"], "noncanonical_va")

    def test_sum_user_mxr_and_mprv(self):
        s = sample([(ROOT, 0x53), (0x20000000, 0)])
        s["pre_registers"]["mstatus"]["struct"]["bits"] = bits(1 << 18)
        self.assertIsNone(decode_sample(s, CFG)["failure_reason"])
        s["pre_registers"]["cur_privilege"] = {"enum": "User"}
        self.assertIsNone(decode_sample(s, CFG)["failure_reason"])
        s = sample([(ROOT, 0x43)], "Memory_Exception", "E_Load_Page_Fault")
        s["pre_registers"]["cur_privilege"] = {"enum": "User"}
        self.assertEqual(decode_sample(s, CFG)["failure_reason"], "privilege_permission")
        s = sample([(ROOT, 0x43), (0x20000000, 0)])
        s["pre_registers"]["cur_privilege"] = {"enum": "Machine"}
        s["pre_registers"]["mstatus"]["struct"]["bits"] = bits((1 << 17) | (1 << 11))
        self.assertEqual(decode_sample(s, CFG)["effective_privilege"], "Supervisor")

    def test_sv48_sv57_full_walk(self):
        for mode, levels in [(9, 4), (10, 5)]:
            words = []
            for i, level in enumerate(reversed(range(levels))):
                table = ROOT + 0x1000*i
                vpn_i = 256 if level == 1 else 0
                value = (((table+0x1000) >> 12) << 10) | 1 if level else (0x80500 << 10) | 0x43
                words.append((table+vpn_i*8, value))
            words.append((0x80500000, 42))
            d = decode_sample(sample(words, mode=mode), CFG)
            self.assertEqual([e["level"] for e in d["entries"][:-1]], list(reversed(range(levels))))
            self.assertEqual(d["paddr_if_success"], 0x80500000)

    def test_enabled_a_update_requires_post_memory(self):
        s = sample([(ROOT, 3), (0x20000000, 0)])
        cfg = Config(svrsw60t59b=False, dirty_update=True)
        with self.assertRaisesRegex(DecodeError, "missing_memory"):
            decode_sample(s, cfg)
        s["post_memory"] = cells(ROOT, 0x43)
        self.assertIsNone(decode_sample(s, cfg)["failure_reason"])

    def test_extra_memory_rejected(self):
        s = sample([(ROOT, 0), (0x1000, 0)], "Memory_Exception", "E_Load_Page_Fault")
        with self.assertRaisesRegex(DecodeError, "无法归属"):
            decode_sample(s, CFG)


class DistributionTests(unittest.TestCase):
    def test_shape_stability_and_observed_masks(self):
        a = decode_sample(sample([(ROOT, 0)], "Memory_Exception", "E_Load_Page_Fault"), CFG)
        b = decode_sample(sample([(ROOT, 0x100)], "Memory_Exception", "E_Load_Page_Fault"), CFG)
        self.assertEqual(shape_key(a), shape_key(b))
        b["sample_id"] = 7
        shapes = aggregate([a, b])
        self.assertEqual(len(shapes), 1)
        self.assertEqual(shapes[0]["count"], 2)
        entry = shapes[0]["representative"]["entries"][0]
        self.assertEqual(entry["free_mask"], "0x0000000000000100")
        self.assertEqual(entry["fixed_mask"], "0xfffffffffffffeff")
        self.assertEqual(aggregate([b, a]), shapes)

    def test_compare_all_difference_types(self):
        same = compare_distributions({"a": 2}, {"a": 2})
        self.assertTrue(same["equal"])
        diff = compare_distributions({"a": 2, "b": 1}, {"a": 3, "c": 1})
        self.assertFalse(diff["equal"])
        self.assertEqual({d["shape"]: d["delta_merge_minus_fork"] for d in diff["different"]},
                         {"a": 1, "b": -1, "c": 1})

    def test_strict_jsonl_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/"samples.jsonl"
            for content in ["\n", "{bad}\n", json.dumps({"schema_version": 99})+"\n",
                            '{"schema_version":1,"schema_version":1}\n',
                            '{"x":NaN}\n',
                            json.dumps(sample([]))+'\n'+json.dumps(sample([]))+'\n']:
                p.write_text(content)
                with self.assertRaises(DecodeError):
                    list(load_samples(p))
            s = sample([]); s["new_field"] = True
            p.write_text(json.dumps(s)+'\n')
            with self.assertRaises(DecodeError):
                list(load_samples(p))

    def test_output_schema_and_metadata(self):
        from pt_decode import process, write_outputs
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/"samples.jsonl"
            p.write_text(json.dumps(sample([(ROOT, 0)], "Memory_Exception", "E_Load_Page_Fault"))+'\n')
            shapes, metadata = process(p, "fork", CFG, None, None, 0)
            out = Path(tmp)/"out"
            write_outputs(out, shapes, metadata)
            tables = json.loads((out/"page_tables.json").read_text())
            entry = tables["page_tables"][0]["entries"][0]
            self.assertEqual(entry["fixed_mask"], "0xffffffffffffffff")
            self.assertEqual(entry["free_mask"], "0x0000000000000000")
            self.assertEqual(metadata["sample_count"], 1)
            self.assertEqual(len(metadata["sha256"]), 64)
            self.assertTrue((out/"distribution.md").exists())

    def test_unknown_concrete_type_and_invalid_post_memory(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/"samples.jsonl"
            s = sample([])
            s["pre_registers"]["unused"] = {"unknown_type": 0}
            p.write_text(json.dumps(s)+'\n')
            with self.assertRaises(DecodeError):
                list(load_samples(p))
            s = sample([])
            s["post_memory"] = [{"address": 0, "bytes": 1, "value": None}]
            p.write_text(json.dumps(s)+'\n')
            with self.assertRaises(DecodeError):
                list(load_samples(p))

    def test_cli_merge_only_sv48(self):
        from pt_decode import main
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            item = sample([(ROOT, 0)], "Memory_Exception", "E_Load_Page_Fault", mode=9)
            item["mode"] = "merge"
            source = root/"merge.jsonl"
            source.write_text(json.dumps(item)+'\n')
            args = ["--merge-only", "--merge", str(source), "--out", str(root/"out"),
                    "--svrsw60t59b", "disabled", "--dirty-update", "disabled"]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(args), 0)
            report = json.loads((root/"out/page_tables.json").read_text())
            self.assertEqual(report["metadata"]["sample_count"], 1)
            self.assertTrue((root/"out/distribution.md").exists())
            self.assertFalse((root/"out/crosscheck.json").exists())
            self.assertFalse((root/"out/fork").exists())
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main(args+["--fork", str(source)])
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                main([value for value in args if value != "--merge-only"])

    def test_cli_equal_and_different_reports(self):
        from pt_decode import main
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fork = sample([(ROOT, 0)], "Memory_Exception", "E_Load_Page_Fault")
            merge = sample([(ROOT, 0x100)], "Memory_Exception", "E_Load_Page_Fault")
            merge["mode"] = "merge"
            for name, s in [("fork", fork), ("merge", merge)]:
                (root/f'{name}.jsonl').write_text(json.dumps(s)+'\n')
            args = ["--fork", str(root/'fork.jsonl'), "--merge", str(root/'merge.jsonl'),
                    "--out", str(root/'out'), "--svrsw60t59b", "disabled", "--dirty-update", "disabled"]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(args), 0)
            report = json.loads((root/'out/crosscheck.json').read_text())
            self.assertTrue(report["equal"])
            merge["pre_memory"] = cells(ROOT, 5)
            (root/'merge.jsonl').write_text(json.dumps(merge)+'\n')
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main(args), 1)
            report = json.loads((root/'out/crosscheck.json').read_text())
            self.assertFalse(report["equal"])
            self.assertEqual(len(report["different"]), 2)


if __name__ == "__main__":
    unittest.main()
