"""用最小路径 JSON 检查逐输入的事件投影。"""

import unittest

from run_scenarios import CheckError, semantic_difference, summarize_paths


def memory_read(data, guard, address="#x10"):
    return guard, {
        "operation": "read", "kind": "()", "address": address, "bytes": 1,
        "data": data, "tag": None, "exclusive": False, "ifetch": False,
        "region": "symbolic",
    }


def path(guard="", memory=(), registers=()):
    memory = list(memory)
    return {
        "guard_smtlib": "(declare-const x (_ BitVec 1))\n"
                        "(declare-const byte (_ BitVec 8))\n"
                        "(declare-const free Bool)\n" + guard,
        "return_value": "true",
        "register_values": {"path_x": "x", "out_value": "x"},
        "memory_events": [event for _, event in memory],
        "memory_event_guards": [guard for guard, _ in memory],
        "register_reads": list(registers),
    }


class ProjectEvents(unittest.TestCase):
    scene = {
        "inputs": {"path_x": 1}, "observe": "out_value", "registers": [],
        "ordered_events": False, "ordered_memory_events": True, "register_reads": {},
    }
    selected = "(= x #b1)"
    bound = "(assert (=> (= x #b1) (= byte #x2a)))"
    baseline = [
        path("(assert (= x #b0))"),
        path("(assert (= x #b1))", [memory_read("#x2a", "true")]),
    ]

    def summarize(self, paths, **overrides):
        return summarize_paths(paths, {**self.scene, **overrides}, 30)[0]

    def test_inactive_memory_value_may_be_unconstrained(self):
        merged = path(self.bound, [memory_read("byte", self.selected)])
        self.assertIsNone(semantic_difference(self.summarize(self.baseline), self.summarize([merged])))

    def test_wrong_read_guard_changes_the_observed_input(self):
        merged = path(self.bound, [memory_read("byte", "false")])
        difference = semantic_difference(self.summarize(self.baseline), self.summarize([merged]))
        self.assertIn("输入 (1,)", difference)

    def test_input_must_determine_the_read_guard(self):
        merged = path("", [memory_read("#x2a", "free")])
        with self.assertRaisesRegex(CheckError, "唯一"):
            self.summarize([merged])

    def test_memory_order_follows_scene(self):
        reads = [memory_read("#x2a", "true"), memory_read("#x7f", "true", "#x20")]
        left, right = [path(memory=reads)], [path(memory=reversed(reads))]
        self.assertIsNotNone(semantic_difference(self.summarize(left), self.summarize(right)))
        self.assertIsNone(semantic_difference(self.summarize(left, ordered_memory_events=False),
                                              self.summarize(right, ordered_memory_events=False)))

    def test_register_read_count_is_checked_for_each_input_in_each_group(self):
        read = {"register": "R", "accessors": [], "data": "x", "guard_smtlib": "true"}
        groups = [path(f"(assert (= x #b{i}))", registers=[read]) for i in (0, 1)]
        self.summarize(groups, register_reads={"R": 1})
        groups[1]["register_reads"] = [{**read, "guard_smtlib": "(= x #b0)"}]
        with self.assertRaisesRegex(CheckError, r"输入 \(1,\).*R.*实际 0"):
            self.summarize(groups, register_reads={"R": 1})


if __name__ == "__main__":
    unittest.main()
