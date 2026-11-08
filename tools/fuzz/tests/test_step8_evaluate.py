"""缩小预算时仍按 95:5 选取历史对照，并逐例核对开关不影响对照。"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))


class Step8Tests(unittest.TestCase):
    def test_baseline_selection_keeps_control_fraction(self):
        from step8_evaluate import selected_indices
        self.assertEqual(selected_indices(1000, 500), list(range(475)) + list(range(950, 975)))
        self.assertEqual(selected_indices(500, 500), list(range(500)))
        with self.assertRaises(AssertionError):
            selected_indices(400, 500)

    def test_control_memory_checks_reads_and_allows_unread_initial_values(self):
        import copy
        from types import SimpleNamespace
        from unittest.mock import patch
        import step8_evaluate as evaluation
        original = dict(sample_id=0, pre_registers={}, isa_state={},
                        pre_memory=[dict(address=4096, bytes=1, value=255)])
        for canonical_value, accepted in [(None, True), (255, True), (7, False)]:
            actual = dict(copy.deepcopy(original), class_id=0)
            actual['pre_memory'][0]['value'] = canonical_value
            proof = dict(sample_id=0, sample=copy.deepcopy(actual), guard_unique=True, post_unique=True)
            proof['sample']['class_id'] = None
            judgment = dict(proof, sample=actual)
            streams = {
                'mutations.jsonl': [dict(sample_id=0, operator='M5', actual_identity={})],
                'mutants.jsonl': [original], 'classified.jsonl': [actual],
                'judged.jsonl': [judgment], 'certified.jsonl': [proof],
                'feedback-observations.jsonl': [dict(feature=dict(identity={}, buckets=[]))],
                'findings.jsonl': [],
                'hardware-timing.jsonl': [dict(sample_id=0, emu_seconds=1, known_rule=None)],
            }
            values = {
                'findings-summary.json': dict(infrastructure_failures=0, executed=1),
                'feedback-summary.json': dict(initial=dict(classes=[])),
                'profile.json': {}, 'profile.lock.json': dict(platform_gen_sha256='test'),
                'result.json': dict(prestate_context={}), 'done.json': dict(seconds=1),
                'timing.json': dict(loop_seconds=1), 'remaining-processes.json': [],
            }
            replay = SimpleNamespace(platform_case=lambda *args: dict(prestate_context={}, decoded=dict(entries=[])))
            with self.subTest(canonical_value=canonical_value), \
                 patch.object(evaluation, 'validate', return_value=dict(valid=True)), \
                 patch.object(evaluation, 'lines', side_effect=lambda path: copy.deepcopy(streams[path.name])), \
                 patch.object(evaluation, 'read', side_effect=lambda path: copy.deepcopy(values[path.name])):
                if accepted:
                    row, differences, buckets = evaluation.audit(Path('/test'), 1, None, replay)
                    self.assertEqual(row['canonicalized_control_memory'], [0] if canonical_value is None else [])
                    self.assertEqual(row['agree'], 1)
                else:
                    with self.assertRaises(AssertionError):
                        evaluation.audit(Path('/test'), 1, None, replay)
