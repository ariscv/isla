"""E2 接线必须保留符号前态，并重新生成属于本场景的编码对照。"""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/fuzz'))


class E2CampaignTests(unittest.TestCase):
    def test_four_scenarios_use_e2_templates_and_controls(self):
        import e2_campaign
        experiment = ROOT.parent / 'isla-sym-config/output/fuzz-step6a'
        source = ROOT.parent / 'replay-p0/output/ecfg4b'
        for scene, count in [('sv39-load', 1359), ('sv39-store', 609),
                             ('sv48-load', 2074), ('sv48-store', 958)]:
            with self.subTest(scene=scene), tempfile.TemporaryDirectory() as temporary:
                out = Path(temporary)
                command, corpus, controls = e2_campaign.prepare(
                    ROOT, experiment, source, scene, out, 1, 12)
                self.assertEqual(len(corpus.read_text().splitlines()), count)
                self.assertEqual(command[command.index('-C')+1], str(
                    experiment / ('serial64/E2.toml' if scene == 'sv48-load' else 'E2.toml')))
                self.assertFalse(any(value.startswith(('cur_privilege=', 'mstatus=')) for value in command))
                profile = json.loads((out/'profile.json').read_text())
                self.assertEqual(profile['isla']['scenario']['privilege_domain'], ['User', 'Supervisor'])
                self.assertEqual(profile['csr_init']['entry_mode'], 'mprv')
                rows = [json.loads(line) for line in (out/'control-inputs.jsonl').read_text().splitlines()]
                parents = {row['sample_id']: row for row in map(json.loads, corpus.read_text().splitlines())}
                records = json.loads(controls.read_text())
                self.assertEqual(len(rows), 12)
                self.assertEqual({row['operator'] for row in records}, {'M1', 'M2', 'M5'})
                for row, record in zip(rows, records):
                    self.assertEqual(row['pre_registers'], parents[record['parent_sample_id']]['pre_registers'])
                    self.assertIn(row['pre_registers']['cur_privilege']['enum'], ['User', 'Supervisor'])
                    status = int(row['pre_registers']['mstatus']['struct']['bits']['bits'], 2)
                    self.assertEqual(status & 0xfffffffffff3ffff, 0xa00000000)
                first = [(out/name).read_bytes() for name in ('controls.json', 'control-inputs.jsonl')]
                with tempfile.TemporaryDirectory() as second:
                    e2_campaign.prepare(ROOT, experiment, source, scene, Path(second), 1, 12)
                    self.assertEqual(first, [(Path(second)/name).read_bytes() for name in ('controls.json', 'control-inputs.jsonl')])
