"""Data binding controls for the separate saved-N5 reading guide."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from build_n5_context import ROOT, PINNED_SOURCES, build, failure


class ContextTests(unittest.TestCase):
    def test_complete_partition_list_and_explanation_counterexample(self):
        record = build()
        self.assertEqual(len(record['partition_audit']), 15)
        self.assertEqual(sum(p['valid'] for p in record['partition_audit']), 5)
        ops = record['claims'][0]['values']['operations']
        self.assertEqual(failure([0, 1, 2, 2], ops),
                         {'operation': 1, 'pair': [2, 3], 'outputs': [0, 1]})
        for p in record['partition_audit']:
            v = p['violation']
            if v:
                x, y = v['pair']
                a, b = v['outputs']
                self.assertEqual(p['partition'][x], p['partition'][y])
                self.assertNotEqual(p['partition'][a], p['partition'][b])

    def test_citations_resolve_to_existing_objects(self):
        record = build()
        refs = record['sources'] + record['claims'][0]['citations'] + record['atlas_relation']['citations']
        for ref in refs:
            if 'path' not in ref:
                continue
            p = ROOT / ref['path']
            self.assertTrue(p.is_file())
            if 'json_pointer' in ref:
                obj = json.loads(p.read_text(encoding='utf-8'))
                for key in ref['json_pointer'].lstrip('/').split('/'):
                    obj = obj[int(key)] if isinstance(obj, list) else obj[key]
                self.assertIsNotNone(obj)
            if 'line' in ref:
                self.assertLessEqual(ref['line'], len(p.read_text(encoding='utf-8').splitlines()))

    def test_shape_correspondence_does_not_transfer_proof(self):
        r = build()['atlas_relation']
        self.assertFalse(r['same_operation_set'])
        self.assertFalse(r['formal_proof_transferred'])
        self.assertNotEqual(sorted(r['transformed_saved_operations']), sorted(r['atlas_operations']))

    def test_changed_data_or_proof_rejected(self):
        paths = PINNED_SOURCES
        for changed, replacement, message in [
            ('lean/FiniteCongruenceChecks.lean', 'changed proof', 'pinned source mismatch'),
            ('evidence/N5-witness.json', '{}', 'pinned source mismatch'),
            ('lean/comparator/evidence/receipt.json', '{"passed": false}', 'pinned source mismatch'),
            ('lean/evidence/bridge-run/result.json', '{"passed": false}', 'pinned source mismatch'),
        ]:
            with self.subTest(changed=changed), tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                for path in paths:
                    (root / path).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / path, root / path)
                (root / changed).write_text(replacement, encoding='utf-8')
                with self.assertRaisesRegex(ValueError, message):
                    build(root)

    def test_failed_comparator_results_rejected(self):
        from unittest.mock import patch
        original = Path.read_text
        def altered(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if path == ROOT / 'lean/comparator/evidence/receipt.json':
                obj = json.loads(text)
                obj['checks'][0]['exit_code'] = 1
                return json.dumps(obj)
            return text
        with patch.object(Path, 'read_text', altered), self.assertRaisesRegex(ValueError, 'comparator control'):
            build()

    def test_changed_atlas_family_rejected(self):
        # In-memory replacement keeps the real saved files and frozen data untouched.
        from unittest.mock import patch
        original = Path.read_text
        def altered(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if path == ROOT / 'space/atlas-data.json':
                obj = json.loads(text)
                next(e for e in obj['entries'] if e['id'] == 'n4-E16709')['partitions'].pop()
                return json.dumps(obj)
            return text
        with patch.object(Path, 'read_text', altered), self.assertRaisesRegex(ValueError, 'family correspondence'):
            build()


if __name__ == '__main__':
    unittest.main()
