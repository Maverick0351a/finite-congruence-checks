"""Regressions for lattice validation, search coverage and evidence handling."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import search


class SearchTests(unittest.TestCase):
    def test_invalid_lattice_join_is_rejected(self):
        lattice = copy.deepcopy(search.examples()['B2'])
        lattice['join'][1][2] = 2
        with self.assertRaises(ValueError):
            search.search_size(lattice, 3)

    def test_carrier_bounds_are_explicit(self):
        for size in (0, 5, True, 1.5):
            with self.subTest(size=size), self.assertRaises(ValueError):
                search.search_size(search.examples()['C2'], size)

    def test_incomparable_colors_join_to_top(self):
        lattice = search.examples()['B2']
        self.assertTrue(search.check_witness(lattice, [[0, 1, 2], [1, 0, 3], [2, 3, 0]])['passed'])

    def test_connectivity_is_necessary(self):
        lattice = search.examples()['B2']
        color = [[0, 1, 2, 3], [1, 0, 3, 3], [2, 3, 0, 3], [3, 3, 3, 0]]
        self.assertIsNone(search.structural_failure(lattice, color))
        result = search.check_witness(lattice, color)
        self.assertFalse(result['passed'])
        self.assertEqual(result['failure'], 'seed_connectivity')
        self.assertEqual(result['failing_pair'], (0, 3))

    def test_no_witness_smaller_than_three_for_three_element_chain(self):
        lattice = search.examples()['C3']
        small = search.search_size(lattice, 2)
        self.assertEqual(small['counts']['candidates'], 2)
        self.assertEqual(small['counts'].get('witnesses', 0), 0)
        found = search.search_size(lattice, 3)
        self.assertEqual(found['counts']['candidates'], 8)
        self.assertEqual(found['counts']['witnesses'], 3)
        self.assertEqual(found['vertex_isomorphism_classes'], 1)

    def test_vertex_relabeling_does_not_relabel_lattice_colors(self):
        color = [[0, 1, 2], [1, 0, 2], [2, 2, 0]]
        permuted = [[color[x][y] for y in (2, 0, 1)] for x in (2, 0, 1)]
        changed_color = [[0, 2, 1], [2, 0, 1], [1, 1, 0]]
        self.assertEqual(search.canonical_key(color), search.canonical_key(permuted))
        self.assertNotEqual(search.canonical_key(color), search.canonical_key(changed_color))

    def test_nonzero_bottom_is_supported(self):
        lattice = dict(name='reordered C2', elements=['top', 'bottom'], bottom=1,
                       leq=[[True, False], [True, True]], join=[[0, 0], [0, 1]])
        result = search.search_size(lattice, 2)
        self.assertEqual(result['counts']['witnesses'], 1)
        self.assertEqual(result['representatives'][0]['color'], [[1, 0], [0, 1]])

    def test_manifest_does_not_reuse_a_stale_certificate(self):
        with tempfile.TemporaryDirectory() as folder:
            command = [sys.executable, str(Path(search.__file__)), '--lattice', 'C3', '--out', folder]
            subprocess.run(command + ['--max-vertices', '3'], check=True, capture_output=True)
            self.assertTrue((Path(folder) / 'C3-witness.json').exists())
            subprocess.run(command + ['--max-vertices', '2'], check=True, capture_output=True)
            record = json.loads((Path(folder) / 'search-results.json').read_text())
            self.assertEqual(record['certificates'], [])
            self.assertIsNone(record['lattices']['C3']['minimum_vertices_found'])


if __name__ == '__main__':
    unittest.main()
