"""Bounded exhaustive search for finite lattice colored-graph witnesses.

Standard-library Python, based on the IsGraphWitness predicate in openai/math.
No Lean compilation or claim of mathematical novelty is made by this program.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys
import time

SOURCE = {
    'repository': 'https://github.com/openai/math',
    'revision': '1581d4cbdd69a0faf34b2089614fe2a814316a6a',
    'path': 'lean/ComparatorChallenges/FiniteCongruenceGraph.lean',
    'sha256': '2ee495def2e1228bf13df520f6c66699ec22b2cd3bc1ae7383a30957aae9f967',
}


def _require(condition):
    """Keep evidence controls active even with python -O."""
    if not condition:
        raise AssertionError("self-check or enumeration invariant failed")


def validate_lattice(lattice):
    labels, bottom, leq, join = (lattice[k] for k in ('elements', 'bottom', 'leq', 'join'))
    size = len(labels)
    if not isinstance(labels, list) or not size or any(not isinstance(label, str) for label in labels) or len(set(labels)) != size:
        raise ValueError('elements must be distinct nonempty-list string labels')
    if type(bottom) is not int or not 0 <= bottom < size:
        raise ValueError('bottom index is invalid')
    if len(leq) != size or any(len(row) != size for row in leq):
        raise ValueError('order table must be square')
    if any(type(x) is not bool for row in leq for x in row):
        raise ValueError('order entries must be booleans')
    if len(join) != size or any(len(row) != size for row in join):
        raise ValueError('join table must be square')
    if any(type(x) is not int or not 0 <= x < size for row in join for x in row):
        raise ValueError('join entries must be valid indices')
    if not all(leq[x][x] and leq[bottom][x] for x in range(size)):
        raise ValueError('order is not reflexive or bottom is incorrect')
    if any(x != y and leq[x][y] and leq[y][x] for x, y in product(range(size), repeat=2)):
        raise ValueError('order is not antisymmetric')
    if any(leq[x][y] and leq[y][z] and not leq[x][z] for x, y, z in product(range(size), repeat=3)):
        raise ValueError('order is not transitive')
    for x, y in product(range(size), repeat=2):
        upper = [z for z in range(size) if leq[x][z] and leq[y][z]]
        least = [z for z in upper if all(leq[z][u] for u in upper)]
        lower = [z for z in range(size) if leq[z][x] and leq[z][y]]
        greatest = [z for z in lower if all(leq[u][z] for u in lower)]
        if least != [join[x][y]] or len(greatest) != 1:
            raise ValueError('join table is not the least-upper-bound table, or meet is missing')


def lattice_from_covers(name, elements, covers):
    size = len(elements)
    leq = [[x == y for y in range(size)] for x in range(size)]
    for x, y in covers:
        leq[x][y] = True
    for k, x, y in product(range(size), repeat=3):
        leq[x][y] |= leq[x][k] and leq[k][y]
    join = [[next(z for z in range(size)
                  if leq[x][z] and leq[y][z]
                  and all(leq[z][u] for u in range(size) if leq[x][u] and leq[y][u]))
             for y in range(size)] for x in range(size)]
    lattice = dict(name=name, elements=elements, bottom=0, leq=leq, join=join)
    validate_lattice(lattice)
    return lattice


def examples():
    lattices = [lattice_from_covers(f'C{k}', [str(x) for x in range(k)],
                                    [(x, x + 1) for x in range(k - 1)]) for k in (2, 3, 4)]
    lattices += [
        lattice_from_covers('B2', ['0', 'a', 'b', '1'], [(0, 1), (0, 2), (1, 3), (2, 3)]),
        lattice_from_covers('M3', ['0', 'a', 'b', 'c', '1'],
                            [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)]),
        lattice_from_covers('N5', ['0', 'a', 'b', 'c', '1'],
                            [(0, 1), (1, 2), (2, 4), (0, 3), (3, 4)]),
        lattice_from_covers('M4', ['0', 'a', 'b', 'c', 'd', '1'],
                            [(0, x) for x in range(1, 5)] + [(x, 5) for x in range(1, 5)]),
        lattice_from_covers('B3', [str(x) for x in range(8)],
                            [(x, x | (1 << bit)) for x in range(8) for bit in range(3)
                             if not x & (1 << bit)]),
    ]
    return {lattice['name']: lattice for lattice in lattices}


def validate_color(lattice, color):
    size, levels = len(color), len(lattice['elements'])
    if not size or any(len(row) != size for row in color):
        raise ValueError('color must be a nonempty square matrix')
    if any(type(x) is not int or not 0 <= x < levels for row in color for x in row):
        raise ValueError('colors must be valid lattice indices')


def structural_failure(lattice, color):
    n, size = len(color), len(lattice['elements'])
    leq, join, bottom = lattice['leq'], lattice['join'], lattice['bottom']
    if any(color[x][y] != color[y][x] for x, y in product(range(n), repeat=2)):
        return 'symmetry'
    if any((color[x][y] == bottom) != (x == y) for x, y in product(range(n), repeat=2)):
        return 'bottom_iff_diagonal'
    if any(not leq[color[x][y]][join[color[x][z]][color[z][y]]]
           for x, y, z in product(range(n), repeat=3)):
        return 'triangle'
    present = set(x for row in color for x in row)
    if any(not leq[a][b] and not any(leq[c][a] and not leq[c][b] for c in present)
           for a, b in product(range(size), repeat=2)):
        return 'order_separation'
    return None


def connectivity(lattice, color):
    """Exact unordered-seed reduction, used only after the structural checks.

    Reversing an edge leaves equivalence closure unchanged, as do diagonal
    loops. Symmetry preserves seed colors on reversal; loops add only bottom.
    A nonempty seed set consisting only of loops has bottom bound and its
    target pairs are reflexive by bottom_iff_diagonal. See METHOD.md.
    """
    n = len(color)
    leq, join = lattice['leq'], lattice['join']
    edges = list(combinations(range(n), 2))
    bit_of = {edge: 1 << i for i, edge in enumerate(edges)}
    placements = [p for p in product(range(n), repeat=n)
                  if all(leq[color[p[x]][p[y]]][color[x][y]] for x, y in edges)]
    images = []
    for x, y in edges:
        mask = 0
        for placement in placements:
            a, b = sorted((placement[x], placement[y]))
            if a != b:
                mask |= bit_of[a, b]
        images.append(mask)
    target = [sum(1 << i for i, (x, y) in enumerate(edges) if leq[color[x][y]][bound])
              for bound in range(len(leq))]
    count = 1 << len(edges)
    marked, bounds = [0] * count, [lattice['bottom']] * count
    closures = {}
    for mask in range(1, count):
        low = mask & -mask
        bit, previous = low.bit_length() - 1, mask ^ low
        marked[mask] = marked[previous] | images[bit]
        x, y = edges[bit]
        bounds[mask] = join[bounds[previous]][color[x][y]]
        relation = marked[mask]
        if relation not in closures:
            parent = list(range(n))

            def find(x):
                while parent[x] != x:
                    parent[x] = parent[parent[x]]
                    x = parent[x]
                return x

            for i, (a, b) in enumerate(edges):
                if relation & (1 << i):
                    parent[find(a)] = find(b)
            closures[relation] = sum(1 << i for i, (a, b) in enumerate(edges) if find(a) == find(b))
        missing = target[bounds[mask]] & ~closures[relation]
        if missing:
            failed_edge = edges[(missing & -missing).bit_length() - 1]
            return dict(passed=False, admissible_maps=len(placements), seed_classes_checked=mask,
                        failing_seeds=[edge for i, edge in enumerate(edges) if mask & (1 << i)],
                        failing_pair=failed_edge, bound=bounds[mask])
    return dict(passed=True, admissible_maps=len(placements), seed_classes_checked=count - 1)


def check_witness(lattice, color):
    validate_lattice(lattice)
    validate_color(lattice, color)
    failure = structural_failure(lattice, color)
    if failure:
        return dict(passed=False, failure=failure)
    result = connectivity(lattice, color)
    if not result['passed']:
        result['failure'] = 'seed_connectivity'
    return result


def canonical_key(color):
    n = len(color)
    return min(tuple(color[p[x]][p[y]] for x, y in combinations(range(n), 2))
               for p in permutations(range(n)))


def make_color(n, bottom, values):
    color = [[bottom] * n for _ in range(n)]
    for (x, y), value in zip(combinations(range(n), 2), values):
        color[x][y] = color[y][x] = value
    return color


def search_size(lattice, n):
    validate_lattice(lattice)
    if type(n) is not int or not 1 <= n <= 4:
        raise ValueError('this exhaustive search supports carrier sizes 1 through 4')
    started = time.perf_counter()
    palette = [x for x in range(len(lattice['elements'])) if x != lattice['bottom']]
    counts, classes = Counter(), Counter()
    first_connectivity_failure = None
    for values in product(palette, repeat=n * (n - 1) // 2):
        counts['candidates'] += 1
        color = make_color(n, lattice['bottom'], values)
        failure = structural_failure(lattice, color)
        if failure:
            counts[failure] += 1
            continue
        counts['structurally_valid'] += 1
        result = connectivity(lattice, color)
        if not result['passed']:
            counts['seed_connectivity'] += 1
            if first_connectivity_failure is None:
                first_connectivity_failure = dict(color=color, result=result)
            continue
        counts['witnesses'] += 1
        classes[canonical_key(color)] += 1
    representatives = [dict(color=make_color(n, lattice['bottom'], key), labeled_count=multiplicity)
                       for key, multiplicity in sorted(classes.items())]
    return dict(vertices=n, complete=True, expected_candidates=len(palette) ** (n * (n - 1) // 2),
                counts=dict(counts), vertex_isomorphism_classes=len(classes),
                representatives=representatives, first_connectivity_failure=first_connectivity_failure,
                seconds=round(time.perf_counter() - started, 6))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-vertices', type=int, choices=range(1, 5), default=4)
    parser.add_argument('--lattice', choices=list(examples()), action='append')
    parser.add_argument('--out', type=Path, default=Path('runs/search'))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    lattices = examples()
    selected = list(dict.fromkeys(args.lattice or list(lattices)))
    output = dict(generated_utc=datetime.now(timezone.utc).isoformat(), source=SOURCE,
                  python=sys.version, max_vertices=args.max_vertices,
                  search='Every labeled symmetric coloring, bottom iff diagonal; all selected sizes exhausted.',
                  isomorphism='Vertex relabeling only; lattice colors are fixed.',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  certificates=[], lattices={})
    for name in selected:
        lattice = lattices[name]
        rows = []
        for n in range(1, args.max_vertices + 1):
            row = search_size(lattice, n)
            _require(row['counts']['candidates'] == row['expected_candidates'])
            rows.append(row)
            print(f'{name} n={n}: {row["counts"].get("witnesses", 0)}/{row["expected_candidates"]} witnesses, '
                  f'{row["vertex_isomorphism_classes"]} vertex-isomorphism classes', flush=True)
        first = next((row for row in rows if row['representatives']), None)
        output['lattices'][name] = dict(lattice=lattice, sizes=rows,
                                        minimum_vertices_found=first['vertices'] if first else None,
                                        smaller_sizes_exhausted=bool(first))
        if first:
            certificate = dict(schema_version=1, source=SOURCE, lattice=lattice,
                               color=first['representatives'][0]['color'],
                               primary_check=check_witness(lattice, first['representatives'][0]['color']))
            path = args.out / f'{name}-witness.json'
            path.write_text(json.dumps(certificate, indent=2) + '\n', encoding='utf-8', newline='\n')
            output['certificates'].append(dict(path=path.name,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    (args.out / 'search-results.json').write_text(json.dumps(output, indent=2) + '\n', encoding='utf-8', newline='\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
