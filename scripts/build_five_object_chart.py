"""Render a deterministic documentation diagram from the audited finite record.

This SVG illustrates the inclusion-order isomorphism. It is not proof evidence.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from html import escape
from pathlib import Path
import sys

import check_five_object as audit

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = "docs/assets/five-object-order.svg"


def covers(order):
    """Recover immediate strict inclusions from the full audited order."""
    size = len(order)
    return [(i, j) for i in range(size) for j in range(size)
            if i != j and order[i][j]
            and not any(k != i and k != j and order[i][k] and order[k][j] for k in range(size))]


def render(root=ROOT):
    record = audit.replay(root=Path(root))
    first, second = (record["constructions"][name] for name in ("A", "B"))
    order = first["order"]
    mapping = record["checks"]["order_isomorphism_A_to_B"]
    edges = covers(order)
    audit.require(edges == [tuple(edge) for edge in first["covers"]], "Audited cover list disagrees with full order")
    audit.require({(mapping[i], mapping[j]) for i, j in edges} == set(covers(second["order"])),
                  "Paired grouping labels do not preserve the covers")

    @lru_cache(maxsize=None)
    def level(i):
        below = [j for j in range(8) if j != i and order[j][i]]
        return 0 if not below else 1 + max(level(j) for j in below)

    levels = {i: level(i) for i in range(8)}
    audit.require(max(levels.values()) == 4, "Diagram expects a five-node maximal chain")
    # Horizontal slots are presentation choices; height comes from the order.
    horizontal_order = (7, 6, 2, 5, 4, 1, 3, 0)
    positions = {}
    for rank in range(5):
        row = [i for i in horizontal_order if levels[i] == rank]
        xs = {1: [420], 2: [310, 640], 3: [200, 420, 640]}[len(row)]
        for i, x in zip(row, xs):
            positions[i] = (x, 704 - 110 * rank)

    title = "One inclusion order. Two rule costs."
    description = (
        "Eight valid groupings in each of two five-object constructions have isomorphic inclusion orders. "
        "Construction A needs exactly three unary rules for its exact relation family; construction B needs exactly two. "
        "The bottom is the grouping with all objects separate and the top puts all objects together. "
        "Each node pairs A's grouping index with B's corresponding index and shows both block-label strings. "
        "This is an illustration of checked records, not a proof or an object-relabeling claim."
    )
    lines = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="840" height="932" viewBox="0 0 840 932" role="img" aria-labelledby="title description">',
        f'  <title id="title">{escape(title)}</title>',
        f'  <desc id="description">{escape(description)}</desc>',
        '  <style>',
        '    text{font-family:Inter,"Segoe UI",Arial,sans-serif;fill:#162442}',
        '    .muted{fill:#53647e}.mono{font-family:"Cascadia Code",Consolas,monospace}',
        '    .edge{stroke:#8493ab;stroke-width:2.3;fill:none}',
        '    .node{fill:#fff;stroke:#9aaec8;stroke-width:1.6}',
        '  </style>',
        '  <rect width="840" height="932" rx="20" fill="#f2f5fc"/>',
        '  <text x="44" y="41" font-size="12" font-weight="700" letter-spacing="1.8" class="muted">FIVE-OBJECT COMPARISON</text>',
        f'  <text x="44" y="82" font-size="30" font-weight="700">{escape(title)}</text>',
        '  <text x="44" y="112" font-size="17" class="muted">The same arrangement of valid groupings can require different rules.</text>',
        '  <rect x="44" y="137" width="364" height="68" rx="10" fill="#e7f6f3" stroke="#a4d6cf"/>',
        '  <rect x="432" y="137" width="364" height="68" rx="10" fill="#eee8fa" stroke="#cabce4"/>',
        f'  <text x="63" y="165" font-size="18" font-weight="700">A: exactly {first["minimum_unary_operations"]} rules minimum</text>',
        '  <text x="63" y="189" font-size="14" class="muted">For A\u2019s exact eight grouping relations</text>',
        f'  <text x="451" y="165" font-size="18" font-weight="700">B: exactly {second["minimum_unary_operations"]} rules minimum</text>',
        '  <text x="451" y="189" font-size="14" class="muted">For B\u2019s exact eight grouping relations</text>',
        '  <text x="420" y="224" text-anchor="middle" font-size="14" class="muted">All together</text>',
        '  <path d="M 65 647 V 311 M 59 319 L 65 311 L 71 319" stroke="#53647e" stroke-width="1.7" fill="none"/>',
        '  <text x="51" y="485" transform="rotate(-90 51 485)" text-anchor="middle" font-size="13" class="muted">Moving up merges groups</text>',
        '  <g aria-label="Immediate inclusion edges">',
    ]
    for i, j in edges:
        x1, y1 = positions[i]
        x2, y2 = positions[j]
        lines.append(f'    <path class="edge" d="M {x1} {y1 - 34} L {x2} {y2 + 34}"><title>A{i} / B{mapping[i]} is immediately finer than A{j} / B{mapping[j]}</title></path>')
    lines.extend(['  </g>', '  <g aria-label="Paired grouping nodes">'])
    for i in range(8):
        x, y = positions[i]
        j = mapping[i]
        labels_a = "".join(map(str, first["groupings"][i]))
        labels_b = "".join(map(str, second["groupings"][j]))
        lines.extend([
            f'    <g id="grouping-{i}" aria-label="A{i}: {labels_a}; corresponding B{j}: {labels_b}">',
            f'      <rect class="node" x="{x - 89}" y="{y - 34}" width="178" height="68" rx="11"/>',
            f'      <text x="{x}" y="{y - 5}" text-anchor="middle" font-size="21" font-weight="650">A{i} \u2194 B{j}</text>',
            f'      <text x="{x}" y="{y + 20}" text-anchor="middle" font-size="14" class="mono muted">{labels_a} \u2194 {labels_b}</text>',
            '    </g>',
        ])
    lines.extend([
        '  </g>',
        '  <text x="420" y="762" text-anchor="middle" font-size="14" class="muted">All separate</text>',
        '  <path d="M 44 788 H 796" stroke="#d4ddeb"/>',
        '  <text x="44" y="815" font-size="15">Each node pairs corresponding groupings; lines show immediate inclusion.</text>',
        '  <text x="44" y="840" font-size="15">Equal digits mean the same group: 00100 = {0,1,3,4} | {2}.</text>',
        '  <text x="44" y="865" font-size="15">The correspondence concerns grouping order, not a renaming of objects.</text>',
        '  <text x="44" y="900" font-size="13" class="muted">Fixed five-object carrier \u00b7 unary rules \u00b7 exact families</text>',
        '  <text x="44" y="919" font-size="12" class="muted">Documentation illustration from computational.json; the formal proof is linked separately.</text>',
        '</svg>',
    ])
    return ("\n".join(lines) + "\n").encode("utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare saved SVG bytes with regenerated output")
    args = parser.parse_args(argv)
    try:
        expected = render()
        output = ROOT / OUTPUT
        if args.check:
            audit.require(output.read_bytes() == expected, "Five-object SVG is stale; run scripts/build_five_object_chart.py")
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(expected)
        print("Five-object order illustration: " + ("checked" if args.check else "generated"))
        return 0
    except (ValueError, OSError, KeyError) as error:
        print("five-object chart failed: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
