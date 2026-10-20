"""Independent reconstruction of the exact 728-card Snaky certificate.

This evaluator uses an explicit syntax tree, eight integer matrices, and literal
finite sets. It imports neither the upstream evaluator nor Lean-generated data.
It checks finite certificate arithmetic, not the game-strategy theorem.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import reduce
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
INPUT = "evidence/snaky-finite-v1/certificate.txt"
OUTPUT = "evidence/snaky-finite-v1/computational.json"
SOURCE = "scripts/check_snaky.py"
CLAIM_ID = "context:family-187:snaky:finite-board-21:v1"
HASH_ENCODING = "SHA-256 of UTF-8 file bytes with CRLF normalized to LF; no other byte changes."
UPSTREAM_COMMIT = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
UPSTREAM_PATH = "preprints/Snaky-in-21-Maker-moves-September-25-2026/verification/certificate.txt"
CERTIFICATE_SHA256 = "3fa12d36a6d4dbb185e3f2808c8dfde13d85ee309afbca030d6ad17ae9fe3d04"
ALPHABET = "0123456789ABCDEFG"
SNAKY = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
# Rows (a,b,c,d) mean (x,y) -> (a*x+b*y,c*x+d*y).
MATRICES = ((1, 0, 0, 1), (0, 1, 1, 0), (-1, 0, 0, 1),
            (0, 1, -1, 0), (1, 0, 0, -1), (0, -1, 1, 0),
            (-1, 0, 0, -1), (0, -1, -1, 0))
Point = tuple[int, int]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf-8")


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=_unique_object)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def raw_digest(payload):
    return hashlib.sha256(payload).hexdigest()


def points_json(points):
    return [list(p) for p in sorted(points)]


def point_digest(points):
    return raw_digest(encode(points_json(points)))


@dataclass(frozen=True)
class Reference:
    index: int
    symmetry: int = 0
    translation: Point = (0, 0)


@dataclass(frozen=True)
class Combination:
    pivot: Point
    children: tuple[Reference | Combination, ...]


@dataclass(frozen=True)
class Card:
    required: frozenset[Point]
    support: frozenset[Point]
    height: int


def parse_point(word):
    require(len(word) == 2 and all(c in ALPHABET for c in word),
            "Invalid encoded point: " + word)
    return tuple(ALPHABET.index(c) for c in word)


def parse_reference(word, earlier_count):
    require(re.fullmatch(r"(?:0|[1-9][0-9]*)(?::[0-7][0-9A-G]{2})?", word) is not None,
            "Invalid reference: " + word)
    pieces = word.split(":")
    index = int(pieces[0])
    require(index < earlier_count, "Reference must name an earlier card: " + word)
    if len(pieces) == 1:
        return Reference(index)
    return Reference(index, int(pieces[1][0]), parse_point(pieces[1][1:]))


def parse_line(line, expected_index):
    """Parse before evaluating; every nested reference shares the line's bound."""
    words = re.findall(r"[()]|[^\s()]+", line)
    require(len(words) >= 3, "A card needs an index, pivot, and nonempty child list")
    require(words[0] == str(expected_index), "Unexpected card number: " + words[0])
    cursor = 1

    def combine(nested, depth):
        nonlocal cursor
        require(depth <= 128, "Expression nesting exceeds the parser limit")
        require(cursor < len(words), "Missing pivot")
        pivot = parse_point(words[cursor])
        cursor += 1
        children = []
        while cursor < len(words) and words[cursor] != ")":
            word = words[cursor]
            cursor += 1
            if word == "(":
                children.append(combine(True, depth + 1))
            else:
                children.append(parse_reference(word, expected_index))
        require(bool(children), "A combination needs at least one child")
        if nested:
            require(cursor < len(words) and words[cursor] == ")", "Unclosed expression")
            cursor += 1
        return Combination(pivot, tuple(children))

    expression = combine(False, 0)
    require(cursor == len(words), "Unexpected closing parenthesis or trailing tokens")
    return expression


def transform(points, symmetry, translation):
    require(type(symmetry) is int and 0 <= symmetry < 8, "Invalid symmetry index")
    require(len(translation) == 2 and all(type(c) is int for c in translation),
            "Translation must be two integers")
    a, b, c, d = MATRICES[symmetry]
    dx, dy = translation
    require(abs(a * d - b * c) == 1, "Placement matrix must be invertible")
    return frozenset((a*x + b*y + dx, c*x + d*y + dy) for x, y in points)


def place(card, reference):
    placed = Card(transform(card.required, reference.symmetry, reference.translation),
                  transform(card.support, reference.symmetry, reference.translation), card.height)
    require(len(placed.required) == len(card.required) and len(placed.support) == len(card.support),
            "Placement must preserve cardinalities")
    return placed


def combine_cards(pivot, children):
    require(bool(children), "A combination needs at least one child")
    require(all(type(c.height) is int and c.height >= 1 for c in children), "Child height must be a positive integer")
    require(all(c.required <= c.support for c in children), "Child requirements leave its support")
    common = reduce(frozenset.intersection, (c.support for c in children))
    requirements = frozenset().union(*(c.required for c in children))
    required = (requirements | common) - {pivot}
    support = frozenset({pivot}).union(*(c.support for c in children))
    result = Card(required, support, 1 + max(c.height for c in children))
    # These are the local hypotheses used by the separate game proof.
    require(result.required <= result.support, "Parent requirements leave its support")
    require(pivot in result.support, "Pivot leaves parent support")
    require(all(c.support <= result.support for c in children), "Child support leaves parent support")
    require(all(c.required <= result.required | {pivot} for c in children), "Unprepared child requirement")
    require(common <= result.required | {pivot}, "Common support is not prepared by the pivot")
    require(all(c.height < result.height for c in children), "Child height must decrease")
    return result


def evaluate(expression, earlier_cards, counters=None, depth=0):
    if isinstance(expression, Reference):
        if counters is not None:
            counters["reference_nodes"] += 1
        return place(earlier_cards[expression.index], expression)
    if counters is not None:
        counters["combination_nodes"] += 1
        counters["maximum_inline_depth"] = max(counters["maximum_inline_depth"], depth)
    children = [evaluate(c, earlier_cards, counters, depth + 1) for c in expression.children]
    return combine_cards(expression.pivot, children)


def reconstruct(payload):
    require(isinstance(payload, bytes), "Certificate input must be bytes")
    try:
        source = payload.decode("ascii")
    except UnicodeDecodeError as exc:
        raise ValueError("Certificate must be ASCII") from exc
    lines = source.splitlines()
    require(bool(lines) and all(line.strip() for line in lines), "Empty certificate or blank data line")
    target = frozenset(SNAKY)
    cards = [Card(target - {point}, target, 1) for point in SNAKY]
    expressions = []
    counters = {"combination_nodes": 0, "reference_nodes": 0, "maximum_inline_depth": 0}
    for index, line in enumerate(lines, start=6):
        expression = parse_line(line, index)
        cards.append(evaluate(expression, cards, counters))
        expressions.append(expression)
    return tuple(cards), tuple(expressions), counters


def validate_endpoint(cards, expressions, *, board_bounds=(0, 16, 0, 16), move_bound=21):
    require(len(board_bounds) == 4 and all(type(c) is int for c in board_bounds)
            and board_bounds == (0, 16, 0, 16), "This claim is bound to the exact 17 by 17 square")
    require(type(move_bound) is int and move_bound == 21, "This claim is bound to 21 Maker moves")
    require(len(cards) == 728 and len(expressions) == 722, "Expected 728 cards including six bases")
    final = cards[-1]
    require(expressions[-1].pivot == (8, 8), "Final pivot must be (8,8)")
    require(not final.required, "Final required set must be empty")
    require(len(final.support) == 251, "Final support must contain exactly 251 cells")
    require(final.height == 21 and max(c.height for c in cards) == 21, "Incorrect certificate height")
    require(all(0 <= x <= 16 and 0 <= y <= 16 for x, y in final.support), "Final support leaves the board")
    # Occupancy is a finite arithmetic bound; the separate Lean proof supplies
    # its connection to legal alternating play and actual Maker claims.
    require(2 * (move_bound - 1) == 40 < len(final.support), "Insufficient room for replacement moves")


def audit(root=ROOT):
    root = Path(root)
    payload = (root / INPUT).read_bytes()
    require(raw_digest(payload) == CERTIFICATE_SHA256, "Pinned certificate raw-byte SHA256 mismatch")
    cards, expressions, counters = reconstruct(payload)
    validate_endpoint(cards, expressions)
    final = cards[-1]
    top = expressions[-1]
    require(len(top.children) == 32 and all(isinstance(c, Reference) for c in top.children),
            "Expected the final 32 placed references")
    child_records = []
    common = final.support
    for number, reference in enumerate(top.children):
        child = evaluate(reference, cards[:727])
        require(child.required == {(8, 8)}, "Final child requirement must be the pivot")
        common &= child.support
        child_records.append({"position": number, "card": reference.index,
                              "symmetry": reference.symmetry, "translation": list(reference.translation),
                              "height": child.height, "required": points_json(child.required),
                              "support_count": len(child.support), "support_sha256": point_digest(child.support),
                              "common_cells_other_than_pivot": len(common - {(8, 8)})})
    require(common == {(8, 8)}, "Final child intersection must be the singleton pivot")
    group_sizes = (4, 4, 8, 4, 8, 4)
    ends = []
    offset = 0
    for size in group_sizes:
        offset += size
        record = child_records[offset - 1]
        ends.append({"card": record["card"], "placements": size,
                     "remaining_cells_other_than_pivot": record["common_cells_other_than_pivot"]})
    require([r["card"] for r in ends] == [648, 708, 712, 713, 725, 726], "Unexpected final child groups")
    require([r["remaining_cells_other_than_pivot"] for r in ends] == [35, 31, 21, 12, 4, 0],
            "Unexpected successive final intersections")
    return {
        "schema_version": 1, "id": CLAIM_ID, "kind": "independent_finite_certificate_audit", "status": "PASS",
        "upstream": {"repository": "openai/math", "commit": UPSTREAM_COMMIT, "path": UPSTREAM_PATH,
                     "url": f"https://github.com/openai/math/blob/{UPSTREAM_COMMIT}/{UPSTREAM_PATH}",
                     "certificate_sha256": raw_digest(payload), "byte_length": len(payload),
                     "hash_encoding": "SHA-256 of exact original certificate bytes; no newline normalization."},
        "checker": {"path": SOURCE, "sha256": digest(root / SOURCE), "hash_encoding": HASH_ENCODING},
        "counts": {"numbered_cards": len(cards), "explicit_lines": len(expressions), "base_cards": 6,
                   "maximum_height": max(c.height for c in cards), **counters},
        "checked_local_obligations": ["Backward references and nonempty child lists at every expression",
                                      "All eight placements are invertible signed coordinate permutations",
                                      "Every requirement lies in its support",
                                      "Every child support and pivot lies in its parent support",
                                      "Child requirements and common support lie in parent requirements plus pivot",
                                      "Height strictly decreases when passing to a child"],
        "final": {"index": 727, "pivot": list(top.pivot), "required": points_json(final.required),
                  "support": points_json(final.support), "required_count": len(final.required),
                  "support_count": len(final.support), "height": final.height,
                  "support_sha256": point_digest(final.support)},
        "finite_board": {"bounds": {"x_min": 0, "x_max": 16, "y_min": 0, "y_max": 16},
                         "square_cells": 289, "envelope_cells": 251, "max_maker_moves": 21,
                         "max_occupied_before_maker_move": 40, "min_free_envelope_cells": 211,
                         "occupancy_assumptions": "Empty board; alternating single fresh-cell claims; Maker first."},
        "cards": [{"index": i, "required_count": len(c.required), "support_count": len(c.support),
                   "height": c.height, "required_sha256": point_digest(c.required),
                   "support_sha256": point_digest(c.support)} for i, c in enumerate(cards)],
        "final_children": child_records, "successive_intersections": ends,
        "limits": ["Reconstruction checks this exact finite certificate, not a complete strategy search.",
                   "The game-strategy implication and quantifier order require the separate Lean theorem.",
                   "The 728-card theorem certificate is distinct from the historical 616-row comparator.",
                   "The 21-move bound and finite-board result are already stated in the source paper.",
                   "No claim of a 20-move strategy, novelty, or improved agent reasoning."]}


def replay(root=ROOT):
    root = Path(root)
    actual = audit(root)
    saved = read(root / OUTPUT)
    require(encode(saved) == encode(actual), "Saved Snaky computational receipt differs from independent reconstruction")
    return actual


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "replay"))
    args = parser.parse_args(argv)
    try:
        result = audit() if args.command == "check" else replay()
        if args.command == "check":
            (ROOT / OUTPUT).write_bytes(encode(result))
        print(json.dumps({"status": "PASS", "command": args.command, "claim_id": CLAIM_ID,
                          "cards": result["counts"]["numbered_cards"], "final_cells": result["final"]["support_count"],
                          "height": result["final"]["height"], "output": OUTPUT}, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print("Snaky audit failed: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
