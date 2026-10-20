"""Replay one Snaky example without importing its move generator.

The frozen oracle supplies the pinned certificate grammar only. This module
reconstructs sets using separate coordinate formulas, composes placements by
their action on basis points, and checks each supplied move against the actual
position. This is finite execution evidence, not a verified policy extraction.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import check_snaky as oracle

ROOT = Path(__file__).resolve().parents[1]
INPUT = "evidence/snaky-play-v1/example.json"
SOURCE = "scripts/check_snaky_play.py"
GENERATOR = "scripts/build_snaky_play.py"
EXAMPLE_ID = "example:family-187:snaky:eight-claim-branch:v1"
IDENTITY = (1, 0, 0, 1, 0, 0)
SHAPE = ((0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1))
FORMS = (lambda x,y:(x,y), lambda x,y:(y,x), lambda x,y:(-x,y), lambda x,y:(y,-x),
         lambda x,y:(x,-y), lambda x,y:(-y,x), lambda x,y:(-x,-y), lambda x,y:(-y,-x))
LIMITS = [
    "One illustrative checked execution with chosen legal Breaker replies.",
    "Eight Maker claims in this example do not establish an eight-move guarantee.",
    "The Python move adapter is not an extracted formally verified policy.",
    "This record binds certificate and implementation inputs, not a successful Lean proof receipt.",
    "The 21-move universal theorem and its proof receipt are separate evidence.",
]


def same(actual, expected, label):
    oracle.require(json.dumps(actual, sort_keys=True, allow_nan=False) ==
                   json.dumps(expected, sort_keys=True, allow_nan=False), label + " mismatch")


def keys(value, required, label):
    oracle.require(isinstance(value, dict) and set(value) == set(required.split()), label + " fields mismatch")


def points(value, label):
    oracle.require(isinstance(value, list), label + " must be a list")
    for point in value:
        oracle.require(isinstance(point, list) and len(point) == 2 and all(type(c) is int for c in point),
                       label + " must contain integer coordinate pairs")
    result = frozenset(tuple(p) for p in value)
    same(value, oracle.points_json(result), label + " canonical coordinates")
    return result


def transform(points_, symmetry, translation):
    f = FORMS[symmetry]
    return frozenset((f(x, y)[0] + translation[0], f(x, y)[1] + translation[1]) for x, y in points_)


def evaluate(node, earlier):
    if isinstance(node, oracle.Reference):
        required, support, height = earlier[node.index]
        return transform(required, node.symmetry, node.translation), transform(support, node.symmetry, node.translation), height
    children = [evaluate(c, earlier) for c in node.children]
    support = {node.pivot}
    required = set()
    for a, t, _ in children:
        support.update(t)
        required.update(a)
    common = {p for p in children[0][1] if all(p in child[1] for child in children[1:])}
    required.update(common)
    required.discard(node.pivot)
    return frozenset(required), frozenset(support), 1 + max(c[2] for c in children)


def reconstruct(root=ROOT):
    root = Path(root)
    payload = (root / oracle.INPUT).read_bytes()
    oracle.require(oracle.raw_digest(payload) == oracle.CERTIFICATE_SHA256, "Pinned certificate bytes changed")
    cards = [(frozenset(SHAPE) - {p}, frozenset(SHAPE), 1) for p in SHAPE]
    expressions = []
    for index, line in enumerate(payload.decode("ascii").splitlines(), 6):
        node = oracle.parse_line(line, index)
        cards.append(evaluate(node, cards))
        expressions.append(node)
    oracle.require(len(cards) == 728 and len(cards[-1][1]) == 251 and cards[-1][2] == 21 and not cards[-1][0],
                   "Certificate endpoint mismatch")
    return cards, expressions


def apply(placement, point):
    a, b, c, d, tx, ty = placement
    return a*point[0] + b*point[1] + tx, c*point[0] + d*point[1] + ty


def compose(placement, ref):
    # Determine F o G by its images of 0,e1,e2, independently of the
    # generator's symbolic matrix-product formula.
    f = FORMS[ref.symmetry]
    def image(point):
        x, y = f(*point)
        return apply(placement, (x + ref.translation[0], y + ref.translation[1]))
    zero, first, second = image((0, 0)), image((1, 0)), image((0, 1))
    return (first[0]-zero[0], second[0]-zero[0], first[1]-zero[1], second[1]-zero[1], *zero)


def place_json(placement):
    return {"matrix": [list(placement[:2]), list(placement[2:4])], "translation": list(placement[4:])}


def node_at(cursor, expressions):
    card, path, _ = cursor
    if card < 6:
        oracle.require(not path, "A base has no inline children")
        return None
    node = expressions[card-6]
    for index in path:
        oracle.require(isinstance(node, oracle.Combination) and 0 <= index < len(node.children), "Invalid inline path")
        node = node.children[index]
    oracle.require(isinstance(node, oracle.Combination), "Inline path must end at a combination")
    return node


def data_at(cursor, cards, expressions):
    card, _, placement = cursor
    data = cards[card] if card < 6 else evaluate(node_at(cursor, expressions), cards[:card])
    return frozenset(apply(placement, p) for p in data[0]), frozenset(apply(placement, p) for p in data[1]), data[2]


def child_cursor(cursor, index, child):
    if isinstance(child, oracle.Reference):
        return child.index, (), compose(cursor[2], child)
    return cursor[0], cursor[1] + (index,), cursor[2]


def snapshot(cursor, cards, expressions):
    required, support, height = data_at(cursor, cards, expressions)
    card, path, placement = cursor
    url = f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/{oracle.UPSTREAM_PATH}"
    line = card-5
    if card < 6:
        url = f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/lean/OAI/GameTheory/SnakyTwentyOne/Cards/Height01Part01.lean"
        line = 8 + 7*card
    return {"card": card, "inline_path": list(path), "height": height,
            "required": oracle.points_json(required), "envelope": oracle.points_json(support),
            "placement": place_json(placement),
            "certificate_ref": {"line": line, "url": url + f"#L{line}",
                                "node": f"card {card}" + "".join(f" / child {i}" for i in path)}}


def witness(maker, board):
    # Every transformed copy includes the image of (0,0), its translation.
    # Thus every possible translation lies in Maker's current cells.
    for symmetry, f in enumerate(FORMS):
        for translation in sorted(maker):
            cells = frozenset((f(x, y)[0] + translation[0], f(x, y)[1] + translation[1]) for x, y in SHAPE)
            if cells <= maker and cells <= board:
                return {"symmetry": symmetry, "translation": list(translation), "cells": oracle.points_json(cells)}
    return None


def validate_step(step, cursor, maker, breaker, board, cards, expressions):
    """Check one local transition. Whole-play reachability is checked by validate."""
    keys(step, "move active maker_before breaker_before global_budget_before global_budget_after maker maker_after breaker breaker_after continuation won witness", "Step")
    move = step["move"]
    oracle.require(type(move) is int and 1 <= move <= 21, "Invalid Maker move count")
    oracle.require(len(maker) == len(breaker) == move-1, "Alternating move counts mismatch")
    oracle.require(maker <= board and breaker <= board and not maker & breaker, "Invalid ownership position")
    same(step["maker_before"], oracle.points_json(maker), "Maker state before")
    same(step["breaker_before"], oracle.points_json(breaker), "Breaker state before")
    same(step["active"], snapshot(cursor, cards, expressions), "Active certificate placement")
    same(step["global_budget_before"], 22-move, "Global budget before")
    same(step["global_budget_after"], 21-move, "Global budget after")
    required, support, height = data_at(cursor, cards, expressions)
    oracle.require(required <= maker and not support & breaker and support <= board, "Active card hypotheses fail")
    oracle.require(height <= 22-move and len(maker) + len(breaker) + 2*height <= len(board), "Insufficient remaining move budget")
    oracle.require(witness(maker, board) is None, "Play continued after an earlier win")
    card, _, placement = cursor
    if card < 6:
        missing = support - required
        oracle.require(len(missing) == 1, "Base must have exactly one completion cell")
        prescribed = next(iter(missing))
        kind = "base_completion"
    else:
        prescribed = apply(placement, node_at(cursor, expressions).pivot)
        kind = "pivot"
    expected = prescribed
    if prescribed in maker:
        free = board - maker - breaker
        oracle.require(bool(free), "No replacement cell available")
        expected, kind = min(free), "replacement"
    oracle.require(expected in board - maker - breaker, "Maker claim must be fresh and on board")
    same(step["maker"], {"cell": list(expected), "kind": kind, "prescribed_cell": list(prescribed)}, "Maker claim")
    after_maker = maker | {expected}
    same(step["maker_after"], oracle.points_json(after_maker), "Maker state after")
    won = witness(after_maker, board)
    same(step["won"], won is not None, "Terminal status")
    same(step["witness"], won, "Complete target witness")
    if won is not None:
        oracle.require(step["breaker"] is None and step["continuation"] is None, "No Breaker reply or continuation after victory")
        same(step["breaker_after"], oracle.points_json(breaker), "Breaker state at victory")
        return None, after_maker, breaker
    oracle.require(card >= 6, "Base completion must win")
    keys(step["breaker"], "cell", "Breaker reply")
    reply_points = points([step["breaker"]["cell"]], "Breaker reply")
    reply = next(iter(reply_points))
    oracle.require(reply in board - after_maker - breaker, "Breaker reply must be fresh and on board")
    expected_reply = ((7, 8), (8, 6))[move-1] if move <= 2 else min(board - after_maker - breaker)
    oracle.require(reply == expected_reply, "Breaker reply differs from this example's declared choices")
    after_breaker = breaker | {reply}
    same(step["breaker_after"], oracle.points_json(after_breaker), "Breaker state after")
    candidates = []
    for index, child in enumerate(node_at(cursor, expressions).children):
        nxt = child_cursor(cursor, index, child)
        child_required, child_support, child_height = data_at(nxt, cards, expressions)
        oracle.require(child_required <= after_maker and child_support <= support and child_height < height,
                       "Child requirement, containment, or decreasing-height condition failed")
        candidates.append((index, child, nxt, child_required, child_support, child_height))
    common = set(candidates[0][4]).intersection(*(c[4] for c in candidates[1:]))
    oracle.require(common <= after_maker, "Common envelope was not secured by Maker")
    chosen = next((c for c in candidates if reply not in c[4]), None)
    oracle.require(chosen is not None, "No child survives the legal Breaker reply")
    index, child, nxt, _, child_support, child_height = chosen
    oracle.require(not child_support & after_breaker, "Chosen child contains an older Breaker claim")
    reference = None
    if isinstance(child, oracle.Reference):
        reference = str(child.index)
        if child.symmetry != 0 or child.translation != (0, 0):
            reference += f":{child.symmetry}{oracle.ALPHABET[child.translation[0]]}{oracle.ALPHABET[child.translation[1]]}"
    same(step["continuation"], {"child_index": index, "kind": "reference" if reference is not None else "inline",
                                "source_reference": reference, "card": nxt[0], "inline_path": list(nxt[1]),
                                "height": child_height, "placement": place_json(nxt[2])}, "Surviving continuation")
    return nxt, after_maker, after_breaker


def validate(record, root=ROOT):
    root = Path(root)
    keys(record, "schema_version id title kind sources board choices steps result limits", "Example")
    same(record["schema_version"], 1, "Schema version")
    same(record["id"], EXAMPLE_ID, "Example identity")
    same(record["title"], "One Snaky play: eight Maker claims", "Example title")
    same(record["kind"], "illustrative_checked_execution", "Evidence kind")
    same(record["limits"], LIMITS, "Evidence limits")
    url = f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/{oracle.UPSTREAM_PATH}"
    same(record["sources"], {
        "certificate": {"path": oracle.INPUT, "sha256": oracle.CERTIFICATE_SHA256, "url": url, "commit": oracle.UPSTREAM_COMMIT},
        "oracle": {"path": oracle.SOURCE, "sha256": oracle.digest(root / oracle.SOURCE)},
        "generator": {"path": GENERATOR, "sha256": oracle.digest(root / GENERATOR)},
        "validator": {"path": SOURCE, "sha256": oracle.digest(root / SOURCE)},
        "root_claim_id": oracle.CLAIM_ID}, "Exact input and implementation hashes")
    cards, expressions = reconstruct(root)
    board = cards[727][1]
    same(record["board"], {"name": "251-cell envelope of card 727", "cells": oracle.points_json(board),
                           "bounds": {"x_min": 0, "x_max": 16, "y_min": 0, "y_max": 16}, "cell_count": 251}, "Exact board")
    same(record["choices"], {
        "maker": "Prescribed pivot, or first free envelope cell if already owned; stop at first Snaky copy.",
        "breaker": "Two displayed paper replies, then first free envelope cell in lexicographic (x,y) order.",
        "breaker_prefix": [[7, 8], [8, 6]],
        "continuation": "First printed child whose placed envelope avoids the legal reply."}, "Declared example choices")
    steps = record["steps"]
    oracle.require(isinstance(steps, list) and 1 <= len(steps) <= 21, "Invalid trace length")
    cursor, maker, breaker = (727, (), IDENTITY), frozenset(), frozenset()
    for number, step in enumerate(steps, 1):
        oracle.require(cursor is not None, "Extra step after victory")
        oracle.require(isinstance(step, dict), "Each step must be an object")
        same(step.get("move"), number, "Consecutive move number")
        cursor, maker, breaker = validate_step(step, cursor, maker, breaker, board, cards, expressions)
    oracle.require(cursor is None and witness(maker, board) is not None, "Trace stops before a checked win")
    same(record["result"], {"maker_claims": len(maker), "breaker_claims": len(breaker), "won": True,
                            "target": witness(maker, board), "remaining_global_budget": 21-len(maker)}, "Final result")
    oracle.require(len(maker) == 8 and len(breaker) == 7, "This registered example has eight Maker claims and seven replies")
    return record


def replay(root=ROOT):
    return validate(oracle.read(Path(root) / INPUT), root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", type=Path, default=ROOT / INPUT)
    args = parser.parse_args()
    result = validate(oracle.read(args.path))
    print(json.dumps({"status": "PASS", "example_id": result["id"], "maker_claims": 8, "breaker_replies": 7,
                      "scope": "One illustrative execution; no eight-move guarantee or verified policy extraction."}, sort_keys=True))


if __name__ == "__main__":
    main()
