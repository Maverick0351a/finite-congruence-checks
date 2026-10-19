"""Generate one illustrative Snaky execution, independently replayed before saving.

This is an adapter over the frozen certificate evaluator. It is not extracted
from Lean and does not establish an eight-move winning guarantee.
"""
from __future__ import annotations

import argparse
from pathlib import Path

import check_snaky as oracle

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = "evidence/snaky-play-v1/example.json"
SOURCE = "scripts/build_snaky_play.py"
VALIDATOR = "scripts/check_snaky_play.py"
EXAMPLE_ID = "example:family-187:snaky:eight-claim-branch:v1"
IDENTITY = (1, 0, 0, 1, 0, 0)
PREFIX = ((7, 8), (8, 6))
LIMITS = [
    "One illustrative checked execution with chosen legal Breaker replies.",
    "Eight Maker claims in this example do not establish an eight-move guarantee.",
    "The Python move adapter is not an extracted formally verified policy.",
    "This record binds certificate and implementation inputs, not a successful Lean proof receipt.",
    "The 21-move universal theorem and its proof receipt are separate evidence.",
]


def affine(placement, point):
    a, b, c, d, tx, ty = placement
    x, y = point
    return a*x + b*y + tx, c*x + d*y + ty


def compose(outer, reference):
    a, b, c, d, tx, ty = outer
    e, f, g, h = oracle.MATRICES[reference.symmetry]
    dx, dy = reference.translation
    return (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h,
            a*dx + b*dy + tx, c*dx + d*dy + ty)


def placement_json(placement):
    a, b, c, d, tx, ty = placement
    return {"matrix": [[a, b], [c, d]], "translation": [tx, ty]}


def local_node(cursor, expressions):
    card, path, _ = cursor
    if card < 6:
        return None
    node = expressions[card - 6]
    for index in path:
        node = node.children[index]
    return node


def data_at(cursor, cards, expressions):
    card, _, placement = cursor
    node = local_node(cursor, expressions)
    local = cards[card] if card < 6 else oracle.evaluate(node, cards[:card])
    return oracle.Card(frozenset(affine(placement, p) for p in local.required),
                       frozenset(affine(placement, p) for p in local.support), local.height)


def source_reference(reference):
    if reference.symmetry == 0 and reference.translation == (0, 0):
        return str(reference.index)
    dx, dy = reference.translation
    return f"{reference.index}:{reference.symmetry}{oracle.ALPHABET[dx]}{oracle.ALPHABET[dy]}"


def next_cursor(cursor, index, child):
    card, path, placement = cursor
    if isinstance(child, oracle.Reference):
        return child.index, (), compose(placement, child)
    return card, path + (index,), placement


def active_json(cursor, cards, expressions):
    card, path, placement = cursor
    data = data_at(cursor, cards, expressions)
    base_url = f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/{oracle.UPSTREAM_PATH}"
    line = card - 5
    if card < 6:
        base_url = f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/lean/OAI/GameTheory/SnakyTwentyOne/Cards/Height01Part01.lean"
        line = 8 + 7*card
    node_name = f"card {card}" + "".join(f" / child {i}" for i in path)
    return {"card": card, "inline_path": list(path), "height": data.height,
            "required": oracle.points_json(data.required), "envelope": oracle.points_json(data.support),
            "placement": placement_json(placement),
            "certificate_ref": {"line": line, "url": base_url + f"#L{line}",
                                "node": node_name}}


def targets_on(board):
    targets = []
    for symmetry in range(8):
        shape = oracle.transform(oracle.SNAKY, symmetry, (0, 0))
        for dx in range(-min(x for x, _ in shape), 17 - max(x for x, _ in shape)):
            for dy in range(-min(y for _, y in shape), 17 - max(y for _, y in shape)):
                target = frozenset((x + dx, y + dy) for x, y in shape)
                if target <= board:
                    targets.append((symmetry, (dx, dy), target))
    return targets


def winning_target(maker, targets):
    for symmetry, translation, cells in targets:
        if cells <= maker:
            return {"symmetry": symmetry, "translation": list(translation), "cells": oracle.points_json(cells)}
    return None


def build_step(cursor, maker, breaker, move, reply, board, cards, expressions, targets):
    """Also usable for isolated replacement fixtures; not a claim of reachability."""
    data = data_at(cursor, cards, expressions)
    oracle.require(not winning_target(maker, targets), "Play already ended")
    oracle.require(data.required <= maker and not data.support & breaker, "Active card hypotheses fail")
    oracle.require(data.support <= board, "Active support leaves board")
    card, _, placement = cursor
    if card < 6:
        prescribed = next(iter(data.support - data.required))
        kind = "base_completion"
    else:
        prescribed = affine(placement, local_node(cursor, expressions).pivot)
        kind = "pivot"
    played = prescribed
    if prescribed in maker:
        played = min(board - maker - breaker)
        kind = "replacement"
    oracle.require(played in board - maker - breaker, "Maker move is not fresh and on board")
    maker_after = maker | {played}
    witness = winning_target(maker_after, targets)
    step = {"move": move, "active": active_json(cursor, cards, expressions),
            "maker_before": oracle.points_json(maker), "breaker_before": oracle.points_json(breaker),
            "global_budget_before": 22 - move, "global_budget_after": 21 - move,
            "maker": {"cell": list(played), "kind": kind, "prescribed_cell": list(prescribed)},
            "maker_after": oracle.points_json(maker_after), "breaker": None,
            "breaker_after": oracle.points_json(breaker), "continuation": None,
            "won": witness is not None, "witness": witness}
    if witness is not None:
        return step, None, maker_after, breaker
    oracle.require(card >= 6, "Base completion did not win")
    if reply is None:
        reply = min(board - maker_after - breaker)
    oracle.require(reply in board - maker_after - breaker, "Breaker reply is not fresh and on board")
    breaker_after = breaker | {reply}
    for index, child in enumerate(local_node(cursor, expressions).children):
        nxt = next_cursor(cursor, index, child)
        child_data = data_at(nxt, cards, expressions)
        if reply not in child_data.support:
            step["breaker"] = {"cell": list(reply)}
            step["breaker_after"] = oracle.points_json(breaker_after)
            step["continuation"] = {
                "child_index": index, "kind": "reference" if isinstance(child, oracle.Reference) else "inline",
                "source_reference": source_reference(child) if isinstance(child, oracle.Reference) else None,
                "card": nxt[0], "inline_path": list(nxt[1]), "height": child_data.height,
                "placement": placement_json(nxt[2]),
            }
            return step, nxt, maker_after, breaker_after
    raise ValueError("No surviving child")


def build(root=ROOT):
    root = Path(root)
    oracle.replay(root)
    payload = (root / oracle.INPUT).read_bytes()
    cards, expressions, _ = oracle.reconstruct(payload)
    board = cards[727].support
    targets = targets_on(board)
    cursor, maker, breaker = (727, (), IDENTITY), frozenset(), frozenset()
    steps = []
    for move in range(1, 22):
        reply = PREFIX[move - 1] if move <= len(PREFIX) else None
        step, cursor, maker, breaker = build_step(cursor, maker, breaker, move, reply, board,
                                                 cards, expressions, targets)
        steps.append(step)
        if step["won"]:
            break
    oracle.require(steps[-1]["won"], "Example did not terminate within the initial move bound")
    return {
        "schema_version": 1, "id": EXAMPLE_ID, "title": "One Snaky play: eight Maker claims",
        "kind": "illustrative_checked_execution",
        "sources": {
            "certificate": {"path": oracle.INPUT, "sha256": oracle.raw_digest(payload),
                            "url": f"https://github.com/openai/math/blob/{oracle.UPSTREAM_COMMIT}/{oracle.UPSTREAM_PATH}",
                            "commit": oracle.UPSTREAM_COMMIT},
            "oracle": {"path": oracle.SOURCE, "sha256": oracle.digest(root / oracle.SOURCE)},
            "generator": {"path": SOURCE, "sha256": oracle.digest(root / SOURCE)},
            "validator": {"path": VALIDATOR, "sha256": oracle.digest(root / VALIDATOR)},
            "root_claim_id": oracle.CLAIM_ID,
        },
        "board": {"name": "251-cell envelope of card 727", "cells": oracle.points_json(board),
                  "bounds": {"x_min": 0, "x_max": 16, "y_min": 0, "y_max": 16}, "cell_count": 251},
        "choices": {"maker": "Prescribed pivot, or first free envelope cell if already owned; stop at first Snaky copy.",
                    "breaker": "Two displayed paper replies, then first free envelope cell in lexicographic (x,y) order.",
                    "breaker_prefix": [list(p) for p in PREFIX],
                    "continuation": "First printed child whose placed envelope avoids the legal reply."},
        "steps": steps,
        "result": {"maker_claims": len(maker), "breaker_claims": len(breaker), "won": True,
                   "target": steps[-1]["witness"], "remaining_global_budget": 21 - len(maker)},
        "limits": LIMITS,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    import check_snaky_play
    result = build()
    check_snaky_play.validate(result)
    path = ROOT / OUTPUT
    if args.check:
        oracle.require(oracle.encode(oracle.read(path)) == oracle.encode(result), "Snaky example is stale")
        print("Snaky example matches its deterministic adapter and independent replay.")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(oracle.encode(result))
        print(path)


if __name__ == "__main__":
    main()
