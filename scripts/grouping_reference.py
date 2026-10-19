"""Independent Python reference for specs/unary-grouping-v1.json.

Written from that contract without reading or importing the Lean/native checker.
Decoding uses arithmetic base-4 digits; preservation uses the image labels of
each block. This is executable reference code, not a formally proved reference.
Agreement with it does not establish compiler or machine-code correctness.

Public functions reject non-builtin-int values (including bool and float) with
TypeError, and out-of-range integers with ValueError. Neither rejection is a
false preservation result. A serialized adapter may translate these exceptions
into its separately specified invalid_input result.
"""

from __future__ import annotations


CONTRACT_ID = "unary-grouping-v1"
REFERENCE_VERSION = "1"
INPUT_COUNT = 65536


def decode(word: int) -> tuple[list[int], list[int]]:
    """Return the operation outputs and group labels, each in object order.

    The eight base-4 digits, least significant first, are f(0)..f(3),
    g(0)..g(3). All 16-bit words are valid, even with unused or repeated labels.
    """
    if type(word) is not int:
        raise TypeError("invalid_input: word must be a built-in integer, not bool or float")
    if word < 0 or word >= INPUT_COUNT:
        raise ValueError("invalid_input: word must be between 0 and 65535 inclusive")
    digits = []
    remaining = word
    for _ in range(8):
        remaining, digit = divmod(remaining, 4)
        digits.append(digit)
    return digits[:4], digits[4:]


def _blocks(labels: list[int]) -> list[list[int]]:
    """List the blocks in first-object order, without canonicalizing labels."""
    by_label: dict[int, list[int]] = {}
    for element, label in enumerate(labels):
        by_label.setdefault(label, []).append(element)
    return list(by_label.values())


def evaluate(word: int) -> dict:
    """Evaluate preservation, giving a concrete violating pair on failure.

    A grouping is preserved precisely when each block's image occupies one
    block. The returned pair is in object order and has equal original labels
    but different output labels. Pair choice is deterministic, not part of the
    mathematical acceptance condition.
    """
    operation, labels = decode(word)
    for block in _blocks(labels):
        image_labels = {labels[operation[element]] for element in block}
        if len(image_labels) > 1:
            first = block[0]
            second = next(
                element for element in block[1:]
                if labels[operation[element]] != labels[operation[first]]
            )
            return {"preserves": False, "violating_pair": [first, second]}
    return {"preserves": True, "violating_pair": None}


def repair_grouping(word: int) -> int:
    """Coarsen the grouping until it is preserved, keeping the operation fixed.

    If a block's image meets multiple blocks, merge those entire output blocks
    and repeat. Every merge reduces the number of blocks, so there are at most
    three merges. These merges are forced in any preserved coarsening: images
    of objects already together must remain together. This explains the method;
    it is not a machine-checked proof of the implementation or its minimality.

    Merged blocks retain their smallest existing label. Labels need not become
    consecutive. Already-preserved inputs return the exact original word.
    The universal grouping is sometimes the only coarsening that works; that
    trivial fallback should not be presented as a new mathematical construction.
    """
    operation, labels = decode(word)
    while True:
        for block in _blocks(labels):
            image_labels = {labels[operation[element]] for element in block}
            if len(image_labels) > 1:
                merged_label = min(image_labels)
                labels = [merged_label if label in image_labels else label for label in labels]
                break
        else:
            digits = operation + labels
            return sum(digit * (4 ** position) for position, digit in enumerate(digits))
