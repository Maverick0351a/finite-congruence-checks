"""Draw the independently reconstructed final Snaky support as an accessible SVG."""
from __future__ import annotations

import argparse
from html import escape
from pathlib import Path

import check_snaky

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/assets/snaky-board.svg"


def render():
    report = check_snaky.replay()
    support = {tuple(p) for p in report["final"]["support"]}
    # Pick an interior example of the unrotated six-cell target, independently
    # of any choice that a particular strategy execution would make.
    candidates = [(x, y) for x in range(17) for y in range(17)
                  if {(x + dx, y + dy) for dx, dy in check_snaky.SNAKY} <= support
                  and (8, 8) not in {(x + dx, y + dy) for dx, dy in check_snaky.SNAKY}]
    check_snaky.require(bool(candidates), "No illustrative target fits in the support")
    dx, dy = min(candidates, key=lambda p: ((p[0] - 5)**2 + (p[1] - 5)**2, p))
    target = {(x + dx, y + dy): i + 1 for i, (x, y) in enumerate(check_snaky.SNAKY)}
    items = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="1000" height="690" viewBox="0 0 1000 690" role="img" aria-labelledby="title description">',
        '<title id="title">The 251-cell Snaky certificate support inside a 17 by 17 board</title>',
        '<desc id="description">Coordinates run from 0 to 16 on both axes. Blue cells form the 251-cell support of card 727. P marks the root pivot at (8,8). Six green cells labelled S1 through S6 illustrate one Snaky target; they are not occupied starting cells or an execution trace. Before Maker move 21, at most 40 cells are occupied, leaving at least 211 support cells free.</desc>',
        '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#17324d}.heading{font-size:25px;font-weight:700}.sub{font-size:15px;fill:#526679}.tick{font-size:11px;fill:#526679}.label{font-size:16px}.small{font-size:14px}.cell-label{font-size:10px;font-weight:700;fill:white;text-anchor:middle;dominant-baseline:middle}.number{font-size:30px;font-weight:700}</style>',
        '<rect width="1000" height="690" rx="18" fill="#f8fafc"/>',
        '<text x="42" y="45" class="heading">A finite board with room for every required move</text>',
        '<text x="42" y="72" class="sub">Exact certificate: 728 cards · final support: 251 cells · height: 21 Maker moves</text>',
    ]
    left, top, step = 64, 118, 27
    for y in range(17):
        for x in range(17):
            px, py = left + x * step, top + (16 - y) * step
            point = (x, y)
            fill = "#d8e9f6" if point in support else "#ffffff"
            stroke = "#91b5d1" if point in support else "#d5dce4"
            if point in target:
                fill, stroke = "#146d62", "#0b4f49"
            elif point == (8, 8):
                fill, stroke = "#a95f00", "#774200"
            label = f"({x},{y}): " + ("certificate support" if point in support else "square cell outside the support")
            if point in target:
                label += f"; illustrative target cell S{target[point]}"
            if point == (8, 8):
                label += "; root pivot P"
            items.append(f'<rect x="{px}" y="{py}" width="25" height="25" rx="3" fill="{fill}" stroke="{stroke}"><title>{escape(label)}</title></rect>')
            if point in target or point == (8, 8):
                name = f"S{target[point]}" if point in target else "P"
                items.append(f'<text x="{px + 12.5}" y="{py + 13}" class="cell-label">{name}</text>')
    for i in range(17):
        items.append(f'<text x="{left + i * step + 12.5}" y="{top + 17 * step + 17}" class="tick" text-anchor="middle">{i}</text>')
        items.append(f'<text x="{left - 12}" y="{top + (16-i) * step + 17}" class="tick" text-anchor="end">{i}</text>')
    items.extend([
        '<text x="286" y="620" class="small" text-anchor="middle">x coordinate</text>',
        '<text x="23" y="350" class="small" text-anchor="middle" transform="rotate(-90 23 350)">y coordinate</text>',
        '<text x="565" y="133" class="label" font-weight="700">How to read the board</text>',
        '<rect x="565" y="153" width="19" height="19" rx="3" fill="#d8e9f6" stroke="#91b5d1"/>',
        '<text x="595" y="168" class="small">251 cells in the final support</text>',
        '<rect x="565" y="184" width="19" height="19" rx="3" fill="white" stroke="#d5dce4"/>',
        '<text x="595" y="199" class="small">38 other cells of the square board</text>',
        '<rect x="565" y="215" width="19" height="19" rx="3" fill="#a95f00"/>',
        '<text x="595" y="230" class="small">P: first prescribed pivot, (8,8)</text>',
        '<rect x="565" y="246" width="19" height="19" rx="3" fill="#146d62"/>',
        '<text x="595" y="261" class="small">S1–S6: one illustrative Snaky target</text>',
        '<rect x="552" y="296" width="402" height="203" rx="12" fill="#e9f2f8"/>',
        '<text x="573" y="327" class="label" font-weight="700">Why a replacement cell is available</text>',
        '<text x="573" y="354" class="small">If play reaches Maker move 21:</text>',
        '<text x="573" y="381" class="small">20 Maker claims + 20 Breaker claims</text>',
        '<text x="573" y="409" class="small">occupy at most 40 cells.</text>',
        '<text x="573" y="454" class="number">251 − 40 = 211</text>',
        '<text x="573" y="481" class="small">At least 211 support cells are still free.</text>',
        '<text x="565" y="537" class="small">All cells start unclaimed. The highlighted</text>',
        '<text x="565" y="559" class="small">target is an illustration; no play trace is shown.</text>',
        '<text x="565" y="592" class="small">The diagram shows a fixed support. The proof</text>',
        '<text x="565" y="614" class="small">also handles every legal Breaker reply.</text>',
        '<text x="42" y="661" class="sub">Generated from the pinned certificate and independent audit · finite-congruence-checks</text>',
        '</svg>',
    ])
    return "\n".join(items) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.check:
        check_snaky.require(OUTPUT.read_text(encoding="utf-8") == content, "Snaky board SVG is stale")
        print("Snaky board SVG matches the independent computational receipt.")
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_bytes(content.encode("utf-8"))
        print(OUTPUT)


if __name__ == "__main__":
    main()
