"""Check that the explicit Lean tables match this repository's JSON evidence."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = {
    "OAI/Algebra/Universal/GraphCriterion.lean": "bd80c2bea95ee1b4f7118fc8dc272aebac7b23038ba93cdafd386dc1b688fb50",
    "OAI/Algebra/Universal/Congruence.lean": "30e9201344dcf4069ca9ace276c76dc3b1507d09f0f6bfbf5a7c5d693ac9716c",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    source = (ROOT / "lean/FiniteCongruenceChecks.lean").read_text(encoding="utf-8")
    minimized = json.loads((ROOT / "evidence/minimized-algebras.json").read_text(encoding="utf-8"))
    operations = {item["certificate"]: item["selected_unary_operations"]
                  for item in minimized["certificates"]}
    checked = []
    for name in ("N5", "B3"):
        certificate = ROOT / "evidence" / f"{name}-witness.json"
        data = json.loads(certificate.read_text(encoding="utf-8"))
        section = source.split(f"namespace {name}\n", 1)[1].split(f"end {name}\n", 1)[0]
        for table_name, matrix in (("le", data["lattice"]["leq"]), ("color", data["color"])):
            body = section.split(f"def {table_name} ", 1)[1].split("\n\n", 1)[0]
            rows = re.findall(r"^  \| (\d+), (\d+) => (true|false|\d+)$", body, re.M)
            actual = {(int(i), int(j)): {"true": True, "false": False}.get(v, int(v) if v.isdigit() else None)
                      for i, j, v in rows}
            expected = {(i, j): v for i, row in enumerate(matrix) for j, v in enumerate(row)}
            require(len(rows) == len(expected) and actual == expected, f"{name}: {table_name} table differs")
        require(len(operations[certificate.name]) == 2, f"{name}: expected exactly two operations")
        for index, expected in enumerate(operations[certificate.name], 1):
            body = section.split(f"def op{index} ", 1)[1].split("\n\n", 1)[0]
            rows = re.findall(r"^  \| (\d+|_) => (\d+)$", body, re.M)
            require(rows == [("0", str(expected[0])), ("1", str(expected[1])),
                            ("2", str(expected[2])), ("_", str(expected[3]))], f"{name}: operation {index} differs")
        checked.append({"lattice": name, "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest()})
    for path, expected in UPSTREAM.items():
        actual = hashlib.sha256((ROOT / "lean/upstream" / path).read_bytes()).hexdigest()
        require(actual == expected, f"vendored upstream source differs: {path}")
    print(json.dumps({"passed": True, "tables_checked": checked, "upstream_sha256": UPSTREAM}, indent=2))


if __name__ == "__main__":
    main()
