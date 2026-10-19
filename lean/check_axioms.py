"""Require a fresh axiom report for every published formal claim."""
import argparse
import json
from pathlib import Path
import re

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPECTED = tuple(
    f"FiniteCongruenceChecks.{name}.{declaration}"
    for name in ("N5", "B3")
    for declaration in ("finite_classification", "all_congruences", "representation", "all_relations")
) + tuple(
    f"FiniteCongruenceChecks.UpstreamBridge.{name}.{declaration}"
    for name in ("N5", "B3")
    for declaration in ("congruenceOrderIso", "principalColor_eq", "isGraphWitness", "hasGraphWitness", "representable")
) + tuple(f"OAI.FiniteCongruence.{name}" for name in
          ("graph_criterion", "graphOrderIso", "principalColor_isGraphWitness"))


def check(text: str) -> dict:
    entries = re.findall(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports = {}
    for name, body in entries:
        if name in reports:
            raise ValueError(f"Duplicate axiom report: {name}")
        axioms = [item.strip() for item in body.split(",") if item.strip()]
        unexpected = set(axioms) - ALLOWED
        if unexpected:
            raise ValueError(f"Unapproved axioms for {name}: {sorted(unexpected)}")
        reports[name] = axioms
    if set(reports) != set(EXPECTED):
        raise ValueError(f"Incomplete or unexpected axiom reports: missing={sorted(set(EXPECTED) - set(reports))}, "
                         f"extra={sorted(set(reports) - set(EXPECTED))}")
    return {"passed": True, "allowed_axioms": sorted(ALLOWED), "declarations": reports}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.log.read_text(encoding="utf-8")), indent=2))
