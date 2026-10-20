"""Generate finite-board semantic derivations from pinned upstream card proofs.

This textual generator is not a verifier. Lean checks every resulting proof.
Exact upstream data and combinatorial lemmas remain in their original modules.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent

def generated():
    manifest = json.loads((ROOT / "vendor-manifest.json").read_text(encoding="utf-8"))
    for item in manifest["files"]:
        actual = (ROOT / item["path"]).read_bytes()
        if hashlib.sha256(actual).hexdigest() != item["sha256"]:
            raise ValueError("vendored source hash mismatch: " + item["path"])
    count = 0
    for source in sorted((ROOT / "OAI/GameTheory/SnakyTwentyOne/Cards").glob("*.lean")):
        text = source.read_text(encoding="utf-8")
        parts = re.findall(r"theorem (?:row_works_[0-9]+(?:_i[0-9]+)*|children_work_[0-9]+(?:_i[0-9]+)*)\b.*?(?=\ntheorem |\ndef |\nend )", text, re.S)
        count += len(parts)
        imports = ["import SnakySemantics", "import " + ".".join(source.relative_to(ROOT).with_suffix("").parts)]
        imports += ["import FiniteCards." + name for name in re.findall(r"import OAI\.GameTheory\.SnakyTwentyOne\.Cards\.(\w+)", text)]
        body = "\n\n".join(parts)
        for old, new in [("placed21_template", "finite_placed21_template"), ("immediate_template", "finite_immediate"), ("row_works_", "finite_row_works_"), ("children_work_", "finite_children_work_"), ("Template", "FiniteTemplate")]:
            body = body.replace(old, new)
        body = re.sub(r"\bcompose\b", "finite_compose", body)
        result = "/- Derived from openai/math SnakyTwentyOne card proofs at\n1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0).\nModified here to use bounded finite-board semantics; see UPSTREAM_LICENSE. -/\n" + "\n".join(imports) + "\n\nnamespace FiniteCongruenceChecks.SnakyFinite\nopen OAI.SnakyPrototype OAI.SnakyPrototype.Certificate21\n\n" + body + "\n\nend FiniteCongruenceChecks.SnakyFinite\n"
        yield ROOT / "FiniteCards" / source.name, result
    if count != 3246:
        raise ValueError(f"expected 3246 semantic derivations, found {count}")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    results = list(generated())
    for path, text in results:
        expected = text.encode("utf-8")
        if args.check:
            if path.read_bytes().replace(b"\r\n", b"\n") != expected:
                raise ValueError("stale finite proof: " + str(path))
        else:
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(expected)
    print(f"{len(results)} finite-card modules: 3246 Lean derivations {'match' if args.check else 'generated'}")

if __name__ == "__main__":
    main()
