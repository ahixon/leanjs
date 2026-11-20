#!/usr/bin/env python3
"""Spec-traceability and core-purity checks for leanjs.

  tools/spec.py            report spec anchors per spec + run purity checks (exit 1 on violation)
  tools/spec.py --list     also print every anchor with its file:line

Spec anchors are comments of the form `spec: <url>#<fragment>` placed above the Lean definition
that implements that spec step. Purity rules for the engine (ES/): no `partial`, no `sorry`,
no `unsafe`, no `@[implemented_by]` (use `@[csimp]` with a proof), no `Float`.
Proofs (JSProofs/): no `sorry`, `admit`, `native_decide`, or new axioms.
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE = [ROOT / "ES.lean", *sorted((ROOT / "ES").rglob("*.lean"))]
ANCHOR = re.compile(r"spec:\s*(https?://[^\s#]+)(#[\w\-.:%]+)?")
FORBIDDEN = {
    r"\bpartial\s+def\b": "core functions must be total",
    r"\bsorry\b": "no sorry in the core",
    r"\bunsafe\b": "no unsafe in the core",
    r"implemented_by": "use @[csimp] with an equality proof instead",
    r"\bFloat\b": "use ES.F64 (exact binary64), not Float",
}


def strip_comments(src: str) -> str:
    """Remove comments and string-literal contents (keeping line structure)."""
    keep_lines = lambda m: "\n" * m.group().count("\n")
    src = re.sub(r"/-.*?-/", keep_lines, src, flags=re.S)
    src = re.sub(r'"(?:[^"\\]|\\.)*"', lambda m: '""' + keep_lines(m), src, flags=re.S)
    return re.sub(r"--.*", "", src)


PROOFS = sorted((ROOT / "JSProofs").rglob("*.lean"))
PROOF_FORBIDDEN = {
    r"\bsorry\b": "proofs must be complete",
    r"\badmit\b": "proofs must be complete",
    r"\bnative_decide\b": "trusts the compiler; use decide/simp",
    r"^\s*axiom\b": "no new axioms",
}


def main() -> int:
    anchors = defaultdict(list)
    violations = []
    for path in PROOFS:
        rel = path.relative_to(ROOT)
        for i, line in enumerate(strip_comments(path.read_text()).splitlines(), 1):
            for pat, why in PROOF_FORBIDDEN.items():
                if re.search(pat, line):
                    violations.append(f"{rel}:{i}: {why}: {line.strip()}")
    for path in CORE:
        src = path.read_text()
        rel = path.relative_to(ROOT)
        for i, line in enumerate(src.splitlines(), 1):
            for m in ANCHOR.finditer(line):
                anchors[m.group(1)].append((m.group(2) or "", f"{rel}:{i}"))
        for i, line in enumerate(strip_comments(src).splitlines(), 1):
            for pat, why in FORBIDDEN.items():
                if re.search(pat, line):
                    violations.append(f"{rel}:{i}: {why}: {line.strip()}")

    print(f"spec anchors: {sum(map(len, anchors.values()))} across {len(anchors)} specs")
    for url in sorted(anchors):
        print(f"  {len(anchors[url]):4}  {url}")
        if "--list" in sys.argv:
            for frag, loc in anchors[url]:
                print(f"          {frag or '(page)':40} {loc}")
    if violations:
        print(f"\npurity violations ({len(violations)}):")
        print("\n".join(f"  {v}" for v in violations))
        return 1
    print("purity: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
