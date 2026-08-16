"""NOESIS static guard for unsupported complexity declarations.

This is an auditor, not a complexity prover. It deliberately reports an
UNRESOLVED finding when a module declares O(1) while its implementation
contains input-sized iteration or an explicit argmax over the input space.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Finding:
    status: str
    reason: str
    line: int | None = None


def audit(path: str | Path) -> list[Finding]:
    source = Path(path).read_text(encoding="utf-8")
    tree = ast.parse(source)
    findings: list[Finding] = []

    declares_constant = "O(1)" in source or "constant time" in source.lower()
    input_iteration = any(isinstance(n, (ast.For, ast.While, ast.ListComp, ast.SetComp, ast.DictComp))
                          for n in ast.walk(tree))
    uses_argmax = "argmax" in source

    if declares_constant and (input_iteration or uses_argmax):
        findings.append(Finding(
            "UNRESOLVED",
            "Constant-time claim coexists with input-sized iteration/comparison; "
            "a formal cost certificate is required before promotion.",
        ))
    else:
        findings.append(Finding("NO_FINDING", "No unsupported O(1) pattern detected by this guard."))

    return findings


if __name__ == "__main__":
    target = Path(__file__).parents[1] / "src" / "ramsey_haar_oracle.py"
    for finding in audit(target):
        print(f"{finding.status}: {finding.reason}")
