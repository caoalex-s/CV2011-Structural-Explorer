"""Reject unapproved axioms in the printed real-field theorem dependencies."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text(encoding="utf-8")
lines = [line for line in text.splitlines() if "RealBeamFields." in line]
if len(lines) != 37:
    raise SystemExit(f"Expected 37 axiom reports, got {len(lines)}.")
for line in lines:
    if "does not depend on any axioms" in line:
        continue
    match = re.search(r"depends on axioms:\s*\[([^]]*)\]", line)
    if not match:
        raise SystemExit("Unrecognised axiom report: " + line)
    actual = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if actual - ALLOWED:
        raise SystemExit("Unapproved axioms: " + ", ".join(sorted(actual - ALLOWED)))
print("Audited all real-field theorems against the standard Mathlib axiom allowlist.")
