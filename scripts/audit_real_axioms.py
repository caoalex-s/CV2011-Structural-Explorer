"""Reject missing theorem reports and unapproved real-field proof axioms."""
from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
module = sys.argv[2] if len(sys.argv) > 2 else "RealBeamFields"
audit_module = {"RealBeamFields": "RealBeamAudit", "LocalFrameFields": "LocalFrameAudit",
                "FrameTransform": "FrameTransformAudit", "FrameEnergy": "FrameEnergyAudit", "FrameVirtualWork": "FrameVirtualWorkAudit", "FramePotential": "FramePotentialAudit", "FrameAssemblyModel": "FrameAssemblyModelAudit", "FrameAssembly": "FrameAssemblyAudit", "FrameDeformation": "FrameDeformationAudit"}[module]
source = Path(module + ".lean").read_text(encoding="utf-8")
audit_source = Path(audit_module + ".lean").read_text(encoding="utf-8")
expected = set(re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE))
printed = re.findall(r"^#print axioms " + re.escape(module) + r"\.(\w+)", audit_source, flags=re.MULTILINE)
if not expected or set(printed) != expected or len(printed) != len(expected):
    raise SystemExit("Axiom audit must list every real-field theorem exactly once.")
reports = Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
seen = set()
for line in reports:
    name = re.search(re.escape(module) + r"\.(\w+)", line)
    if not name:
        continue
    name = name.group(1)
    if name not in expected or name in seen:
        raise SystemExit("Unexpected or repeated axiom report: " + name)
    seen.add(name)
    if "does not depend on any axioms" in line:
        continue
    match = re.search(r"depends on axioms:\s*\[([^]]*)\]", line)
    if not match:
        raise SystemExit("Unrecognised axiom report: " + line)
    actual = {item.strip() for item in match.group(1).split(",") if item.strip()}
    if actual - ALLOWED:
        raise SystemExit("Unapproved axioms: " + ", ".join(sorted(actual - ALLOWED)))
if seen != expected:
    raise SystemExit("Missing axiom reports: " + ", ".join(sorted(expected - seen)))
print(f"Audited {len(seen)} real-field theorems against the standard Mathlib axiom allowlist.")
