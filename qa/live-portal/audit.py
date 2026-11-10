"""Emit and strictly audit every named theorem in the portal bridge.

No Lean execution here. --emit writes the public audit source; --check verifies
the separate kernel log using the already accepted axiom-policy parser.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

spec = importlib.util.spec_from_file_location('strict_audit', Path(__file__).parents[1] / 'wasm-feasibility/audit_axioms.py')
strict_audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(strict_audit)

def expected_theorems(source):
    names = re.findall(r'^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)', source, re.MULTILINE)
    if not names or len(names) != len(set(names)):
        raise ValueError('Missing or repeated source theorem names')
    return {'PortalSoundness.' + name for name in names}

def audit(source, log):
    strict_audit.EXPECTED_THEOREMS = expected_theorems(source)
    return strict_audit.audit_reports(log)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', type=Path)
    parser.add_argument('--check', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = Path('proofs/PortalSoundness.lean').read_text(encoding='utf-8')
    if args.emit:
        args.emit.write_text('import PortalSoundness\n' + ''.join('#print axioms ' + name + '\n' for name in sorted(expected_theorems(source))), encoding='utf-8')
    if args.check:
        reports = audit(source, args.check.read_text(encoding='utf-8'))
        receipt = {'passed': True, 'theorems': reports,
                   'source_sha256': hashlib.sha256(Path('proofs/PortalSoundness.lean').read_bytes()).hexdigest(),
                   'log_sha256': hashlib.sha256(args.check.read_bytes()).hexdigest()}
        args.output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
