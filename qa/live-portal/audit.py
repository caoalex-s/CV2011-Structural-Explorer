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

def expected_theorems(source, namespace='PortalSoundness'):
    names = re.findall(r'^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)', source, re.MULTILINE)
    if not names or len(names) != len(set(names)):
        raise ValueError('Missing or repeated source theorem names')
    return {namespace + '.' + name for name in names}

def audit(source, log):
    strict_audit.EXPECTED_THEOREMS = expected_theorems(source)
    return strict_audit.audit_reports(log)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', type=Path)
    parser.add_argument('--check', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--frame', action='store_true', help='Audit all generic frame bridge theorems.')
    args = parser.parse_args()
    if args.frame:
        sources = sorted(Path('proofs').glob('RationalFrame*.lean'))
        expected = set()
        for path in sources:
            source = path.read_text(encoding='utf-8')
            if not re.search(r'^theorem\s+', source, re.MULTILINE):
                continue
            namespaces = re.findall(r'^namespace\s+(\S+)', source, re.MULTILINE)
            if len(namespaces) != 1:
                raise ValueError(f'Audit requires an explicit single namespace: {path}')
            expected.update(expected_theorems(source, namespaces[0]))
        imported = 'RationalFrameSoundness'
    else:
        sources = [Path('proofs/PortalSoundness.lean')]
        expected = expected_theorems(sources[0].read_text(encoding='utf-8'))
        imported = 'PortalSoundness'
    if args.emit:
        # Keep each complete dependency list on one line for the strict parser.
        # This changes pretty-print layout only; no dependency is suppressed.
        args.emit.write_text(f'import {imported}\nset_option pp.width 1000\n' +
                            ''.join('#print axioms ' + name + '\n' for name in sorted(expected)), encoding='utf-8')
    if args.check:
        strict_audit.EXPECTED_THEOREMS = expected
        reports = strict_audit.audit_reports(args.check.read_text(encoding='utf-8'))
        receipt = {'passed': True, 'theorems': reports,
                   'sources': {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sources},
                   'log_sha256': hashlib.sha256(args.check.read_bytes()).hexdigest()}
        if not args.frame:
            receipt['source_sha256'] = receipt['sources'][str(sources[0])]
        args.output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
