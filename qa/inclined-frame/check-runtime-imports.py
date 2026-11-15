"""Check local runtime imports before the later authoritative Lean --deps gate.

Run from the repository root. This source-only check executes no Lean code and
does not establish compilation, proof acceptance or a WASM import closure.
"""
import hashlib
import json
from pathlib import Path
import re

pending = ['InclinedFrameIntervalReport', 'RationalFrameWire', 'PortalChecker']
sources = {}
external = set()
while pending:
    module = pending.pop()
    if module in sources or module in external:
        continue
    if module == 'Init' or module.startswith(('Init.', 'Batteries.')):
        external.add(module)
        continue
    path = Path('proofs').joinpath(*module.split('.')).with_suffix('.lean')
    assert path.is_file(), f'Unexpected external runtime import: {module}'
    content = path.read_bytes()
    sources[module] = hashlib.sha256(content).hexdigest()
    imports = re.findall(r'^import\s+([^\r\n]+)', content.decode('utf-8'), re.MULTILINE)
    for statement in imports:
        pending.extend(statement.split('--', 1)[0].split())

print(json.dumps({'local_runtime_modules': sources, 'external_imports': sorted(external),
                  'scope': 'Local source imports only; compiled dependency gate still required'}, indent=2))
