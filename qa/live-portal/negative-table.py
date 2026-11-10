"""CI-only negative fixture: changing one fixed K entry must break its model proof.

All changes are confined to a fresh .data directory. The ordinary source and
positive compiled checker stay intact. This is not an alternative checker build.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

assert sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true'
root = Path.cwd()
folder = root / '.data/live-portal/table-negative'
folder.mkdir()
source = (root / 'proofs/PortalTables.lean').read_text()
needle = '(1011250 / 3)'
assert source.count(needle) == 2
mutant = source.replace(needle, '(1011253 / 3)', 1)
(folder / 'PortalTables.lean').write_text(mutant)
for name in ['PortalChecker.lean', 'PortalSoundness.lean']:
    (folder / name).write_bytes((root / 'proofs' / name).read_bytes())
environment = dict(os.environ)
environment['LEAN_PATH'] = str(folder) + ':' + str(root / 'proofs') + ':' + environment.get('LEAN_PATH', '')
for module in ['PortalTables', 'PortalChecker']:
    subprocess.run(['lean', '-o', module + '.olean', module + '.lean'], cwd=folder, env=environment, check=True, timeout=120)
result = subprocess.run(['lean', 'PortalSoundness.lean'], cwd=folder, env=environment,
                        capture_output=True, text=True, timeout=180)
(folder / 'rejection.log').write_text(result.stdout + result.stderr)
proof = (folder / 'PortalSoundness.lean').read_text().splitlines()
start = next(i + 1 for i, line in enumerate(proof) if line.startswith('theorem actual_stiffness_work'))
end = next(i + 1 for i, line in enumerate(proof) if i + 1 > start and line.startswith('theorem actual_force_work'))
errors = [int(line) for line in re.findall(r'PortalSoundness.lean:(\d+):\d+: error:', result.stdout)]
assert result.returncode != 0 and any(start <= line < end for line in errors), 'Mutated K did not fail its actual-model bridge'
(folder / 'result.json').write_text(json.dumps({'passed': True, 'mutation': 'K[3,3] += 1',
    'original_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'mutant_sha256': hashlib.sha256(mutant.encode()).hexdigest(),
    'failed_actual_stiffness_bridge': True}, indent=2) + '\n')
