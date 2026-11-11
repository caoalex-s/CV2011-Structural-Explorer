"""CI-only final browser verification of an already reproduced structural bundle.

This entry does not compile WASM. The fixture checks its immutable hashes,
current proof sources, ABI, worker and fresh axiom audit, then exercises the
actual installed checker in the final workspace. Run from the repository root.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys

assert sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true'
root = Path.cwd()
output = root / '.data/live-portal-browser'
output.mkdir()
subprocess.run(['npm', 'install', '--prefix', str(output), '--ignore-scripts',
                '--save-exact', 'playwright@1.51.1'], check=True)
subprocess.run(['node', str(output / 'node_modules/playwright/cli.js'),
                'install', '--with-deps', 'chromium'], check=True)
shutil.copyfile(root / 'qa/live-portal/browser-test.mjs', output / 'browser-test.mjs')
subprocess.run(['node', str(output / 'browser-test.mjs'),
                str(root / 'public/portal-checker/bundle'), str(root / 'qa/live-portal'),
                str(output)], check=True)
