"""Compare critical live bytes with the normal Pages artifact before/after smoke.

CI downloads github-pages from this same workflow. This reader opens its tar
without extracting executable files and records exact hashes. Run at repo root.
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import tarfile
import time
import urllib.request

assert sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true'
phase = sys.argv[1]
assert phase in ['before', 'after']
root = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/'
commit = os.environ['RELEASE_COMMIT']
archive_path, = Path('.data/pages-artifact').glob('*.tar')
output = Path('.data/public-frame-import')
output.mkdir(parents=True, exist_ok=True)
with tarfile.open(archive_path) as archive:
    members = {member.name.removeprefix('./'): member for member in archive.getmembers() if member.isfile()}
    def content(name):
        return archive.extractfile(members[name]).read()
    assert json.loads(content('verification.json'))['commit'] == commit
    manifest_bytes = content('portal-checker/bundle/manifest.json')
    assert manifest_bytes == Path('public/portal-checker/bundle/manifest.json').read_bytes()
    manifest = json.loads(manifest_bytes)
    names = ['index.html', 'workspace-entry.js', 'workspace-readiness.js', 'app.js', 'verification.json', 'portal-live.js', 'portal-runtime.js',
             'frame-interval-display.js', 'frame-interval-worked.js', 'main-checker-sw.js',
             'workspace.css', 'worked.css', 'portal-checker/bundle/manifest.json', 'portal-checker/bundle/worker.mjs']
    names += ['portal-checker/bundle/' + name for name in manifest['files']]
    expected = {name: hashlib.sha256(content(name)).hexdigest() for name in names}

# Allow a bounded propagation delay after normal Pages deployment. Each pass
# must match the complete set; no mixed-release response can pass.
for attempt in range(1, 7):
    actual = {}
    for name in names:
        request = urllib.request.Request(root + name, headers={'Cache-Control': 'no-cache'})
        with urllib.request.urlopen(request, timeout=30) as response:
            assert response.status == 200
            actual[name] = hashlib.sha256(response.read()).hexdigest()
    if actual == expected:
        break
    if attempt < 6:
        time.sleep(10)
assert actual == expected, 'Live critical bytes differ from this normal Pages artifact.'
record = {'commit': commit, 'release_run': os.environ['RELEASE_RUN'], 'replay_run': os.environ['GITHUB_RUN_ID'], 'phase': phase,
          'pages_tar_sha256': hashlib.sha256(archive_path.read_bytes()).hexdigest(),
          'files': actual, 'attempts': attempt, 'passed': True}
(output / ('live-binding-' + phase + '.json')).write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'commit': commit, 'phase': phase, 'files': len(actual), 'passed': True}))
