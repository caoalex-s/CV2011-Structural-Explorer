"""Bind a browser-only CI retry to diagnostic 2's immutable build and proofs.

Run from the repository root after downloading the two fixed archives into
.data/browser-replay. This verifies saved evidence; it does not rerun Lean or
claim that the earlier failed browser run passed.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import zipfile

assert sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true'
root = Path.cwd()
folder = root / '.data/browser-replay'
compiled_commit = '038b0a48c95022647af26fd5dd6165abf5a92c8f'
expected_archives = {
    'compiled.zip': 'b343cb5a0483c7a53085ba154b3b1ee5ae4442044a321186bf84180fd24cbe57',
    'proof.zip': '2fc507bf895616251d72706eb9091a13b469a98ad6c22dcbc7f467785de1e12f',
}


def digest(content):
    return hashlib.sha256(content).hexdigest()


def save(relative, content):
    destination = (root / relative).resolve()
    assert destination.is_relative_to(root)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(content)


for name, expected in expected_archives.items():
    assert digest((folder / name).read_bytes()) == expected, name

with zipfile.ZipFile(folder / 'compiled.zip') as archive:
    prefix = '.data/live-portal-build/'
    receipt = json.loads(archive.read(prefix + 'receipt.json'))
    assert receipt['commit'] == compiled_commit
    assert receipt['repeatability'] is True and receipt['comparison']['equal'] is True
    manifests = []
    for index in [1, 2]:
        content = archive.read(prefix + f'pass-{index}/manifest.json')
        assert digest(content) == receipt[f'manifest_{index}_sha256']
        manifest = json.loads(content)
        manifests.append(manifest)
        for layer, files in manifest['layers'].items():
            if layer == 'lean_sources_and_generated_C':
                assert files == receipt[f'generated_modules_{index}']
                continue
            for relative, expected in files.items():
                assert digest(archive.read(prefix + f'pass-{index}/files/' + relative)) == expected
    assert manifests[0] == manifests[1]
    # Preserve the executable producer and decoder sources. Browser harness
    # expectations may change without rebuilding these unchanged bytes.
    for mapping in ['frame_sources', 'inclined_sources']:
        for relative, expected in receipt[mapping].items():
            assert digest((root / relative).read_bytes()) == expected, relative
    for relative in ['qa/inclined-frame/abi.c', 'qa/inclined-frame/worker.mjs',
                     'qa/inclined-frame/build-worker-modules.mjs']:
        assert digest((root / relative).read_bytes()) == receipt['files'][relative]
    bundle_prefix = 'public/portal-checker/bundle/'
    manifest_bytes = archive.read(bundle_prefix + 'manifest.json')
    bundle_manifest = json.loads(manifest_bytes)
    assert bundle_manifest['sourceCommit'] == compiled_commit
    for name, expected in bundle_manifest['proofFiles'].items():
        assert digest((root / 'proofs' / name).read_bytes()) == expected, name
    for name, expected in bundle_manifest['files'].items():
        content = archive.read(bundle_prefix + name)
        assert digest(content) == expected
        save(bundle_prefix + name, content)
    worker = archive.read(bundle_prefix + 'worker.mjs')
    assert digest(worker) == bundle_manifest['workerSha256']
    save(bundle_prefix + 'worker.mjs', worker)
    save(bundle_prefix + 'manifest.json', manifest_bytes)

with zipfile.ZipFile(folder / 'proof.zip') as archive:
    for name in archive.namelist():
        if name.startswith('inclined-native/') or name in [
                'axiom-audit.json', 'frame-axiom-audit.json', 'inclined-report-axiom-audit.json']:
            assert not name.endswith('/')
            save('.data/live-portal/' + name, archive.read(name))

record = {'compiled_run': 43804308191, 'compiled_commit': compiled_commit,
          'workspace_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
          'archive_sha256': expected_archives, 'bundle_sha256': digest(manifest_bytes),
          'scope': 'Browser-only retry with verified unchanged compiled bytes and archived proof evidence; no new proof build or deployment.'}
save('.data/browser-replay/reuse-receipt.json', (json.dumps(record, indent=2) + '\n').encode())
print(json.dumps(record))
