"""Verify a public CI archive and stage its immutable static checker assets.

Run from the repository root with the archive path, expected ZIP SHA-256 and
compilation source commit. This performs byte verification only, never Lean or
WASM execution. Final browser checks and independent review remain separate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('archive', type=Path)
parser.add_argument('archive_sha256')
parser.add_argument('source_commit')
args = parser.parse_args()
def digest(data):
    return hashlib.sha256(data).hexdigest()
assert digest(args.archive.read_bytes()) == args.archive_sha256
prefix = '.data/live-portal-build/'

with zipfile.ZipFile(args.archive) as archive:
    receipt_bytes = archive.read(prefix + 'receipt.json')
    receipt = json.loads(receipt_bytes)
    generic = receipt.get('mode') == 'frame'
    abi_path = Path('qa/general-frame/abi.c' if generic else 'qa/live-portal/abi.c')
    assert receipt['commit'] == args.source_commit
    assert receipt['repeatability'] and receipt['comparison']['equal']
    assert receipt['cleanup']['removed']
    # Stage proved, reproducible bytes so the final workspace can test them.
    # A failed build-time browser run stays in the manifest provenance and
    # must be resolved by the separate installed-bundle CI before acceptance.
    build_browser_passed = receipt.get('runtime_gate_passed') is True
    manifests = [json.loads(archive.read(prefix + f'pass-{number}/manifest.json')) for number in (1, 2)]
    assert manifests[0] == manifests[1]
    checked_files = 0
    for number, manifest in enumerate(manifests, 1):
        assert digest(archive.read(prefix + f'pass-{number}/manifest.json')) == receipt[f'manifest_{number}_sha256']
        for layer, files in manifest['layers'].items():
            if layer == 'lean_sources_and_generated_C':
                continue
            for name, expected in files.items():
                assert digest(archive.read(prefix + f'pass-{number}/files/' + name)) == expected, name
                checked_files += 1

    # All current formal sources and ABI/worker inputs must remain the same as
    # the source commit actually used by the compiler, including bridge imports.
    source_paths = ['proofs', str(abi_path), 'qa/live-portal/worker.mjs']
    if generic:
        source_paths.extend(receipt['frame_sources'])
    subprocess.run(['git', 'diff', '--exit-code', args.source_commit, '--', *source_paths], check=True)
    for path in [abi_path, Path('qa/live-portal/worker.mjs')]:
        assert digest(path.read_bytes()) == receipt['files'][path.as_posix()]
    checker_module = 'RationalFrameWire' if generic else 'PortalChecker'
    assert digest(archive.read(prefix + checker_module + '.c')) == receipt['generated_modules_1'][checker_module]['c_sha256']
    audit = archive.read(prefix + ('frame-axiom-audit.json' if generic else 'axiom-audit.json'))
    assert json.loads(audit)['passed'] is True
    assert digest(audit) == receipt['frame_proof_audit_sha256' if generic else 'proof_audit_sha256']

    bundle = Path('public/portal-checker/bundle')
    bundle.mkdir(parents=True, exist_ok=True)
    files = {}
    asset_names = ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']
    if generic:
        asset_names.extend(['frame-rational.js', 'model-evidence.js', 'frame-candidate.js', 'frame-packet.js', 'frame-result.js'])
    for name in asset_names:
        relative = '.data/wasm-build/canonical/assets/' + name
        data = archive.read(prefix + 'pass-2/files/' + relative)
        files[name] = digest(data)
        assert files[name] == receipt['artifact_hashes'][relative]
        (bundle / name).write_bytes(data)
    worker = Path('qa/live-portal/worker.mjs').read_bytes()
    (bundle / 'worker.mjs').write_bytes(worker)
    # Use the committed text bytes used by Linux CI. Windows generators may
    # leave CRLF in a worktree even when Git's declared storage format is LF.
    proof_files = {}
    proof_names = sorted(path.name for path in Path('proofs').glob('*.lean')) if generic else [
        'PortalChecker.lean', 'PortalTables.lean', 'PortalSoundness.lean', 'PortalFramePilot.lean']
    proof_names.extend(['lean-toolchain', 'lake-manifest.json'])
    for name in proof_names:
        committed = subprocess.run(['git', 'show', args.source_commit + ':proofs/' + name],
                                   capture_output=True, check=True).stdout
        assert (Path('proofs') / name).read_bytes().replace(b'\r\n', b'\n') == committed
        proof_files[name] = digest(committed)
    manifest = {
        'status': 'proved-compiled', 'theorem': 'RationalFrameSoundness.acceptance_actual_frame' if generic else 'PortalSoundness.acceptance_actual_portal',
        'sourceCommit': receipt['commit'], 'pins': receipt['pins'],
        'frameSemantics': 'affine-vertical-v1' if generic else None,
        'buildManifests': [receipt['manifest_1_sha256'], receipt['manifest_2_sha256']],
        'stabilityWitness': 'RationalFrame.Stability.checked_unique' if generic else 'PortalSoundness.fixed_inverse',
        'groupedReactions': 'RationalFrame.Reactions.checked_grouped_reactions' if generic else 'PortalSoundness.accepted_grouped_reactions',
        'files': files, 'proofFiles': proof_files, 'workerSha256': digest(worker),
        'abiSha256': digest(abi_path.read_bytes()),
        'axiomAuditSha256': digest(audit),
        'buildArchiveSha256': args.archive_sha256, 'buildReceiptSha256': digest(receipt_bytes),
        'buildBrowserPassed': build_browser_passed,
        'trust': 'Pinned Lean 4.19/C/Emscripten compilation, runtime, decoder and input binding. No kernel invocation per edit.',
    }
    (bundle / 'manifest.json').write_bytes((json.dumps(manifest, indent=2) + '\n').encode('utf-8'))
    print(json.dumps({'verified_archived_files': checked_files, 'artifact': files['checker.wasm'],
                      'manifest': digest((bundle / 'manifest.json').read_bytes()),
                      'browser_status': 'Requires final CI browser check and independent review.'}))
