"""One Linux CI browser-only diagnostic of immutable recovered WASM bytes.

No Lean/Emscripten build command is present. Only the pinned browser test tools
are installed. Keep the original archive, selected raw assets and provenance.
"""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import time
import urllib.error
import urllib.request
import zipfile

from recovery_package import verify_package

ROOT = Path.cwd()
SOURCES = ROOT / 'qa/wasm-feasibility'
OUTPUT = ROOT / '.data/wasm-hosting'
TOOLS = ROOT / '.data/wasm-hosting-tools'
receipt = {'passed': False, 'stage': 'initialize', 'overall_gate_passed': False,
           'public_origin_verified': False, 'builds': 0}


def digest(data):
    return hashlib.sha256(data).hexdigest()


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, file, code, message, headers, new_url):
        return None


def github_get(url, token):
    """Never send the GitHub credential to the signed storage destination."""
    request = urllib.request.Request(url, headers={'Authorization': 'Bearer ' + token,
                                                  'Accept': 'application/vnd.github+json'})
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=45) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code != 302:
            raise
        with urllib.request.urlopen(error.headers['Location'], timeout=60) as response:
            return response.read()


def run(arguments, environment, timeout=300):
    print('+', ' '.join(map(str, arguments)), flush=True)
    subprocess.run(list(map(str, arguments)), check=True, env=environment, timeout=timeout)


def main():
    assert sys.platform == 'linux' and os.environ.get('GITHUB_ACTIONS') == 'true', 'Linux CI only'
    pin = json.loads((SOURCES / 'hosting-source.json').read_text())
    receipt['candidate_commit'] = os.environ['GITHUB_SHA']
    receipt['source'] = pin
    receipt['stage'] = 'verify-immutable-recovery'
    token = os.environ.pop('GH_TOKEN')
    url = 'https://api.github.com/repos/' + pin['repository'] + '/actions/artifacts/' + str(pin['artifact_id'])
    metadata = json.loads(github_get(url, token))
    assert metadata['id'] == pin['artifact_id'] and metadata['name'] == pin['artifact_name']
    assert not metadata['expired'] and metadata['workflow_run']['id'] == pin['run_id']
    assert metadata['workflow_run']['head_sha'] == pin['source_commit']
    assert metadata['digest'] == 'sha256:' + pin['outer_zip_sha256']
    data = github_get(url + '/zip', token)
    assert digest(data) == pin['outer_zip_sha256']
    (OUTPUT / 'source-artifact.zip').write_bytes(data)
    (OUTPUT / 'source-artifact-metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        tar_bytes = archive.read('recovered-evidence.tar.gz')
        index_bytes = archive.read('package-index.json')
    assert digest(tar_bytes) == pin['tar_sha256'] and digest(index_bytes) == pin['index_sha256']
    receipt['archive_verification'] = verify_package(io.BytesIO(tar_bytes), json.loads(index_bytes))
    assets = OUTPUT / 'assets'
    assets.mkdir()
    with tarfile.open(fileobj=io.BytesIO(tar_bytes), mode='r:gz') as archive:
        for name, expected in pin['final_assets'].items():
            member = 'files/.data/wasm-build/canonical/assets/' + name
            raw = archive.extractfile(member).read()
            assert len(raw) == expected['bytes'] and digest(raw) == expected['sha256']
            (assets / name).write_bytes(raw)
        for name in ('recovered-manifest.json', 'axiom-audit.json', 'receipt.json'):
            (OUTPUT / ('source-' + name)).write_bytes(archive.extractfile('evidence/' + name).read())
    assert digest((OUTPUT / 'source-recovered-manifest.json').read_bytes()) == pin['manifest_sha256']
    assert json.loads((OUTPUT / 'source-axiom-audit.json').read_text())['passed'] is True
    assert json.loads((OUTPUT / 'source-receipt.json').read_text())['commit'] == pin['source_commit']
    assert digest((SOURCES / 'isolation-sw.js').read_bytes()) == pin['shim_sha256']
    receipt['verified_assets'] = pin['final_assets']
    receipt['proof_provenance'] = 'Accepted recovery proof audit only; no Lean/compiler execution in this job.'

    # These tools are test-only. The token has already been removed from the environment.
    receipt['stage'] = 'install-pinned-browser'
    TOOLS.mkdir()
    environment = {**os.environ, 'PLAYWRIGHT_BROWSERS_PATH': str(TOOLS / 'browsers')}
    run(['npm', 'install', '--prefix', TOOLS, '--ignore-scripts', '--save-exact',
         'playwright@' + pin['playwright_version']], environment)
    run(['node', TOOLS / 'node_modules/playwright/cli.js', 'install', '--with-deps', 'chromium'], environment)
    shutil.copyfile(TOOLS / 'package-lock.json', OUTPUT / 'browser-package-lock.json')
    source_names = ['hosting-test.mjs', 'hosting-harness.mjs', 'hosting-worker.mjs', 'isolation-sw.js',
                    'hosting-source.json', 'hosting-diagnostic.py', 'coi-LICENSE']
    (OUTPUT / 'sources').mkdir()
    receipt['source_sha256'] = {}
    for name in source_names:
        raw = (SOURCES / name).read_bytes()
        receipt['source_sha256'][name] = digest(raw)
        (OUTPUT / 'sources' / name).write_bytes(raw)
    shutil.copyfile(SOURCES / 'hosting-test.mjs', TOOLS / 'hosting-test.mjs')
    receipt['stage'] = 'headerless-subpath-browser-test'
    run(['node', TOOLS / 'hosting-test.mjs', assets, SOURCES, OUTPUT], environment, timeout=240)
    receipt['browser'] = json.loads((OUTPUT / 'hosting-results.json').read_text())
    assert receipt['browser']['passed'] is True
    receipt['passed'] = True
    receipt['stage'] = 'synthetic-hosting-diagnostic-complete'
    receipt['trust_boundary'] = ('Trusted decoder/ABI, Lean compiler/runtime, loader and request binding, '
                                'plus the reviewed service-worker shim and browser isolation behavior. '
                                'Synthetic headerless host only; actual published origin remains unverified.')


if __name__ == '__main__':
    OUTPUT.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        main()
    except Exception as error:
        receipt['failure'] = str(error)
        raise
    finally:
        receipt['elapsed_seconds'] = time.monotonic() - started
        (OUTPUT / 'hosting-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
