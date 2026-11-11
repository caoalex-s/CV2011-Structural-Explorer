"""Read-only identity gates for one published-portal browser check.

Reuse the accepted normal-origin artifact/deployment verification pattern.
No source build, runtime execution, repository mutation, or deployment occurs.
"""
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import urllib.error
import urllib.request
import zipfile

MAIN = 'e36129aad36bca41a024004fa83a556257d2440b'
RUN = 42950864611
ROOT = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/'
API_ROOT = 'https://api.github.com/repos/caoalex-s/CV2011-Structural-Explorer'
HEADERS = {'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'], 'Accept': 'application/vnd.github+json'}
OUTPUT = Path('.data/portal-https')
OUTPUT.mkdir(parents=True, exist_ok=True)
LIVE_PATHS = ['index.html', 'verification.json', 'app.js', 'theme.css', 'style.css', 'workspace.css',
    'portal-checker/index.html', 'portal-checker/verification.json', 'portal-checker/app.js',
    'portal-checker/theme.css', 'portal-checker/style.css', 'portal-checker/workspace.css',
    'portal-checker/portal-live.js', 'portal-checker/portal-runtime.js', 'portal-checker/portal-candidate.js',
    'portal-checker/model-evidence.js', 'portal-checker/exact-cut-adapter.js', 'portal-checker/engine.js',
    'portal-checker/isolation-sw.js'] + ['portal-checker/bundle/' + name for name in
    ['manifest.json', 'worker.mjs', 'checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def api(path):
    with urllib.request.urlopen(urllib.request.Request(API_ROOT + path, headers=HEADERS), timeout=30) as response:
        return json.load(response)

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None

def download_artifact(artifact_id):
    """Never forward the repository credential to a signed blob URL."""
    request = urllib.request.Request(API_ROOT + f'/actions/artifacts/{artifact_id}/zip', headers=HEADERS)
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=30) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code != 302:
            raise
        with urllib.request.urlopen(error.headers['Location'], timeout=60) as response:
            return response.read()

def deployment_state(binding):
    assert api('/branches/main')['commit']['sha'] == MAIN
    run = api(f'/actions/runs/{RUN}')
    assert run['head_sha'] == MAIN and run['head_branch'] == 'main' and run['workflow_id'] == 404253700
    assert run['event'] == 'push' and run['run_attempt'] == 1
    assert run['status'] == 'completed' and run['conclusion'] == 'success'
    jobs = api(f'/actions/runs/{RUN}/jobs')['jobs']
    assert {job['name']: job['conclusion'] for job in jobs} == {'verify': 'success', 'deploy': 'success'}
    latest = api('/deployments?environment=github-pages&per_page=5')[0]
    assert latest['id'] == binding['deployment_id'] and latest['sha'] == MAIN
    statuses = api(f'/deployments/{latest["id"]}/statuses')
    assert statuses[0]['state'] == 'success' and str(RUN) in statuses[0]['log_url']
    environment = api('/environments/github-pages')
    policies = api('/environments/github-pages/deployment-branch-policies')
    assert environment == binding['environment'] and policies == binding['policies']
    return {'run': run, 'jobs': jobs, 'deployment': latest, 'statuses': statuses}

def native_file(name, expected):
    """Read actual HTTPS bytes outside any service-worker-controlled browser."""
    request = urllib.request.Request(ROOT + name, headers={'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(request, timeout=30) as response:
        body = response.read()
        record = {'path': name, 'status': response.status, 'sha256': sha(body), 'bytes': len(body),
                  'content_type': response.headers.get('Content-Type')}
        assert response.status == 200 and sha(body) == expected, name
        return record

assert sys.platform == 'linux' and os.environ['GITHUB_ACTIONS'] == 'true'
assert os.environ['GITHUB_RUN_ATTEMPT'] == '1'
assert os.environ['GITHUB_REF'] == 'refs/heads/codex/portal-https-e36129a'
binding = json.loads(Path('qa/portal-published/binding.json').read_bytes())
assert binding['approved'] is True and binding['human_approval_reference'].strip()
assert binding['deployed_main'] == MAIN and binding['normal_run_id'] == RUN
assert binding['target_url'] == ROOT + 'portal-checker/'
assert binding['live_read_paths'] == LIVE_PATHS
expected_changes = {'.github/workflows/portal-https-once.yml', 'qa/portal-published/binding.json',
                    'qa/portal-published/browser-test.mjs', 'qa/portal-published/verify-binding.py'}
changed = subprocess.check_output(['git', 'diff', '--name-only', MAIN, 'HEAD'], text=True).splitlines()
assert set(changed) == expected_changes
assert set(binding['runner_source_hashes']) == expected_changes - {'qa/portal-published/binding.json'}
for name, expected in binding['runner_source_hashes'].items():
    assert sha(Path(name).read_bytes()) == expected

state = deployment_state(binding)
if sys.argv[1:] == ['--after']:
    state['live_verification'] = native_file('verification.json', binding['artifact_file_hashes']['verification.json'])
    (OUTPUT / 'after-state.json').write_text(json.dumps(state, indent=2) + '\n')
    print('Publication identity unchanged after the bounded browser test.')
    sys.exit(0)
assert not sys.argv[1:]
artifacts = api(f'/actions/runs/{RUN}/artifacts')['artifacts']
assert len(artifacts) == 1
artifact = artifacts[0]
assert artifact['id'] == binding['artifact_id'] and artifact['name'] == 'github-pages' and not artifact['expired']
assert artifact['digest'] == 'sha256:' + binding['artifact_zip_sha256']
zip_bytes = download_artifact(artifact['id'])
assert sha(zip_bytes) == binding['artifact_zip_sha256']
with zipfile.ZipFile(io.BytesIO(zip_bytes)) as archive:
    assert archive.namelist() == ['artifact.tar']
    tar_bytes = archive.read('artifact.tar')
assert sha(tar_bytes) == binding['artifact_tar_sha256']
bodies = {}
with tarfile.open(fileobj=io.BytesIO(tar_bytes), mode='r:') as archive:
    for member in archive:
        path = PurePosixPath(member.name)
        assert not path.is_absolute() and '..' not in path.parts and '\\' not in member.name
        if member.isdir():
            continue
        assert member.isfile() and str(path) not in bodies
        bodies[str(path)] = archive.extractfile(member).read()
hashes = {name: sha(body) for name, body in bodies.items()}
assert hashes == binding['artifact_file_hashes']
assert json.loads(bodies['verification.json'])['commit'] == MAIN
assert json.loads(bodies['verification.json'])['lean'] == 'checked'
assert bodies['app.js'] == bodies['portal-checker/app.js']
assert b'href="portal-checker/"' in bodies['index.html']
assert b'href="../"' in bodies['portal-checker/index.html']
manifest_path = 'portal-checker/bundle/manifest.json'
assert hashes[manifest_path] == binding['manifest_sha256'] == 'fd0b16743f2107bb897fb6f6dca58374e3bbc6187848c8fd6c9b6cbd789d40c7'
manifest = json.loads(bodies[manifest_path])
assert binding['wasm_sha256'] == manifest['files']['checker.wasm'] == '8efdf2e865e7bc64d8eba43eb38df904cc3d913031ae7d5b0ff53e51c7664e2f'
for name, expected in manifest['files'].items():
    assert hashes['portal-checker/bundle/' + name] == expected
assert hashes['portal-checker/bundle/worker.mjs'] == manifest['workerSha256']
live = [native_file(name, hashes[name]) for name in binding['live_read_paths']]
assert api('/branches/main')['commit']['sha'] == MAIN
state.update(artifact=artifact, artifact_file_hashes=hashes, live=live,
             test_head=os.environ['GITHUB_SHA'], test_run=os.environ['GITHUB_RUN_ID'])
(OUTPUT / 'binding-verification.json').write_text(json.dumps(state, indent=2) + '\n')
print('Verified successful normal deployment, exact artifact, shared workspace, and live HTTPS bytes.')
