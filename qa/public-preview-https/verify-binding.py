"""Read-only identity gates before the single approved public-origin browser test."""
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import urllib.error
import urllib.request
import zipfile

MAIN = 'a1271d30bcf02c14fdd0c6dbaf2a4f3bc69ac23d'
RUN = 42433321948
STAGING = 'eabc90e0a4a548b31a8d1f50f8dd1309336d272e'
CANDIDATE = '9c0a1ac36253f429fa4ba2908ca67dc03b7f7a5d'
TEST_HASH = '21ba3c59b5f2ff3d31d9eb9747adc19f1e2e043c272c350291a95e40f498034f'
LOCK_HASH = 'a15732280331bdee86122669c3d4a660fe4eac216ea11d2e7184ed8190cdfd86'
API_ROOT = 'https://api.github.com/repos/caoalex-s/CV2011-Structural-Explorer'
PUBLIC_ROOT = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/'
HEADERS = {'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN'], 'Accept': 'application/vnd.github+json'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def api(path):
    with urllib.request.urlopen(urllib.request.Request(API_ROOT + path, headers=HEADERS), timeout=30) as response:
        return json.load(response)

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, file, code, message, headers, new_url):
        return None

def download_artifact(artifact_id):
    """Keep the GitHub credential off the signed blob-download request."""
    request = urllib.request.Request(API_ROOT + f'/actions/artifacts/{artifact_id}/zip', headers=HEADERS)
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=30) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code != 302:
            raise
        with urllib.request.urlopen(error.headers['Location'], timeout=45) as response:
            return response.read()

# 1. Require the reviewed content identity and explicit approval for this deployment.
assert os.environ['GITHUB_ACTIONS'] == 'true' and os.environ['GITHUB_RUN_ATTEMPT'] == '1'
assert os.environ['GITHUB_REF'] == 'refs/heads/codex/checker-preview-https-a1271d30'
binding = json.loads(Path('qa/public-preview-https/binding.json').read_bytes())
assert binding['approved'] is True and binding['human_approval_reference'].strip()
assert binding['deployed_main'] == MAIN and binding['normal_run_id'] == RUN
assert binding['candidate_commit'] == CANDIDATE and binding['test_sha256'] == TEST_HASH
bundle = Path('.data/reviewed-bundle')
assert subprocess.check_output(['git', '-C', str(bundle), 'rev-parse', 'HEAD'], text=True).strip() == STAGING
reviewed = bundle / 'checker-preview-review'
lock_bytes = (reviewed / 'preview-file-manifest.json').read_bytes()
assert sha(lock_bytes) == LOCK_HASH and sha((reviewed / 'https-test.mjs').read_bytes()) == TEST_HASH
lock = json.loads(lock_bytes)
assert lock['candidate_commit'] == CANDIDATE
assert lock['target_url'] == PUBLIC_ROOT + 'checker-preview/64b31158/'

# 2. Bind to the successful normal run, current main, deployment, and retained artifact.
assert api('/branches/main')['commit']['sha'] == MAIN, 'Main changed before test.'
run = api(f'/actions/runs/{RUN}')
assert run['head_sha'] == MAIN and run['workflow_id'] == 404253700
assert run['event'] == 'workflow_dispatch' and run['run_attempt'] == 1
assert run['status'] == 'completed' and run['conclusion'] == 'success'
deployments = api('/deployments?environment=github-pages&per_page=5')
deployment = deployments[0]
assert deployment['id'] == binding['deployment_id'] and deployment['sha'] == MAIN
statuses = api(f'/deployments/{deployment["id"]}/statuses')
assert statuses[0]['state'] == 'success' and str(RUN) in statuses[0]['log_url']
artifacts = api(f'/actions/runs/{RUN}/artifacts')['artifacts']
assert len(artifacts) == 1
artifact = artifacts[0]
assert artifact['id'] == binding['artifact_id'] and artifact['name'] == 'github-pages'
assert artifact['digest'] == 'sha256:' + binding['artifact_zip_sha256'] and not artifact['expired']
archive_bytes = download_artifact(artifact['id'])
assert sha(archive_bytes) == binding['artifact_zip_sha256']

# 3. Check every uploaded body and derive the root-index assertion from the actual tar.
with zipfile.ZipFile(io.BytesIO(archive_bytes)) as archive:
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
        assert member.isfile()
        name = str(path)
        assert name not in bodies
        bodies[name] = archive.extractfile(member).read()
hashes = {name: sha(body) for name, body in bodies.items()}
assert hashes == binding['artifact_file_hashes']
for name, record in lock['files'].items():
    assert hashes['checker-preview/64b31158/' + name] == record['sha256']
assert hashes['index.html'] == binding['root_index_sha256']
verification = json.loads(bodies['verification.json'])
assert verification['commit'] == MAIN and verification['lean'] == 'checked'
if lock['baseline_index_sha256'] != hashes['index.html']:
    lock['baseline_index_sha256'] = hashes['index.html']
    lock_bytes = (json.dumps(lock, indent=2) + '\n').encode()
assert sha(lock_bytes) == binding['test_manifest_sha256'], 'Manifest must have its reviewed identity.'

# A native HTTPS read checks served proof metadata without registering any worker.
with urllib.request.urlopen(PUBLIC_ROOT + 'verification.json', timeout=30) as response:
    live_verification = response.read()
assert sha(live_verification) == hashes['verification.json']
assert api('/branches/main')['commit']['sha'] == MAIN
Path('.data/preview-lock.json').write_bytes(lock_bytes)
approval = dict(approved=True, candidate_commit=CANDIDATE, target_url=lock['target_url'],
                lock_sha256=sha(lock_bytes), human_approval_reference=binding['human_approval_reference'],
                deployed_main=MAIN, normal_run_id=RUN, artifact_id=artifact['id'])
Path('.data/publication-approval.json').write_text(json.dumps(approval))
Path('.data/binding-verification.json').write_text(json.dumps({
    'normal_run': RUN, 'deployed_main': MAIN, 'test_run': os.environ['GITHUB_RUN_ID'],
    'test_head': os.environ['GITHUB_SHA'], 'artifact': artifact, 'deployment_id': deployment['id'],
    'root_index_sha256': hashes['index.html'], 'file_hashes': hashes,
    'test_sha256': TEST_HASH, 'test_manifest_sha256': sha(lock_bytes),
}, indent=2) + '\n')
print('Verified successful deployment, exact artifact, preview bodies, and root-index binding.')
