"""Bind the deployed release checkers and browser entry points to the Pages build."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
import tarfile
import time
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

base = "https://caoalex-s.github.io/CV2011-Structural-Explorer/"
release = os.environ["RELEASE_SHA"]
phase = sys.argv[1]
assert phase in {"before", "after"}
archive_path, = Path(".data/pages-artifact").glob("*.tar")
expected = {}
with tarfile.open(archive_path) as archive:
    for entry in archive.getmembers():
        name = entry.name.removeprefix("./")
        if not entry.isfile():
            continue
        parts = Path(name).parts
        checker = len(parts) >= 3 and parts[0] == "portal-checker" and parts[1] in {"bundle", "hinge", "inclined-release"}
        browser = len(parts) == 1 and (name.endswith((".js", ".css")) or name in {"index.html", "verification.json"})
        if not (checker or browser):
            continue
        content = archive.extractfile(entry).read()
        if checker:
            assert content == (Path("public") / name).read_bytes(), name
        if name == "verification.json":
            assert json.loads(content)["commit"] == release
        expected[name] = sha256(content).hexdigest()
for bundle in ["bundle", "hinge", "inclined-release"]:
    folder = Path("public/portal-checker") / bundle
    for asset in folder.iterdir():
        assert asset.relative_to("public").as_posix() in expected, asset
assert {"index.html", "portal-runtime.js", "main-checker-sw.js", "verification.json"} <= expected.keys()

def live_hash(name):
    request = Request(base + name, headers={"Cache-Control": "no-cache"})
    for attempt in range(5):
        try:
            with urlopen(request, timeout=45) as response:
                assert response.status == 200 and response.url == base + name, name
                return name, sha256(response.read()).hexdigest()
        except (URLError, TimeoutError) as error:
            print(f"{name}: attempt {attempt + 1}: {error}", flush=True)
            if isinstance(error, HTTPError) and error.code not in {429, 500, 502, 503, 504}:
                raise
            if attempt == 4:
                raise
            time.sleep(2 ** (attempt + 1))

with ThreadPoolExecutor(max_workers=2) as pool:
    actual = dict(pool.map(live_hash, expected))
assert actual == expected, [name for name in expected if expected[name] != actual[name]]
report = {"commit": release, "pages_run": os.environ["PAGES_RUN"], "phase": phase,
          "archive_sha256": sha256(archive_path.read_bytes()).hexdigest(), "files": actual}
output = Path(".data/student-results")
output.mkdir(parents=True, exist_ok=True)
(output / f"published-binding-{phase}.json").write_text(json.dumps(report, indent=2))
print(f"Verified {len(actual)} published files {phase} the drawing replay.")
