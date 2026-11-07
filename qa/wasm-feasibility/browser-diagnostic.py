"""CI-only execution of one immutable existing WASM artifact; never rebuild it.

The pinned archive and every selected asset are checked before extraction.
The existing browser harness is hash-checked and runs exactly once. Browser
success cannot change the failed repeatability or overall feasibility status.
"""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
import zipfile

ROOT = Path.cwd()
SOURCES = ROOT / "qa/wasm-feasibility"
OUTPUT = ROOT / ".data/wasm-browser-diagnostic"
TOOLS = ROOT / ".data/wasm-browser-tools"
receipt = {"stage": "initialize", "browser_passed": False, "repeatability": False,
           "gate_passed": False, "feasibility_gate_passed": False}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(arguments, **options):
    """Record commands without exposing the token-bearing environment."""
    print("+", " ".join(map(str, arguments)), flush=True)
    return subprocess.run(list(map(str, arguments)), check=True, text=True, **options)


def save_receipt():
    (OUTPUT / "diagnostic-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, file, code, message, headers, new_url):
        return None


def github_get(url, token):
    """Keep GitHub credentials off the signed artifact storage request."""
    request = urllib.request.Request(url, headers={"Authorization": "Bearer " + token,
                                                  "Accept": "application/vnd.github+json"})
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=45) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code != 302:
            raise
        with urllib.request.urlopen(error.headers["Location"], timeout=60) as response:
            return response.read()


def main():
    assert sys.platform == "linux" and os.environ.get("GITHUB_ACTIONS") == "true", "Linux CI only"
    manifest_bytes = (SOURCES / "browser-source-manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    receipt["manifest_sha256"] = digest(manifest_bytes)
    receipt["diagnostic_source_commit"] = os.environ["GITHUB_SHA"]
    receipt["source_identity"] = {key: manifest[key] for key in
                                  ("repository", "run_id", "artifact_id", "source_commit", "archive_sha256")}
    receipt["stage"] = "retrieve-and-verify"
    save_receipt()
    token = os.environ["GH_TOKEN"]
    api_root = "https://api.github.com/repos/" + manifest["repository"]
    artifact_url = api_root + "/actions/artifacts/" + str(manifest["artifact_id"])
    metadata = json.loads(github_get(artifact_url, token))
    assert metadata["id"] == manifest["artifact_id"] and metadata["name"] == manifest["artifact_name"]
    assert not metadata["expired"]
    assert metadata["workflow_run"]["id"] == manifest["run_id"]
    assert metadata["workflow_run"]["head_sha"] == manifest["source_commit"]
    assert metadata["digest"] == "sha256:" + manifest["archive_sha256"]
    archive_bytes = github_get(artifact_url + "/zip", token)
    assert digest(archive_bytes) == manifest["archive_sha256"], "Archive digest mismatch"
    (OUTPUT / "source-artifact.zip").write_bytes(archive_bytes)
    (OUTPUT / "source-artifact-metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    archive = zipfile.ZipFile(io.BytesIO(archive_bytes))
    # Extract only explicitly named, verified files, never the other build's assets.
    for name, expected in manifest["entries"].items():
        destination = (OUTPUT / name).resolve()
        assert destination.is_relative_to(OUTPUT.resolve())
        assert archive.namelist().count(name) == 1
        data = archive.read(name)
        assert digest(data) == expected, "Source archive entry mismatch: " + name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    for group in ("harness_sha256", "proof_source_sha256"):
        for name, expected in manifest[group].items():
            assert digest((SOURCES / name).read_bytes()) == expected, "Changed source: " + name
    build_receipt = json.loads((OUTPUT / "receipt.json").read_text())
    proof_audit = json.loads((OUTPUT / "axiom-audit.json").read_text())
    assert build_receipt["commit"] == manifest["source_commit"] and build_receipt["passed"] is False
    assert build_receipt["artifact_hashes"] != build_receipt["repeat_hashes"]
    assert proof_audit["passed"] is True
    receipt["verified_assets"] = {name: value for name, value in manifest["entries"].items()
                                  if name.startswith("assets-1/")}
    receipt["proof_provenance"] = {"source_commit": manifest["source_commit"],
        "source_sha256": manifest["proof_source_sha256"], "saved_audit": proof_audit,
        "note": "Prior CI proof/audit only; no Lean compiler or kernel invoked by this diagnostic."}
    receipt["stage"] = "install-pinned-browser"
    save_receipt()
    TOOLS.mkdir(parents=True)
    environment = {key: value for key, value in os.environ.items() if key != "GH_TOKEN"}
    environment["PLAYWRIGHT_BROWSERS_PATH"] = str(TOOLS / "browsers")
    run(["npm", "install", "--prefix", TOOLS, "--ignore-scripts", "--save-exact",
         "playwright@" + manifest["playwright_version"]], env=environment)
    run(["node", TOOLS / "node_modules/playwright/cli.js", "install", "--with-deps", "chromium"],
        env=environment)
    for source, target in ((TOOLS / "package-lock.json", "browser-package-lock.json"),
                           (TOOLS / "node_modules/playwright-core/browsers.json", "browser-versions.json")):
        shutil.copyfile(source, OUTPUT / target)
    receipt["browser_package_version"] = json.loads(
        (TOOLS / "node_modules/playwright/package.json").read_text())["version"]
    assert receipt["browser_package_version"] == manifest["playwright_version"]
    receipt["installed_browser_binaries"] = {
        str(path.relative_to(TOOLS)): digest(path.read_bytes())
        for path in sorted((TOOLS / "browsers").rglob("*"))
        if path.is_file() and path.name in ("chrome", "headless_shell", "chrome-headless-shell")}
    assert receipt["installed_browser_binaries"], "No pinned browser executable found"
    receipt["stage"] = "browser-harness"
    save_receipt()
    # Copy the unchanged driver beside its pinned test dependency for ESM imports.
    shutil.copyfile(SOURCES / "browser-test.mjs", TOOLS / "browser-test.mjs")
    assert digest((TOOLS / "browser-test.mjs").read_bytes()) == manifest["harness_sha256"]["browser-test.mjs"]
    run(["node", TOOLS / "browser-test.mjs", OUTPUT / "assets-1", SOURCES], env=environment, timeout=180)
    receipt["browser_result"] = json.loads((OUTPUT / "browser-results.json").read_text())
    assert receipt["browser_result"]["passed"] is True
    receipt["browser_passed"] = True
    receipt["stage"] = "browser-diagnostic-complete"
    # Deliberately leave repeatability and both overall gate fields false.


if __name__ == "__main__":
    OUTPUT.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    try:
        main()
    except Exception as error:
        receipt["failure"] = str(error)
        raise
    finally:
        receipt["elapsed_seconds"] = time.monotonic() - started
        save_receipt()
