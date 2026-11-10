"""One CI-only canonical reproduction, exact prior-manifest match and delivery.

This driver reuses the accepted build functions unchanged. It does not run the
two-pass main() from gate.py. Runtime sources, settings and browser harness are
hash-bound to the accepted candidate; the only new behavior is recovery and
explicit evidence packaging.
"""
import io
import json
import os
from pathlib import Path
import shutil
import sys
import time
import urllib.error
import urllib.request
import zipfile

import gate as build
from canonical_evidence import collect_manifest, compare_passes
from recovery_package import create_package, sha256


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, file, code, message, headers, new_url):
        return None


def github_get(url, token):
    request = urllib.request.Request(url, headers={"Authorization": "Bearer " + token,
                                                  "Accept": "application/vnd.github+json"})
    try:
        with urllib.request.build_opener(NoRedirect).open(request, timeout=45) as response:
            return response.read()
    except urllib.error.HTTPError as error:
        if error.code != 302:
            raise
        # Never forward the GitHub credential to the signed storage URL.
        with urllib.request.urlopen(error.headers["Location"], timeout=60) as response:
            return response.read()


def get_baseline():
    pin = json.loads((build.SOURCES / "recovery-baseline.json").read_text())
    for name, expected in pin["unchanged_source_sha256"].items():
        assert build.digest(build.SOURCES / name) == expected, "Changed accepted source: " + name
    api = "https://api.github.com/repos/" + pin["repository"] + "/actions/artifacts/" + str(pin["artifact_id"])
    token = os.environ.pop("GH_TOKEN")
    metadata = json.loads(github_get(api, token))
    assert metadata["id"] == pin["artifact_id"] and metadata["name"] == pin["artifact_name"]
    assert not metadata["expired"] and metadata["workflow_run"]["id"] == pin["run_id"]
    assert metadata["workflow_run"]["head_sha"] == pin["source_commit"]
    assert metadata["digest"] == "sha256:" + pin["archive_sha256"]
    data = github_get(api + "/zip", token)
    assert sha256(data) == pin["archive_sha256"]
    (build.OUTPUT / "prior-canonical.zip").write_bytes(data)
    (build.OUTPUT / "prior-artifact-metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    archive = zipfile.ZipFile(io.BytesIO(data))
    first, second = archive.read("pass-1/manifest.json"), archive.read("pass-2/manifest.json")
    assert first == second and sha256(first) == pin["manifest_sha256"]
    (build.OUTPUT / "expected-manifest.json").write_bytes(first)
    previous = json.loads(archive.read("receipt.json"))
    assert previous["commit"] == pin["source_commit"] and previous["repeatability"] is True
    assert previous["pins"] == build.PINS
    assert build.digest(build.ROOT / "proofs/lake-manifest.json") == previous["dependency_lock_sha256"]
    assert build.digest(build.OUTPUT / "axiom-audit.json") == previous["proof_audit_sha256"]
    build.receipt["baseline"] = pin
    return pin, json.loads(first), previous


def setup_same_toolchain(previous):
    """Use the accepted setup sequence and canonical source/tool paths."""
    build.WORK.mkdir(parents=True)
    build.receipt["commit"] = build.run(["git", "rev-parse", "HEAD"], capture=True)
    build.receipt["runner"] = {key: os.environ.get(key) for key in ("ImageOS", "ImageVersion", "RUNNER_ARCH")}
    build.receipt["host_tools"] = {name: build.run([name, "--version"], capture=True).splitlines()[0]
                                   for name in ("cmake", "python3", "node", "npm", "git")}
    for name, url in (("lean", "https://github.com/leanprover/lean4.git"),
                      ("emsdk", "https://github.com/emscripten-core/emsdk.git")):
        build.checkout(url, build.PINS[name], build.WORK / name)
    build.run(["./emsdk", "install", build.PINS["emscripten"]], cwd=build.WORK / "emsdk")
    build.run(["./emsdk", "activate", build.PINS["emscripten"]], cwd=build.WORK / "emsdk")
    settings = build.run(["bash", "-c", 'source .data/wasm-build/emsdk/emsdk_env.sh >/dev/null 2>&1; '
                          'cd proofs; lake env python3 -c '
                          '\'import json,os; print(json.dumps({k:os.environ[k] for k in '
                          '["PATH","LEAN_PATH","EMSDK","EM_CONFIG","EMSDK_NODE"] if k in os.environ}))\''], capture=True)
    environment = {**os.environ, **json.loads(settings), "SOURCE_DATE_EPOCH": "1746057600"}
    environment["EM_CONFIG"] = str(build.WORK / "emsdk/.emscripten")
    environment["LEAN_PATH"] = str(build.ROOT / "proofs") + ":" + environment["LEAN_PATH"]
    native_lean = build.run(["elan", "which", "lean"], cwd=build.ROOT / "proofs", env=environment, capture=True)
    build.receipt["native_lean"] = native_lean
    build.receipt["native_lean_sha256"] = build.digest(Path(native_lean))
    build.receipt["lean_version"] = build.run([native_lean, "--version"], env=environment, capture=True)
    build.receipt["emcc_version"] = build.run(["emcc", "--version"], env=environment, capture=True)
    build.receipt["emscripten_config_sha256"] = build.digest(Path(environment["EM_CONFIG"]))
    build.receipt["emsdk_manifest_sha256"] = build.digest(build.WORK / "emsdk/emscripten-releases-tags.json")
    for key in ("native_lean_sha256", "lean_version", "emcc_version", "emscripten_config_sha256", "emsdk_manifest_sha256"):
        assert build.receipt[key] == previous[key], "Changed toolchain identity: " + key
    build.receipt["source_date_epoch"] = environment["SOURCE_DATE_EPOCH"]
    assert build.receipt["source_date_epoch"] == previous["source_date_epoch"]
    build.receipt["toolchain_cache_policy"] = previous["toolchain_cache_policy"]
    return environment, native_lean


def recover():
    assert sys.platform == "linux" and os.environ.get("GITHUB_ACTIONS") == "true", "Linux CI only"
    pin, expected, previous = get_baseline()
    environment, native_lean = setup_same_toolchain(previous)
    assert str(build.ROOT) == expected["workspace"] and str(build.CANONICAL) == expected["canonical"]
    assert not build.CANONICAL.exists(), "Recovery requires a clean canonical directory"
    build.CANONICAL.mkdir()
    build.receipt["stage"] = "single-clean-build"
    build.save_receipt()
    generated = build.generate_c(environment, native_lean, 1)
    assets = build.build_artifact(1, environment, generated)
    manifest = collect_manifest(build.ROOT, build.WORK, build.CANONICAL, build.receipt["generated_modules_1"])
    manifest_bytes = (json.dumps(manifest, indent=2) + "\n").encode()
    (build.OUTPUT / "recovered-manifest.json").write_bytes(manifest_bytes)
    build.receipt["stage"] = "compare-with-accepted-canonical"
    build.receipt["comparison"] = compare_passes(expected, manifest)
    build.save_receipt()
    assert build.receipt["comparison"]["equal"], "Recovery manifest mismatch: " + str(build.receipt["comparison"])
    assert sha256(manifest_bytes) == pin["manifest_sha256"], "Full manifest identity differs"
    assert build.digest(assets / "checker.wasm") == pin["wasm_sha256"]
    build.receipt["repeatability"] = True
    build.receipt["manifest_sha256"] = sha256(manifest_bytes)
    build.receipt["artifact_hashes"] = manifest["layers"]["final_assets"]
    build.receipt["proof_audit_sha256"] = build.digest(build.OUTPUT / "axiom-audit.json")
    build.receipt["stage"] = "fresh-browser-check"
    build.save_receipt()
    browser = build.OUTPUT / "browser"
    browser.mkdir()
    build.run(["npm", "install", "--prefix", browser, "--ignore-scripts", "--save-exact",
               "playwright@" + build.PINS["playwright"]])
    build.run(["node", browser / "node_modules/playwright/cli.js", "install", "--with-deps", "chromium"])
    shutil.copyfile(build.SOURCES / "browser-test.mjs", browser / "browser-test.mjs")
    build.run(["node", browser / "browser-test.mjs", assets, build.SOURCES])
    shutil.copyfile(build.CANONICAL / "browser-results.json", build.OUTPUT / "browser-results.json")
    build.receipt["browser"] = json.loads((build.OUTPUT / "browser-results.json").read_text())
    build.receipt["browser_package_lock_sha256"] = build.digest(browser / "package-lock.json")
    assert build.receipt["browser"]["passed"] is True
    build.receipt["passed"] = True
    build.receipt["runtime_gate_passed"] = True
    build.receipt["stage"] = "recovered-build-and-browser-complete"
    build.receipt["delivery"] = "pending package and independent post-download verification"
    return manifest


def package_recovery(manifest):
    paths = {}
    for layer, files in manifest["layers"].items():
        if layer != "lean_sources_and_generated_C":
            for relative, expected in files.items():
                member = "files/" + relative
                if member in paths:
                    assert paths[member][1] == expected
                paths[member] = (build.ROOT / relative, expected)
    roots = [build.ROOT / "proofs", build.ROOT / "proofs/.lake/packages/batteries",
             Path(build.receipt["native_lean"]).parent.parent / "src/lean"]
    for name, hashes in manifest["layers"]["lean_sources_and_generated_C"].items():
        relative = Path(*name.split(".")).with_suffix(".lean")
        source = next(root / relative for root in roots if (root / relative).is_file())
        paths["lean-sources/" + name + ".lean"] = (source, hashes["source_sha256"])
    evidence = ["prior-canonical.zip", "prior-artifact-metadata.json", "expected-manifest.json",
                "recovered-manifest.json", "receipt.json", "axiom-audit.json", "axioms.log",
                "SmokeChecker.c", "browser-results.json", "browser/package-lock.json"]
    for name in evidence:
        path = build.OUTPUT / name
        paths["evidence/" + name] = (path, build.digest(path))
    # Only tracked public QA sources, selected explicitly; no hidden-workspace scan.
    sources = ["gate.py", "canonical_evidence.py", "SmokeChecker.lean", "SmokeSoundness.lean", "abi.c",
               "browser-test.mjs", "worker.mjs", "harness.mjs", "audit_axioms.py", "recover_artifact.py",
               "recovery_package.py", "recovery-baseline.json", "test_recovery_package.py"]
    for name in sources:
        path = build.SOURCES / name
        paths["sources/" + name] = (path, build.digest(path))
    required = {"files/" + relative for relative in manifest["layers"]["final_assets"]}
    assert required <= paths.keys() and any("/runtime/include/" in name for name in paths)
    preflight = create_package(paths, build.OUTPUT / "recovered-evidence.tar.gz", build.OUTPUT / "package-index.json")
    preflight.update({"candidate_commit": build.receipt["commit"], "required_assets": sorted(required),
                      "post_download_verification": "pending independent reader", "overall_gate_passed": False})
    (build.OUTPUT / "package-preflight.json").write_text(json.dumps(preflight, indent=2) + "\n")


if __name__ == "__main__":
    started = time.monotonic()
    try:
        recovered = recover()
    except Exception as error:
        build.receipt["failure"] = str(error)
        raise
    finally:
        build.receipt["elapsed_seconds"] = time.monotonic() - started
        build.save_receipt()
    package_recovery(recovered)
