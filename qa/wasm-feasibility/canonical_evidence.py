"""Exact build-file manifests and workspace-scoped cleanup for Linux CI."""
import hashlib
import json
from pathlib import Path
import shutil
import sys


def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_cleanup_target(target, workspace):
    """Allow only the literal canonical directory beneath the resolved workspace.

    Resolving both the target and its lexical parent also rejects redirected
    ancestors. This validation performs no deletion and can be tested locally.
    """
    expected = workspace.resolve() / ".data/wasm-build/canonical"
    if target.absolute() != expected or target.resolve() != expected or target.is_symlink():
        raise ValueError("Refusing cleanup outside the exact canonical build directory")
    return expected


def collect_manifest(workspace, work, canonical, generated_modules):
    """Hash effective source/header inputs and the objects/archives actually linked."""
    runtime = canonical / "runtime"
    libuv = runtime / "libuv/src/libuv"
    layers = {}

    def record(name, paths):
        files = sorted({path for path in paths if path.is_file()})
        if not files:
            raise ValueError("Missing evidence layer: " + name)
        layers[name] = {str(path.relative_to(workspace)): file_hash(path) for path in files}

    source_files = [path for path in (work / "lean/src").rglob("*")
                    if path.suffix in (".h", ".cpp", ".c")]
    source_files += [path for directory in (libuv / "src", libuv / "include")
                     for path in directory.rglob("*") if path.suffix in (".h", ".c")]
    source_files += [libuv / "CMakeLists.txt"]
    record("runtime_sources", source_files)
    layers["lean_sources_and_generated_C"] = generated_modules
    record("generated_C_files", (canonical / "generated").glob("*.c"))
    record("effective_headers", list((runtime / "include").rglob("*.h")) +
           list((work / "lean/src/include").rglob("*.h")) + [runtime / "githash.h"])
    record("runtime_objects", (runtime / "runtime/CMakeFiles/leanrt.dir").rglob("*.o"))
    record("libuv_objects", (libuv / "CMakeFiles/uv_a.dir").rglob("*.o"))
    record("checker_objects", (canonical / "objects").glob("*.o"))
    record("archives", [canonical / "checker-core.a", runtime / "lib/lean/libleanrt.a", libuv / "libuv.a"])
    record("final_assets", (canonical / "assets").iterdir())
    return {"workspace": str(workspace), "canonical": str(canonical), "layers": layers}


def archive_pass(workspace, destination, manifest):
    """Preserve every hashed input/output byte before the next clean pass."""
    destination.mkdir(parents=True)
    for layer, files in manifest["layers"].items():
        if layer == "lean_sources_and_generated_C":
            continue
        for relative, expected in files.items():
            source = workspace / relative
            target = destination / "files" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            if file_hash(target) != expected:
                raise ValueError("Archived bytes differ: " + relative)
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


def clean_archived_build(target, workspace, archive, manifest):
    """Delete only after verifying a separate, complete first-pass archive."""
    if sys.platform != "linux":
        raise RuntimeError("Build cleanup is Linux CI only")
    resolved = validate_cleanup_target(target, workspace)
    if archive.resolve().is_relative_to(resolved):
        raise ValueError("Evidence archive cannot be inside the cleanup target")
    if json.loads((archive / "manifest.json").read_text()) != manifest:
        raise ValueError("Archived manifest changed")
    checked = 0
    for layer, files in manifest["layers"].items():
        if layer == "lean_sources_and_generated_C":
            continue
        for relative, expected in files.items():
            if file_hash(archive / "files" / relative) != expected:
                raise ValueError("Incomplete or changed archive: " + relative)
            checked += 1
    shutil.rmtree(resolved)
    if resolved.exists():
        raise RuntimeError("Canonical build directory was not removed")
    return {"removed_absolute_path": str(resolved), "archive_verified_files": checked,
            "archive": str(archive.resolve()), "removed": True}


def compare_passes(first, second):
    """Report exact equality and the first differing layer, without normalization."""
    assert first["workspace"] == second["workspace"] and first["canonical"] == second["canonical"]
    assert list(first["layers"]) == list(second["layers"])
    differences = {}
    for layer, left in first["layers"].items():
        right = second["layers"][layer]
        changed = [name for name in sorted(left.keys() | right.keys()) if left.get(name) != right.get(name)]
        if changed:
            differences[layer] = changed
    return {"equal": not differences, "first_differing_layer": next(iter(differences), None),
            "differences": differences, "compared_layers": list(first["layers"])}
