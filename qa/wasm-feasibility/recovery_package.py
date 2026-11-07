"""Allowlisted public evidence packaging; no recursive workspace collection."""
import hashlib
import io
import json
from pathlib import PurePosixPath
import tarfile


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def validate_member_name(name):
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or "\\" in name or str(path) != name:
        raise ValueError("Unsafe archive member: " + name)


def verify_package(fileobj, index):
    """Require every indexed regular file exactly once and verify all bytes."""
    expected = index["members"]
    seen = set()
    with tarfile.open(fileobj=fileobj, mode="r:gz") as archive:
        for member in archive:
            validate_member_name(member.name)
            if not member.isfile() or member.name in seen:
                raise ValueError("Non-regular or repeated member: " + member.name)
            seen.add(member.name)
            if member.name == "package-index.json":
                expected_bytes = (json.dumps(index, indent=2) + "\n").encode()
                if archive.extractfile(member).read() != expected_bytes:
                    raise ValueError("Embedded package index differs")
                continue
            if member.name not in expected:
                raise ValueError("Unlisted archive member: " + member.name)
            record = expected[member.name]
            if member.size != record["bytes"]:
                raise ValueError("Member size differs: " + member.name)
            if sha256(archive.extractfile(member).read()) != record["sha256"]:
                raise ValueError("Member hash differs: " + member.name)
    if seen != set(expected) | {"package-index.json"}:
        raise ValueError("Missing archive members")
    return {"passed": True, "verified_members": len(expected),
            "all_regular_files": True, "exact_member_set": True}


def create_package(paths, destination, index_path):
    """Package only caller-supplied paths with caller-supplied expected hashes.

    Tar metadata is conventional; source and binary payload bytes are never
    normalized. The hidden .data component stays inside one visible tar.gz.
    """
    index = {"format": 1, "members": {}}
    for name, (path, expected_hash) in sorted(paths.items()):
        validate_member_name(name)
        if name == "package-index.json" or not path.is_file() or path.is_symlink():
            raise ValueError("Invalid package input: " + name)
        data = path.read_bytes()
        if sha256(data) != expected_hash:
            raise ValueError("Input hash differs: " + name)
        index["members"][name] = {"sha256": expected_hash, "bytes": len(data)}
    index_bytes = (json.dumps(index, indent=2) + "\n").encode()
    index_path.write_bytes(index_bytes)
    with tarfile.open(destination, "w:gz") as archive:
        for name in [*index["members"], "package-index.json"]:
            data = index_bytes if name == "package-index.json" else paths[name][0].read_bytes()
            if name != "package-index.json" and sha256(data) != index["members"][name]["sha256"]:
                raise ValueError("Input changed during packaging: " + name)
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    with destination.open("rb") as stream:
        preflight = verify_package(stream, index)
    preflight.update({"archive_sha256": sha256(destination.read_bytes()),
                      "index_sha256": sha256(index_bytes)})
    return preflight
