"""Install the pinned browser renderer when npm is unavailable locally.

Verify the npm registry's SHA-512 integrity value before extracting the package.
No package lifecycle script or downloaded executable is run. Normal development
and CI can use `npm install --ignore-scripts` instead.
"""
import base64
import hashlib
import json
from pathlib import Path
import tarfile
import urllib.request


def main():
    root = Path(__file__).resolve().parents[1]
    version = json.loads((root / "package.json").read_text())["dependencies"]["katex"]
    with urllib.request.urlopen(f"https://registry.npmjs.org/katex/{version}", timeout=30) as response:
        metadata = json.load(response)
    with urllib.request.urlopen(metadata["dist"]["tarball"], timeout=30) as response:
        package = response.read()
    integrity = "sha512-" + base64.b64encode(hashlib.sha512(package).digest()).decode()
    if integrity != metadata["dist"]["integrity"]:
        raise ValueError("The KaTeX archive does not satisfy the registry integrity check.")
    archive_path = root / ".tools/katex.tgz"
    archive_path.parent.mkdir(exist_ok=True)
    archive_path.write_bytes(package)
    target = root / "node_modules/katex"
    target.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive_path) as archive:
        for member in archive.getmembers():
            if not member.name.startswith("package/"):
                raise ValueError("Unexpected archive member.")
            member.name = member.name.removeprefix("package/")
            archive.extract(member, target, filter="data")
    print(f"Installed KaTeX {version}; SHA-512 integrity verified; no lifecycle scripts run.")


if __name__ == "__main__":
    main()
