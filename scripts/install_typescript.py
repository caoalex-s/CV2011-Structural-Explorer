"""Install the pinned TypeScript compiler into ignored project tooling."""
from pathlib import Path
import tarfile
import urllib.request

root = Path(__file__).resolve().parents[1]
folder = root / ".tools" / "typescript"
folder.mkdir(parents=True, exist_ok=True)
archive = folder / "typescript.tgz"
urllib.request.urlretrieve("https://registry.npmjs.org/typescript/-/typescript-5.9.3.tgz", archive)
with tarfile.open(archive) as package:
    package.extractall(folder, filter="data")
print("Pinned TypeScript compiler installed under .tools/typescript")
