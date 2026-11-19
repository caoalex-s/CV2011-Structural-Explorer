"""Compile the checked-in Lean import closure in dependency order on Linux."""
from pathlib import Path
import subprocess
import sys

built = set()
def compile_module(name):
    path = Path(name + ".lean")
    if name in built or not path.is_file():
        return
    built.add(name)
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("import "):
            for dependency in line.split()[1:]:
                compile_module(dependency)
    options = ["-c", name + ".c"] if name.startswith("InclinedRelease") else []
    if not Path(name + ".olean").exists() or options:
        subprocess.run(["lean", *options, "-o", name + ".olean", str(path)], check=True)

for target in sys.argv[1:]:
    compile_module(target)
