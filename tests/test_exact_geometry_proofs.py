"""Generate and kernel-check fixed synthetic adapter geometry expressions."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class ExactGeometryProofChecks(unittest.TestCase):
    def test_synthetic_adapter_expressions(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "GeneratedExactGeometry.lean"
            generated = subprocess.run(
                ["node", "scripts/generate-exact-geometry-fixture.mjs", str(source)],
                cwd=ROOT, capture_output=True, text=True, timeout=30, check=False,
            )
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            checked = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=ROOT / "proofs",
                capture_output=True, text=True, timeout=120, check=False,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
