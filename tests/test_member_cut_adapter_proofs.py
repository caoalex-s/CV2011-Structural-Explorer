"""Generate a synthetic exact adapter artifact and check it on Linux CI."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class MemberCutAdapterProofChecks(unittest.TestCase):
    def test_generated_adapter_fixture(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "GeneratedMemberCut.lean"
            generated = subprocess.run(
                ["node", "scripts/generate-member-cut-fixture.mjs", str(source)], cwd=ROOT,
                capture_output=True, text=True, timeout=30, check=False,
            )
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            checked = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=ROOT / "proofs",
                capture_output=True, text=True, timeout=120, check=False,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
