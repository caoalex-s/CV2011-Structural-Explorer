"""Check only the shipped public portal instance on the Linux CI runner."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@unittest.skipUnless(os.environ.get("REQUIRE_LEAN") == "1", "Lean checks run in Linux CI")
class PortalFramePilotChecks(unittest.TestCase):
    def test_shipped_instance_and_false_claim(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(os.environ.get("PORTAL_PILOT_OUTPUT", temporary)).resolve()
            generated = subprocess.run(
                ["node", "scripts/portal-frame-pilot.mjs", str(output)], cwd=ROOT,
                capture_output=True, text=True, timeout=30, check=False,
            )
            self.assertEqual(generated.returncode, 0, generated.stdout + generated.stderr)
            source = (output / "PortalFramePilot.lean").read_text(encoding="utf-8")
            names = re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE)
            self.assertTrue(names)
            self.assertEqual(len(names), len(set(names)))
            audited = source + "\n" + "\n".join(
                f"#print axioms PortalFramePilot.{name}" for name in names
            ) + "\n"
            audited_path = output / "AuditedPortalFramePilot.lean"
            audited_path.write_text(audited, encoding="utf-8")
            checked = subprocess.run(
                ["lake", "env", "lean", str(audited_path)], cwd=ROOT / "proofs",
                capture_output=True, text=True, timeout=180, check=False,
            )
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            seen = set()
            for line in checked.stdout.splitlines():
                match = re.search(r"'PortalFramePilot\.(\w+)' (.*)", line)
                if not match:
                    continue
                name, report = match.groups()
                self.assertIn(name, names)
                self.assertNotIn(name, seen)
                seen.add(name)
                if "does not depend on any axioms" in report:
                    continue
                axioms = re.search(r"depends on axioms:\s*\[([^]]*)\]", report)
                self.assertIsNotNone(axioms, line)
                actual = {item.strip() for item in axioms.group(1).split(",") if item.strip()}
                self.assertFalse(actual - ALLOWED_AXIOMS, line)
            self.assertEqual(seen, set(names), checked.stdout)
            (output / "axioms.log").write_text(checked.stdout, encoding="utf-8")

            # A wrong downward-column direction must fail at the theorem site.
            negative_path = output / "RejectedPortalFramePilot.lean"
            negative_path.write_text(source + "\nexample : (PortalFramePilot.model.member 2).orientation.sine = 1 := by\n"
                "  norm_num [PortalFramePilot.model, PortalFramePilot.sine]\n", encoding="utf-8")
            rejected = subprocess.run(
                ["lake", "env", "lean", str(negative_path)], cwd=ROOT / "proofs",
                capture_output=True, text=True, timeout=180, check=False,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("unsolved goals", rejected.stdout + rejected.stderr)
            receipt = {
                "status": "checked-public-portal-instance", "commit": os.environ.get("GITHUB_SHA"),
                "run_id": os.environ.get("GITHUB_RUN_ID"),
                "generated_source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "audited_source_sha256": hashlib.sha256(audited.encode()).hexdigest(),
                "theorems": names, "axioms": sorted(ALLOWED_AXIOMS), "wrong_cd_direction": "rejected",
                "scope": "Finite contract, geometry, load work and local recovery; no global solution or stability certificate.",
            }
            (output / "kernel-check.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
            print(f"Checked {len(names)} portal theorems and rejected the wrong CD direction.")
