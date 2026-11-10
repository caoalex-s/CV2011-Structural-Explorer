"""Validation tests; no local build, runtime or build-output cleanup occurs."""
import os
from pathlib import Path
import tempfile
import unittest

from canonical_evidence import validate_cleanup_target, compare_passes


class CanonicalEvidenceChecks(unittest.TestCase):
    def test_only_exact_workspace_target_is_allowed(self):
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary).resolve()
            canonical = workspace / ".data/wasm-build/canonical"
            self.assertEqual(validate_cleanup_target(canonical, workspace), canonical)
            for candidate in (workspace, workspace.parent, canonical.parent,
                              workspace / ".data/wasm-gate", canonical / "nested",
                              workspace.parent / "canonical"):
                with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                    validate_cleanup_target(candidate, workspace)

    @unittest.skipIf(os.name == "nt", "Symlink fixture is checked in Linux CI")
    def test_redirected_ancestor_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            workspace, elsewhere = base / "workspace", base / "elsewhere"
            workspace.mkdir()
            elsewhere.mkdir()
            (workspace / ".data").symlink_to(elsewhere, target_is_directory=True)
            with self.assertRaises(ValueError):
                validate_cleanup_target(workspace / ".data/wasm-build/canonical", workspace)

    def test_comparison_identifies_first_layer_without_ignoring_binary_changes(self):
        first = {"workspace": "root", "canonical": "root/build", "layers": {
            "headers": {"lean.h": "same"}, "objects": {"x.o": "first"},
            "final_assets": {"checker.wasm": "first"}}}
        second = {**first, "layers": {"headers": {"lean.h": "same"},
                  "objects": {"x.o": "second"}, "final_assets": {"checker.wasm": "second"}}}
        self.assertTrue(compare_passes(first, first)["equal"])
        result = compare_passes(first, second)
        self.assertFalse(result["equal"])
        self.assertEqual(result["first_differing_layer"], "objects")
        self.assertIn("checker.wasm", result["differences"]["final_assets"])


if __name__ == "__main__":
    unittest.main()
