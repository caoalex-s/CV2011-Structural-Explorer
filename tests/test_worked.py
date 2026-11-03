"""Verify course methods, concentrated-action limits, and certificate rejection."""
import os
import unittest

import sympy as sp

from test_verifier import beam
from server.verifier import reference
from server.worked import at, build_polynomials, lean_executable, verify_source, worked_solution


class WorkedTests(unittest.TestCase):
    def test_point_load_methods_agree(self):
        result = worked_solution({"model": beam(), "section": 0.5}, verify=False)
        self.assertEqual(result["selected"][-1]["exact"], "-32/3")
        self.assertEqual(result["virtual"]["result"]["exact"], "-32/3")
        self.assertEqual(len(result["pieces"]), 2)
        self.assertIn("continuity", result["proof"]["groups"])
        self.assertEqual(result["proof"]["status"], "not_run")

    def test_mixed_loads_overhang_and_reversed_pin(self):
        model = beam()
        model["supports"][0].update(t=0.2, kind="roller")
        model["supports"][1].update(t=0.8, kind="pin")
        model["loads"] += [
            {**model["loads"][0], "id": "q", "kind": "distributed", "t": 0.1, "end": 0.7, "fy": -2, "qEnd": -7},
            {**model["loads"][0], "id": "C", "kind": "moment", "t": 1, "mz": 13},
        ]
        model["loads"][0].update(fx=9, t=0)
        reference_beam = reference(model)
        pieces, _, _, _ = build_polynomials(reference_beam)
        for location in [sp.S.Zero, sp.Rational(4, 5), sp.Rational(8, 5), sp.Rational(16, 5), sp.Integer(8)]:
            values = reference_beam.values(location)
            for field, key in [("N", "normal"), ("V", "shear"), ("M", "moment")]:
                self.assertEqual(at(pieces, field, location), values[key])
            self.assertEqual(at(pieces, "v", location) * 1000, values["deflection"])
        result = worked_solution({"model": model, "section": 0.05}, verify=False)
        self.assertEqual(result["virtual"]["result"]["exact"], result["selected"][-1]["exact"])

    def test_couple_jump_and_continuous_slope(self):
        model = beam()
        model["loads"][0].update(kind="moment", mz=30)
        pieces, _, _, _ = build_polynomials(reference(model))
        x = sp.Symbol("x")
        self.assertEqual((pieces[1]["M"] - pieces[0]["M"]).subs(x, 4), -30)
        for field in ["v", "theta"]:
            self.assertEqual((pieces[1][field] - pieces[0][field]).subs(x, 4), 0)

    def test_unsupported_inputs_do_not_get_certificates(self):
        model = beam()
        model["nodes"][0]["joint"] = "pinned"
        with self.assertRaises(ValueError):
            worked_solution({"model": model}, verify=False)
        model = beam()
        model["loads"] *= 13
        with self.assertRaises(ValueError):
            worked_solution({"model": model}, verify=False)

    def test_lean_certificates_and_mutations(self):
        if not lean_executable():
            if os.environ.get("REQUIRE_LEAN"):
                self.fail("The required Lean executable is unavailable.")
            self.skipTest("Local Lean execution is disabled. CI runs this test.")
        for kind in ["force", "moment", "distributed"]:
            model = beam()
            model["loads"][0].update(kind=kind, mz=30, t=0 if kind == "distributed" else 0.5)
            result = worked_solution({"model": model, "section": 0.5})
            self.assertEqual(result["proof"]["status"], "checked", result["proof"].get("audit"))
        source = result["proof"]["source"]
        # Change the first displacement polynomial without changing its claims.
        corrupted = source.replace("def v0 : Poly := [", "def v0 : Poly := [(1 : Rat) + ", 1)
        self.assertEqual(verify_source(corrupted)["status"], "failed")
        self.assertEqual(verify_source(source + "\ntheorem false_claim : (1 : Rat) = 2 := by decide\n")["status"], "failed")


if __name__ == "__main__":
    unittest.main()
