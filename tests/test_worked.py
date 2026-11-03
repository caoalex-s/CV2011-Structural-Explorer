"""Verify course methods, concentrated-action limits, and certificate rejection."""
import base64
import hashlib
import io
import json
import os
import unittest
import zipfile

import sympy as sp

from test_verifier import beam
from server.verifier import reference
from server.worked import at, build_polynomials, lean_executable, verify_source, worked_solution


class WorkedTests(unittest.TestCase):
    def test_point_load_methods_agree(self):
        result = worked_solution({"model": beam(), "section": 0.5}, verify=False)
        self.assertEqual(result["selected"][-1]["exact"], "-32/3")
        self.assertEqual(result["virtual"]["result"]["exact"], "32/3")
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
        self.assertEqual(sp.sympify(result["virtual"]["result"]["exact"]), -sp.sympify(result["selected"][-1]["exact"]))

    def test_couple_jump_and_continuous_slope(self):
        model = beam()
        model["loads"][0].update(kind="moment", mz=30)
        pieces, _, _, _ = build_polynomials(reference(model))
        x = sp.Symbol("x")
        self.assertEqual((pieces[1]["M"] - pieces[0]["M"]).subs(x, 4), -30)
        for field in ["v", "theta"]:
            self.assertEqual((pieces[1][field] - pieces[0][field]).subs(x, 4), 0)

    def test_latex_and_vscode_project_match_the_generated_solution(self):
        result = worked_solution({"model": beam(), "section": 0.5}, verify=False)
        displacement = result["selected"][-1]
        self.assertEqual(displacement["latex"], r"- \frac{32}{3}")
        self.assertEqual(result["selected"][-2]["labelLatex"], r"\theta")
        self.assertIn(r"\int_{0}^{4}", result["virtual"]["rows"][0]["equations"][-1]["labelLatex"])
        proof = result["proof"]
        with zipfile.ZipFile(io.BytesIO(base64.b64decode(proof["projectZip"]))) as archive:
            self.assertEqual(set(archive.namelist()), {
                "WorkedBeam.lean", "lean-toolchain", "lakefile.toml", "certificate.json", "README.md",
            })
            source = archive.read("WorkedBeam.lean")
            self.assertEqual(source.decode(), proof["source"])
            self.assertEqual(hashlib.sha256(source).hexdigest(), proof["sha256"])
            self.assertEqual(archive.read("lean-toolchain").decode().strip(), "leanprover/lean4:v4.19.0")
            metadata = json.loads(archive.read("certificate.json"))
            self.assertEqual(metadata["status"], "not_run")
            self.assertEqual(metadata["sha256"], proof["sha256"])

    def test_unsupported_inputs_do_not_get_certificates(self):
        model = beam()
        model["nodes"][0]["joint"] = "pinned"
        with self.assertRaises(ValueError):
            worked_solution({"model": model}, verify=False)
        model = beam()
        model["loads"] *= 13
        with self.assertRaises(ValueError):
            worked_solution({"model": model}, verify=False)

    def test_tutorial_load_sign_virtual_units_and_interval_constants(self):
        model = beam()
        model["loads"][0].update(kind="distributed", t=0, fy=-5, qEnd=-5)
        result = worked_solution({"model": model, "section": 0.5}, verify=False)
        self.assertEqual(result["pieces"][0]["forces"][0]["labelLatex"], "w(x)")
        self.assertEqual(result["pieces"][0]["forces"][0]["exact"], "5")
        self.assertEqual(result["virtual"]["rows"][0]["equations"][0]["unit"], "m")
        self.assertEqual(result["virtual"]["rows"][0]["equations"][1]["unit"], "m")
        self.assertEqual(result["virtual"]["result"]["exact"], "40/3")
        self.assertTrue(result["equilibrium"][3]["labelLatex"].startswith("B_{y}"))
        x = sp.Symbol("x")
        for index, piece in enumerate(result["pieces"]):
            constants = {sp.Symbol(f"C_{2*index+1}"): sp.sympify(result["constants"][2*index]["exact"]),
                         sp.Symbol(f"C_{2*index+2}"): sp.sympify(result["constants"][2*index+1]["exact"])}
            theta, v = [sp.sympify(row["exact"]) for row in piece["displacements"]]
            first, second = [sp.sympify(row["exact"]).subs(constants) for row in piece["integrations"]]
            self.assertEqual(sp.expand(first - model["members"][0]["EI"] * theta), 0)
            self.assertEqual(sp.expand(second - model["members"][0]["EI"] * v), 0)
            shear = sp.sympify(piece["forces"][2]["exact"])
            self.assertEqual(sp.diff(shear, x), -5)

    def test_tutorial_5_triangle_and_tutorial_8_clockwise_couple(self):
        # Tutorial 5 Q1: L=6 m, downward w=2x kN/m, A_y=12, B_y=24.
        model = beam()
        model["nodes"][1]["x"] = 6
        model["loads"][0].update(kind="distributed", t=0, fy=0, qEnd=-12)
        result = worked_solution({"model": model, "section": 0.5}, verify=False)
        self.assertEqual(result["equilibrium"][3]["exact"], "24")
        self.assertEqual(result["equilibrium"][4]["exact"], "12")
        x = sp.Symbol("x")
        self.assertEqual(sp.sympify(result["pieces"][0]["forces"][0]["exact"]), 2*x)
        self.assertEqual(sp.sympify(result["pieces"][0]["forces"][2]["exact"]), 12-x**2)
        self.assertEqual(sp.sympify(result["pieces"][0]["forces"][3]["exact"]), 12*x-x**3/3)
        # Tutorial 8 Q1: clockwise M0 at midspan gives theta_A=M0*L/(24EI).
        model = beam()
        model["loads"][0].update(kind="moment", mz=-30)
        result = worked_solution({"model": model, "section": 0}, verify=False)
        self.assertEqual(sp.sympify(result["selected"][-2]["exact"]), sp.Rational(30*8, 24*20000))

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
        # The displayed course load sign and downward virtual displacement
        # must also be rejected if their generated polynomial signs change.
        wrong_load = source.replace("def w0 : Poly := [", "def w0 : Poly := [(1 : Rat) + ", 1)
        self.assertEqual(verify_source(wrong_load)["status"], "failed")
        wrong_virtual = source.replace("def virtualm0 : Poly := [", "def virtualm0 : Poly := [(1 : Rat) + ", 1)
        self.assertEqual(verify_source(wrong_virtual)["status"], "failed")


if __name__ == "__main__":
    unittest.main()
