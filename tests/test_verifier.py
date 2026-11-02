"""Independent exact-reference and access-control tests."""
import json
from pathlib import Path
import tempfile
import unittest

import sympy as sp

from server.verifier import parse_arithmetic, reference, check
from server.app import Store


def beam():
    return {"nodes": [{"id": "A", "x": 0, "y": 0}, {"id": "B", "x": 8, "y": 0}],
            "members": [{"id": "AB", "a": "A", "b": "B", "EA": 2000000, "EI": 20000}],
            "supports": [{"id": "S1", "member": "AB", "t": 0, "kind": "pin", "angle": 90},
                         {"id": "S2", "member": "AB", "t": 1, "kind": "roller", "angle": 90}],
            "loads": [{"id": "P", "member": "AB", "t": 0.5, "kind": "force", "fx": 0, "fy": -20, "mz": 0, "end": 1, "qEnd": -5}]}


class VerifierTests(unittest.TestCase):
    def test_reactions_and_point_deflection(self):
        result = reference(beam()).values(sp.Integer(4))
        self.assertEqual(result["reaction_left"], 10)
        self.assertEqual(result["moment"], 40)
        self.assertEqual(result["deflection"], sp.Rational(-32, 3))

    def test_uniform_load(self):
        model = beam()
        model["loads"][0].update(kind="distributed", t=0, fy=-5, qEnd=-5)
        result = reference(model).values(sp.Integer(4))
        self.assertEqual(result["deflection"], sp.Rational(-40, 3))
        self.assertEqual(result["reaction_left"], 20)

    def test_overhang_and_moment_jump(self):
        model = beam()
        model["supports"][0]["t"] = 0.2
        model["supports"][1]["t"] = 0.8
        model["loads"][0]["t"] = 1
        result = reference(model)
        self.assertEqual(result.reaction_left, sp.Rational(-20, 3))
        self.assertEqual(result.values(sp.Rational(32, 5))["moment"], -32)
        model = beam()
        model["loads"][0].update(kind="moment", mz=30)
        self.assertEqual(reference(model).values(sp.Integer(4))["moment"], -15)

    def test_safe_parser(self):
        self.assertEqual(parse_arithmetic("20*(8-4)/8"), 10)
        for expression in ["__import__('os').getcwd()", "(1).__class__", "2**10000000", "1/0", "[1]*5"]:
            with self.assertRaises((ValueError, SyntaxError)):
                parse_arithmetic(expression)

    def test_grading_units_and_sign(self):
        payload = {"model": beam(), "section": 0.5, "step": "reaction_left", "answer": "10", "units": "kN"}
        self.assertEqual(check(payload)["status"], "correct")
        payload.update(answer="10000", units="N")
        self.assertEqual(check(payload)["status"], "correct")
        payload.update(answer="-10", units="kN")
        self.assertEqual(check(payload)["category"], "opposite_sign")
        payload.update(answer="10", units="mm")
        self.assertEqual(check(payload)["category"], "unit_dimension")

    def test_nonfinite_and_unsupported_geometry(self):
        model = beam()
        model["loads"][0]["fy"] = float('nan')
        with self.assertRaises(ValueError):
            reference(model)
        model = beam()
        model["supports"][1]["angle"] = 45
        with self.assertRaises(ValueError):
            reference(model)

    def test_records_are_owned_and_idempotent(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).resolve().parents[1] / ".data") as folder:
            store = Store(folder)
            alice = store.issue("STUDENT-001")
            bob = store.issue("STUDENT-002")
            self.assertEqual(store.identity(alice), "STUDENT-001")
            self.assertEqual(store.identity(bob), "STUDENT-002")
            event = {"id": "attempt-1", "event": "submit", "courseId": "forged", "answer": "10"}
            store.record("STUDENT-001", event, {"status": "correct"})
            store.record("STUDENT-001", event, {"status": "incorrect"})
            self.assertEqual(len(store.records("STUDENT-001")), 1)
            self.assertEqual(store.records("STUDENT-002"), [])
            self.assertEqual(store.records()[0]["courseId"], "STUDENT-001")
            with self.assertRaises(ValueError):
                store.record("STUDENT-002", event, {})


if __name__ == "__main__":
    (Path(__file__).resolve().parents[1] / ".data").mkdir(exist_ok=True)
    unittest.main()
