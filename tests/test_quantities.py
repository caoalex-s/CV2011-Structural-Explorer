"""Analytical extrema, one-sided point values, and whole-interval enclosures."""
import unittest

import sympy as sp

from server.quantities import bernstein_coefficients, curve_range
from server.worked import worked_solution
from test_verifier import beam

X = sp.Symbol("x")


def summary(result, field):
    return next(row for row in result["quantities"]["summaries"] if row["field"] == field)


def extremum(result, field, kind="absolute"):
    return next(row for row in summary(result, field)["extrema"] if row["kind"] == kind)


class QuantityTests(unittest.TestCase):
    def assert_encloses(self, row, expected):
        lower, upper = sp.Rational(row["lower"]), sp.Rational(row["upper"])
        self.assertTrue(bool(lower <= expected))
        self.assertTrue(bool(expected <= upper))
        self.assertLess(float(upper-lower), max(1, abs(float(expected))) * 1e-7)

    def test_central_force_extrema_and_both_shear_limits(self):
        result = worked_solution({"model": beam(), "section": 0.3}, verify=False)
        for field, expected in [("M", 40), ("theta", 4), ("v", sp.Rational(32, 3))]:
            self.assert_encloses(extremum(result, field), expected)
        midpoint = [row for row in result["quantities"]["points"] if row["x"] == "4"]
        self.assertEqual([row["values"]["V"] for row in midpoint], [10, -10])
        self.assertEqual([row["side"] for row in midpoint], ["-", "+"])
        self.assertTrue(all(row["values"]["theta"] == 0 for row in midpoint))
        self.assertTrue(any("Selected section" in row["labels"] and row["x"] == "12/5"
                            for row in result["quantities"]["points"]))
        self.assertIn("key_points", result["proof"]["groups"])

    def test_udl_angle_and_displacement_maxima(self):
        model = beam()
        model["loads"][0].update(kind="distributed", t=0, fy=-5, qEnd=-5)
        result = worked_solution({"model": model}, verify=False)
        self.assert_encloses(extremum(result, "M"), 40)
        self.assert_encloses(extremum(result, "theta"), sp.Rational(16, 3))
        self.assert_encloses(extremum(result, "v"), sp.Rational(40, 3))
        self.assert_encloses(extremum(result, "v", "minimum"), -sp.Rational(40, 3))
        self.assertEqual(extremum(result, "v")["x"], "4")

    def test_tutorial_triangle_irrational_critical_position(self):
        model = beam()
        model["nodes"][1]["x"] = 6
        model["loads"][0].update(kind="distributed", t=0, fy=0, qEnd=-12)
        result = worked_solution({"model": model}, verify=False)
        peak = extremum(result, "M")
        self.assert_encloses(peak, 16*sp.sqrt(3))
        self.assertAlmostEqual(peak["xApprox"], float(2*sp.sqrt(3)), places=8)
        self.assertFalse(peak["exact"])
        self.assertEqual(summary(result, "M")["roots"][0]["coordinateLatex"], r"2 \sqrt{3}")
        self.assertTrue(peak["coordinate"]["approximate"])
        self.assertTrue(peak["compactSubstitution"]["approximate"])
        self.assertIn("x_{c}", peak["compactSubstitution"]["symbolicLatex"])

    def test_couple_preserves_two_moment_limits_and_common_rotation(self):
        model = beam()
        model["loads"][0].update(kind="moment", mz=-30)
        result = worked_solution({"model": model}, verify=False)
        middle = [point for point in result["quantities"]["points"] if point["x"] == "4"]
        self.assertEqual([point["values"]["M"] for point in middle], [-15, 15])
        self.assertEqual(middle[0]["values"]["theta"], middle[1]["values"]["theta"])
        self.assert_encloses(extremum(result, "M"), 15)

    def test_unloaded_beam_has_constant_zero_ranges(self):
        model = beam()
        model["loads"] = []
        result = worked_solution({"model": model}, verify=False)
        for row in result["quantities"]["summaries"]:
            self.assertEqual(row["roots"], [])
            for peak in row["extrema"]:
                self.assertEqual((peak["lower"], peak["upper"]), ("0", "0"))
                self.assertTrue(peak["exact"])
                self.assertTrue(peak["plateau"])

    def test_bernstein_identity_and_coverage_at_stationary_and_repeated_roots(self):
        expression = (X-1)**4 - 2*(X-1)**2
        result = curve_range(((sp.S.Zero, sp.Integer(2), expression),))
        self.assertEqual(result["minimum"]["value"], -1)
        self.assertEqual(result["maximum"]["value"], 0)
        self.assertEqual(result["cells"][0]["start"], 0)
        self.assertEqual(result["cells"][-1]["end"], 2)
        for left, right in zip(result["cells"], result["cells"][1:]):
            self.assertEqual(left["end"], right["start"])
        t = sp.Symbol("t")
        for cell in result["cells"]:
            start, end = cell["start"], cell["end"]
            coefficients = bernstein_coefficients(expression, start, end)
            reconstruction = sum(value*sp.binomial(5, i)*t**i*(1-t)**(5-i)
                                 for i, value in enumerate(coefficients))
            self.assertEqual(sp.expand(reconstruction-expression.subs(X, start+(end-start)*t)), 0)
        repeated = curve_range(((sp.S.Zero, sp.Integer(2), (X-1)**3),))
        self.assertEqual(repeated["roots"][0]["multiplicity"], 2)
        self.assertEqual(repeated["minimum"]["value"], -1)
        self.assertEqual(repeated["maximum"]["value"], 1)


if __name__ == "__main__":
    unittest.main()
