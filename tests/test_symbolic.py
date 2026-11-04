"""Check parametric expressions away from their generating numerical inputs."""
import unittest

import sympy as sp

from server.worked import worked_solution
from test_verifier import beam


class SymbolicTests(unittest.TestCase):
    def test_uniform_load_shows_arithmetic_and_short_trace(self):
        model = beam()
        model["loads"][0].update(kind="distributed", t=0, fy=-5, qEnd=-5)
        result = worked_solution({"model": model, "section": 0.5}, verify=False)
        moment = result["selected"][2]
        self.assertIn(r"\left(5\right)", moment["substitutionLatex"])
        self.assertIn(r"\left(8\right)^{2}", moment["substitutionLatex"])
        self.assertIn(r"\times", moment["substitutionLatex"])
        self.assertEqual(moment["exact"], "40")
        peak = next(item for item in result["quantities"]["summaries"][0]["extrema"] if item["kind"] == "absolute")
        self.assertEqual(peak["coordinate"]["symbolicLatex"], r"\frac{L}{2}")
        self.assertTrue(peak["isStationary"])
        self.assertIn(r"\loadsymbol{0}{}", peak["governing"]["symbolicLatex"])

    def test_central_force_retains_load_length_and_rigidity(self):
        result = worked_solution({"model": beam(), "section": 0.5}, verify=False)
        load, length, rigidity = sp.symbols("load0 L EI")
        moment = sp.sympify(result["selected"][2]["symbolicExact"])
        displacement = sp.sympify(result["selected"][4]["symbolicExact"])
        coordinates = {sp.Symbol("a_load"): length/2, sp.Symbol("x_s"): length/2}
        self.assertEqual(sp.expand(moment.subs(coordinates)-load*length/4), 0)
        self.assertEqual(sp.expand(displacement.subs(coordinates)+1000*load*length**3/(48*rigidity)), 0)
        self.assertEqual(result["selected"][4]["symbolicUnit"], "m")
        self.assertIn(r"\loadsymbol{0}{}", result["pieces"][0]["forces"][-1]["symbolicLatex"])

    def test_point_force_coordinates_remain_independent_across_regimes(self):
        model = beam()
        model["loads"][0]["label"] = "F_A"
        for location, section, force in [(0.25, 0.6, -30), (0.75, 0.4, -15),
                                         (0.5, 0.5, 0), (0.25, 0.7, 20),
                                         (0, 0.5, -20), (1, 1, -20)]:
            model["loads"][0].update(t=location, fy=force)
            result = worked_solution({"model": model, "section": section}, verify=False)
            values = {"L": 8, "EI": 20000, "a_load": 8*sp.Rational(str(location)),
                      "x_s": 8*sp.Rational(str(section)), "load0": -force}
            for row in result["selected"]:
                expression = sp.sympify(row["symbolicExact"])
                substituted = expression.subs({symbol: values[str(symbol)] for symbol in expression.free_symbols})
                self.assertEqual(sp.cancel(substituted-sp.sympify(row["exact"])), 0)
            if 0 < location < 1:
                self.assertIn("a_load", result["selected"][2]["symbolicExact"])
                self.assertIn("x_s", result["selected"][2]["symbolicExact"])
                self.assertIn(r"\loadsymbol{0}{}", result["pieces"][0]["forces"][-1]["symbolicLatex"])
                self.assertIn("a_load", result["momentArea"][0]["equation"]["symbolicExact"])
                self.assertIn("x_s", result["virtual"]["result"]["symbolicExact"])

    def test_point_force_formulas_predict_other_coordinates_in_each_regime(self):
        for first, second in [((0.25, 0.6), (0.35, 0.8)),
                              ((0.75, 0.4), (0.65, 0.2))]:
            model = beam()
            model["loads"][0].update(t=first[0], fy=-12)
            original = worked_solution({"model": model, "section": first[1]}, verify=False)
            model["loads"][0].update(t=second[0], fy=-31)
            model["nodes"][1]["x"] = 12
            model["members"][0]["EI"] = 30000
            changed = worked_solution({"model": model, "section": second[1]}, verify=False)
            values = {"L": 12, "EI": 30000, "a_load": 12*sp.Rational(str(second[0])),
                      "x_s": 12*sp.Rational(str(second[1])), "load0": 31}
            pairs = list(zip(original["selected"], changed["selected"]))
            pairs += [(original["virtual"]["result"], changed["virtual"]["result"])]
            pairs += [(original["momentArea"][i]["equation"], changed["momentArea"][i]["equation"]) for i in range(4)]
            for formula, actual in pairs:
                expression = sp.sympify(formula["symbolicExact"])
                prediction = expression.subs({symbol: values[str(symbol)] for symbol in expression.free_symbols})
                self.assertEqual(sp.cancel(prediction-sp.sympify(actual["exact"])), 0)

    def test_mixed_load_formulas_predict_a_different_beam_in_the_same_family(self):
        model = beam()
        model["supports"][0]["t"], model["supports"][1]["t"] = 0.2, 0.8
        model["loads"][0].update(fx=9, fy=-20, t=0.3)
        model["loads"] += [
            {**model["loads"][0], "id":"couple", "kind":"moment", "t":0.7, "mz":-13},
            {**model["loads"][0], "id":"intensity", "kind":"distributed", "t":0.1, "end":0.9, "fy":-2, "qEnd":-7},
        ]
        original = worked_solution({"model":model,"section":0.6}, verify=False)
        model["nodes"][1]["x"] = 12
        model["members"][0]["EI"] = 30000
        model["loads"][0].update(fx=15, fy=-28)
        model["loads"][1]["mz"] = -19
        model["loads"][2].update(fy=-3, qEnd=-9)
        changed = worked_solution({"model":model,"section":0.6}, verify=False)
        values = {sp.Symbol(key):value for key,value in {
            "L":12,"EI":30000,"load0x":15,"load0y":-28,"load1":19,"load2a":3,"load2b":9,
        }.items()}
        for symbolic, numeric in zip(original["selected"], changed["selected"]):
            self.assertEqual(sp.cancel(sp.sympify(symbolic["symbolicExact"]).subs(values)-sp.sympify(numeric["exact"])), 0)
        self.assertIn("not a theorem for all parameter values", original["symbolicScope"])

    def test_clockwise_couple_uses_positive_named_magnitude_with_correct_sign(self):
        model = beam()
        model["loads"][0].update(kind="moment", mz=-30, label="M_0")
        result = worked_solution({"model":model,"section":0.25}, verify=False)
        moment, length = sp.symbols("load0 L")
        self.assertEqual(sp.cancel(sp.sympify(result["equilibrium"][3]["symbolicExact"])-moment/length), 0)
        self.assertEqual(sp.cancel(sp.sympify(result["equilibrium"][4]["symbolicExact"])+moment/length), 0)


if __name__ == "__main__":
    unittest.main()
