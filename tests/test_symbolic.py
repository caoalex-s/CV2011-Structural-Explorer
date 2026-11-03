"""Check parametric expressions away from their generating numerical inputs."""
import unittest

import sympy as sp

from server.worked import worked_solution
from test_verifier import beam


class SymbolicTests(unittest.TestCase):
    def test_central_force_retains_load_length_and_rigidity(self):
        result = worked_solution({"model": beam(), "section": 0.5}, verify=False)
        load, length, rigidity = sp.symbols("load0 L EI")
        moment = sp.sympify(result["selected"][2]["symbolicExact"])
        displacement = sp.sympify(result["selected"][4]["symbolicExact"])
        self.assertEqual(sp.expand(moment-load*length/4), 0)
        self.assertEqual(sp.expand(displacement+1000*load*length**3/(48*rigidity)), 0)
        self.assertIn("48", result["selected"][4]["symbolicLatex"])
        self.assertEqual(result["selected"][4]["symbolicUnit"], "m")
        self.assertIn(r"\loadsymbol{0}{}", result["pieces"][0]["forces"][-1]["symbolicLatex"])

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
