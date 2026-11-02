"""Compare two independently implemented formulations on mixed-load beams."""
import json
from pathlib import Path
import random
import shutil
import subprocess
import unittest

import sympy as sp

from server.verifier import reference
from test_verifier import beam


@unittest.skipUnless(shutil.which("node"), "Node.js is required for cross-language comparison")
class IndependentFormulations(unittest.TestCase):
    def test_forty_mixed_load_cases(self):
        generator = random.Random(2011)
        models = []
        for _ in range(40):
            model = beam()
            model["supports"][0]["t"] = generator.choice([0, 0.1, 0.2])
            model["supports"][1]["t"] = generator.choice([0.8, 0.9, 1])
            model["loads"] = []
            for index in range(3):
                model["loads"].append({"id": f"P{index}", "member": "AB", "kind": "force",
                                       "t": generator.choice([0, 0.25, 0.5, 0.75, 1]),
                                       "end": 1, "fx": generator.randint(-10, 10),
                                       "fy": generator.randint(-30, 15), "mz": 0, "qEnd": 0})
            model["loads"].append({"id": "C", "member": "AB", "kind": "moment", "t": 0.6,
                                   "end": 1, "fx": 0, "fy": 0, "mz": generator.randint(-30, 30), "qEnd": 0})
            model["loads"].append({"id": "q", "member": "AB", "kind": "distributed", "t": 0.15,
                                   "end": 0.85, "fx": 0, "fy": generator.randint(-8, 4),
                                   "mz": 0, "qEnd": generator.randint(-8, 4)})
            models.append(model)
        process = subprocess.run(["node", "tests/batch-analysis.mjs"], input=json.dumps(models),
                                 capture_output=True, text=True, check=True,
                                 cwd=Path(__file__).resolve().parents[1])
        results = json.loads(process.stdout)
        for model, numerical in zip(models, results):
            self.assertEqual(numerical["status"], "stable")
            exact = reference(model)
            for sample in numerical["sections"]:
                values = exact.values(sp.Rational(str(sample["x"])))
                for field, key, scale in [("N", "normal", 1), ("V", "shear", 1), ("M", "moment", 1), ("uy", "deflection", 1000)]:
                    expected = float(values[key])
                    self.assertAlmostEqual(sample[field] * scale, expected,
                                           delta=1e-6 * max(1, abs(expected)))
