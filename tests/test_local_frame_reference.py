"""Compare loaded exact local fields with the engine's fixed-end segments.

This is a numerical cross-check, not a proof of the TypeScript execution or of
its translation from a drawing into the mathematical model.
"""
import json
import subprocess
import unittest

import sympy as sp


class LocalFrameFieldComparison(unittest.TestCase):
    def test_fields_for_reversed_and_inclined_affine_loading(self):
        cases = [((0, 0), (5, 0), -2, -7, "fixed"), ((0, 0), (3, 4), -2, -7, "fixed"),
                 ((3, 4), (0, 0), 3, -4, "fixed"), ((0, 0), (3, 4), 0, 0, "fixed"),
                 ((0, 0), (3, 4), -3, -8, "pin-roller")]
        models = []
        for start, end, q0, q1, support_case in cases:
            models.append({"nodes": [{"id": "A", "x": start[0], "y": start[1]},
                                     {"id": "B", "x": end[0], "y": end[1]}],
                           "members": [{"id": "AB", "a": "A", "b": "B", "EA": 3000, "EI": 2000}],
                           "supports": [{"id": "S1", "member": "AB", "t": 0, "kind": "fixed" if support_case == "fixed" else "pin", "angle": 90},
                                        {"id": "S2", "member": "AB", "t": 1, "kind": "fixed" if support_case == "fixed" else "roller", "angle": 90}],
                           "loads": [{"id": "q", "member": "AB", "kind": "distributed", "t": 0,
                                      "end": 1, "fx": 0, "fy": q0, "mz": 0, "qEnd": q1}]})
        script = """
            import {analyse} from './web/engine.ts';
            let input=''; for await (const chunk of process.stdin) input += chunk;
            console.log(JSON.stringify(JSON.parse(input).map(analyse)));
        """
        response = subprocess.run(["node", "--input-type=module", "-e", script], input=json.dumps(models),
                                  text=True, capture_output=True, check=True)
        x = sp.Symbol("x")
        length, axial, bending = sp.Integer(5), sp.Integer(3000), sp.Integer(2000)
        for (start, end, q0, q1, support_case), result in zip(cases, json.loads(response.stdout)):
            self.assertEqual(result["status"], "stable")
            c = sp.Rational(end[0]-start[0], 5)
            s = sp.Rational(end[1]-start[1], 5)
            p0, p1, t0, t1 = s*q0, s*q1, c*q0, c*q1
            first, last = result["elements"][0]["samples"][0], result["elements"][0]["samples"][-1]
            def local_components(sample):
                ux, uy = sp.Rational(str(sample["ux"])), sp.Rational(str(sample["uy"]))
                return c*ux+s*uy, -s*ux+c*uy, sp.Rational(str(sample["rotation"]))
            u0, v0, theta0 = local_components(first)
            u1, v1, theta1 = local_components(last)
            z = x/length
            u = u0*(1-z)+u1*z + length**2/(6*axial)*(p0*(2*z-3*z**2+z**3)+p1*(z-z**3))
            v = (v0*(1-3*z**2+2*z**3)+length*theta0*(z-2*z**2+z**3)
                 + v1*(3*z**2-2*z**3)+length*theta1*(z**3-z**2)
                 + length**4/(120*bending)*z**2*(z-1)**2*((t1-t0)*(z+2)+5*t0))
            N, M = axial*sp.diff(u, x), bending*sp.diff(v, x, 2)
            V, rotation = sp.diff(M, x), sp.diff(v, x)
            for sample in result["elements"][0]["samples"]:
                at = length*sp.Rational(str(sample["t"]))
                expected = {"N": N, "V": V, "M": M, "rotation": rotation,
                            "ux": c*u-s*v, "uy": s*u+c*v}
                for field, expression in expected.items():
                    self.assertAlmostEqual(sample[field], float(expression.subs(x, at)), places=8,
                                           msg=f"{start}->{end}: {field} at {sample['t']}")


if __name__ == "__main__":
    unittest.main()
