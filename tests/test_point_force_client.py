"""Compare the offline closed-form beam with the exact worked service."""
import json
from fractions import Fraction
import subprocess
import unittest

from server.worked import worked_solution
from test_verifier import beam


class PointForceClientTests(unittest.TestCase):
    def test_offline_values_match_exact_derivation(self):
        cases = [(0.2, 0.7, -30), (0.8, 0.3, -15), (0.5, 0.5, 0),
                 (0.3, 0.7, 20), (0, 0.5, -20), (1, 1, -20)]
        payloads = []
        for position, section, force in cases:
            model = beam()
            model["loads"][0].update(t=position, fy=force, label="F_A")
            payloads.append({"model": model, "section": section})
        script = """
            import { registerHooks } from 'node:module';
            registerHooks({resolve(s,c,n) { return c.parentURL?.includes('/web/') && s.startsWith('./') && s.endsWith('.js') ? n(s.replace(/\\.js$/, '.ts'),c) : n(s,c); }});
            const {pointForceWorked} = await import('./web/point-force-worked.ts');
            let input=''; for await (const chunk of process.stdin) input += chunk;
            console.log(JSON.stringify(JSON.parse(input).map(p => pointForceWorked(p.model,p.section))));
        """
        output = subprocess.run(["node", "--input-type=module", "-e", script], input=json.dumps(payloads),
                                text=True, capture_output=True, check=True)
        for payload, client in zip(payloads, json.loads(output.stdout)):
            server = worked_solution(payload, verify=False)
            self.assertEqual(client["label"], "F_{A}")
            self.assertAlmostEqual(client["leftReaction"], float(Fraction(server["equilibrium"][4]["exact"])))
            for key, index, factor in [("shear", 1, 1), ("moment", 2, 1),
                                       ("theta", 3, 1), ("displacement", 4, 1000)]:
                self.assertAlmostEqual(client[key]*factor, float(Fraction(server["selected"][index]["exact"])), places=8)


if __name__ == "__main__":
    unittest.main()
