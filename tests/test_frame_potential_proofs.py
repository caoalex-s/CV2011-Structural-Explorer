"""Signed element and linked spring fixtures, verified on Linux CI."""
from test_local_frame_proofs import LocalFrameFieldChecks


class LinkedFrameChecks(LocalFrameFieldChecks):
    def compile_example(self, statement):
        return super().compile_example(statement.replace("-- linked", ""))

    def test_signed_end_actions_and_spring(self):
        result = self.compile_example("""
def signedDofs : LocalDofs := ![1, -2, 3, -4, 5, -6]
example : endActions signedDofs 2 10 8 3 (-1) 2 (-4) =
    ![70/3, -601/5, -1258/15, -76/3, 611/5, -2348/15] := by
  funext i
  rw [end_actions_from_fields signedDofs 2 10 8 3 (-1) 2 (-4) (by norm_num) (by norm_num) (by norm_num)]
  fin_cases i <;> norm_num [signedDofs, stiffness, consistentLoad, Fin.sum_univ_succ]
example : HasDerivAt (memberPotential signedDofs 0 2 10 8 3 (-1) 2 (-4) 2 (91/3)) 0 1 := by
  convert member_potential_derivative signedDofs 0 2 10 8 3 (-1) 2 (-4) 2 (91/3) 1
    (by norm_num) (by norm_num) (by norm_num) using 1
  rw [end_actions_from_fields _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  norm_num [varyingDofs, signedDofs, stiffness, consistentLoad, Fin.sum_univ_succ]
""")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_wrong_right_end_actions(self):
        for index, wrong in [(4, "-611/5"), (5, "2348/15")]:
            result = self.compile_example(f"""
def signedDofs : LocalDofs := ![1, -2, 3, -4, 5, -6]
example : endActions signedDofs 2 10 8 3 (-1) 2 (-4) {index} = {wrong} := by
  rw [end_actions_from_fields signedDofs 2 10 8 3 (-1) 2 (-4) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [signedDofs, stiffness, consistentLoad, Fin.sum_univ_succ]
""")
            output = result.stdout + result.stderr
            self.assertNotEqual(result.returncode, 0)
            self.assertRegex(output, r"unsolved goals|tactic .*failed")
            self.assertNotIn("unknown identifier", output)
