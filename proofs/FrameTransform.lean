import LocalFrameFields

/-!
Orthogonal coordinate transformations and member-side relative motions.
The direction cosines are inputs here. A later stage must prove their relation
to the drawing geometry, including irrational lengths and input rounding.
-/
open FrameInterfaces

namespace FrameTransform

noncomputable section

abbrev Triple := Fin 3 → ℝ

/-- Transform global translation and rotation into the member's local axes. -/
def toLocal (c s : ℝ) (v : Triple) : Triple :=
  ![c*v 0+s*v 1, -s*v 0+c*v 1, v 2]

/-- Apply the transposed rotation to a local translation or action. -/
def toGlobal (c s : ℝ) (v : Triple) : Triple :=
  ![c*v 0-s*v 1, s*v 0+c*v 1, v 2]

def work (a b : Triple) : ℝ := a 0*b 0 + a 1*b 1 + a 2*b 2

/-- The transpose is the inverse when the direction cosines are normalised. -/
theorem inverse_transform (c s : ℝ) (v : Triple) (h : c^2+s^2 = 1) :
    toGlobal c s (toLocal c s v) = v := by
  funext i
  fin_cases i <;> simp [toGlobal, toLocal]
  all_goals nlinarith [show (c^2+s^2)*v 0 = v 0 by rw [h]; ring,
    show (c^2+s^2)*v 1 = v 1 by rw [h]; ring]

/-- Orthogonal transformation preserves paired force–displacement work. -/
theorem work_invariant (c s : ℝ) (f d : Triple) (h : c^2+s^2 = 1) :
    work (toLocal c s f) (toLocal c s d) = work f d := by
  simp [work, toLocal]
  nlinarith [show (c^2+s^2)*(f 0*d 0+f 1*d 1) = f 0*d 0+f 1*d 1 by rw [h]; ring]

/-- End mapping adds local axial/transverse slips to the reference movement. -/
def endMotion (c s : ℝ) (reference slip : Triple) : Triple :=
  ![reference 0+c*slip 0-s*slip 1,
    reference 1+s*slip 0+c*slip 1, reference 2+slip 2]

/-- With zero relative movement the member end is rigidly tied to the reference. -/
theorem rigid_end (c s : ℝ) (reference : Triple) :
    endMotion c s reference (fun _ => 0) = reference := by
  funext i
  fin_cases i <;> simp [endMotion]

/-- Potential for one relative direction. pSide includes all actions applied
directly to this member side, including loads and support actions. -/
def relativePotential (k pSide r delta : ℝ) : ℝ := k*delta^2/2 - pSide*delta + r*delta

theorem potential_derivative (k pSide r delta : ℝ) :
    HasDerivAt (relativePotential k pSide r) (k*delta-pSide+r) delta := by
  have h := (((hasDerivAt_id delta).pow 2).const_mul (k/2)).sub
    ((hasDerivAt_id delta).const_mul pSide) |>.add ((hasDerivAt_id delta).const_mul r)
  convert h using 1
  · funext x
    dsimp [relativePotential]
    ring
  · simp
    ring

/-- Stationarity includes side loads; it does not identify −r with kδ alone. -/
theorem spring_stationarity (k pSide r delta : ℝ)
    (h : HasDerivAt (relativePotential k pSide r) 0 delta) :
    r + k*delta = pSide := by
  have hderiv := (potential_derivative k pSide r delta).unique h
  linarith

/-- A free direction can still carry a directly applied member-side action. -/
theorem free_stationarity (pSide r delta : ℝ)
    (h : HasDerivAt (relativePotential 0 pSide r) 0 delta) : r = pSide := by
  have hbalance := spring_stationarity 0 pSide r delta h
  simpa using hbalance

/-- Positive spring stiffness gives nonnegative stored energy. -/
theorem spring_energy_nonnegative (k delta : ℝ) (hk : 0 ≤ k) :
    0 ≤ k*delta^2/2 := by positivity

end
end FrameTransform
