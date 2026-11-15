import InclinedFrameGlobalBasis
import FrameMatrixResidual

/-! The reduced operator is defined from the original physical stiffness form
    and the source-owned admissible embedding. Invertibility is used for unique
    equilibrium; positive stiffness additionally uses the physical PSD theorem.
    Interval assembly and flattened packet ordering must bind to these entries. -/
namespace InclinedFrameReduced
open InclinedFrameSource InclinedFrameBasis InclinedFrameGlobalBasis InclinedFrameReal
noncomputable section

variable (data : Partition) (basis : GlobalBasis)

def form : Coordinates data basis →ₗ[ℝ] Coordinates data basis →ₗ[ℝ] ℝ where
  toFun values := (stiffnessForm data (embedding data basis values)).comp (embedding data basis)
  map_add' first second := by
    apply LinearMap.ext
    intro variation
    change stiffnessForm data (embedding data basis (first+second)) (embedding data basis variation) =
      stiffnessForm data (embedding data basis first) (embedding data basis variation) +
        stiffnessForm data (embedding data basis second) (embedding data basis variation)
    rw [map_add, map_add]
    rfl
  map_smul' scalar values := by
    apply LinearMap.ext
    intro variation
    change stiffnessForm data (embedding data basis (scalar • values)) (embedding data basis variation) =
      scalar * stiffnessForm data (embedding data basis values) (embedding data basis variation)
    rw [map_smul, map_smul]
    rfl

def load : Coordinates data basis →ₗ[ℝ] ℝ := (loadForm data).comp (embedding data basis)

def unit (index : Index data basis) : Coordinates data basis :=
  fun other => if other = index then 1 else 0

/-- Row i tests virtual coordinate i; column j applies displacement coordinate j. -/
def matrix (row column : Index data basis) : ℝ :=
  form data basis (unit data basis column) (unit data basis row)

def force (row : Index data basis) : ℝ := load data basis (unit data basis row)

theorem coordinate_expansion (values : Coordinates data basis) :
    values = ∑ index, values index • unit data basis index := by
  funext index
  simp [unit, Finset.sum_apply, smul_eq_mul, mul_ite, eq_comm]

theorem linear_expansion (functional : Coordinates data basis →ₗ[ℝ] ℝ)
    (values : Coordinates data basis) :
    functional values = ∑ index, values index * functional (unit data basis index) := by
  calc
    functional values = functional (∑ index, values index • unit data basis index) :=
      congrArg functional (coordinate_expansion data basis values)
    _ = _ := by simp [map_sum, map_smul]

theorem matrix_row (values : Coordinates data basis) (row : Index data basis) :
    form data basis values (unit data basis row) =
      FrameMatrixResidual.action (matrix data basis) values row := by
  calc
    form data basis values (unit data basis row) =
        form data basis (∑ index, values index • unit data basis index) (unit data basis row) :=
      congrArg (fun coordinates => form data basis coordinates (unit data basis row))
        (coordinate_expansion data basis values)
    _ = _ := by simp [map_sum, map_smul, FrameMatrixResidual.action, matrix, mul_comm]

theorem matrix_representation (values variation : Coordinates data basis) :
    form data basis values variation =
      ∑ row, variation row * FrameMatrixResidual.action (matrix data basis) values row := by
  rw [linear_expansion data basis (form data basis values) variation]
  simp only [matrix_row]

theorem force_representation (variation : Coordinates data basis) :
    load data basis variation = ∑ row, variation row * force data basis row :=
  linear_expansion data basis (load data basis) variation

theorem form_symmetric (first second : Coordinates data basis) :
    form data basis first second = form data basis second first :=
  stiffness_symmetric data (embed data basis first) (embed data basis second)

theorem form_nonnegative (h : PartitionValid data) (values : Coordinates data basis) :
    0 ≤ form data basis values values :=
  stiffness_nonnegative data h (embed data basis values)

/-- Equilibrium is tested against every source-admissible virtual motion. -/
def Equilibrium (motion : Motion data) : Prop :=
  SourceAllows data motion ∧ ∀ variation, SourceAllows data variation →
    stiffnessWork data motion variation = externalWork data variation

theorem reduced_equilibrium (hpartition : PartitionValid data)
    (h : GlobalBasisValid data basis) (values : Coordinates data basis) :
    FrameMatrixResidual.action (matrix data basis) values = force data basis ↔
      Equilibrium data (embed data basis values) := by
  constructor
  · intro hsolution
    constructor
    · exact (range_equals_source_kernel hpartition h _).mpr ⟨values, rfl⟩
    · intro variation hadmissible
      obtain ⟨coordinates, rfl⟩ := (range_equals_source_kernel hpartition h variation).mp hadmissible
      change form data basis values coordinates = load data basis coordinates
      rw [matrix_representation, force_representation, hsolution]
  · intro hequilibrium
    funext row
    have hadmissible : SourceAllows data (embed data basis (unit data basis row)) :=
      (range_equals_source_kernel hpartition h _).mpr ⟨unit data basis row, rfl⟩
    have hwork := hequilibrium.2 _ hadmissible
    change form data basis values (unit data basis row) = force data basis row at hwork
    simpa only [matrix_row] using hwork

/-- Verified contraction of the actual reduced operator gives unique physical
    equilibrium. An inverse proposal or floating rank estimate is insufficient. -/
theorem unique_equilibrium (hpartition : PartitionValid data) (h : GlobalBasisValid data basis)
    (inverse : Index data basis → Index data basis → ℝ) (q : ℝ)
    (hqzero : 0 ≤ q) (hqone : q < 1)
    (hrows : ∀ row, (∑ column,
      |FrameMatrixResidual.defect (matrix data basis) inverse row column|) ≤ q) :
    ∃! motion, Equilibrium data motion := by
  have hdefect := FrameMatrixResidual.defect_norm_bound (matrix data basis) inverse q hqzero hrows
  obtain ⟨values, hsolution, hunique⟩ := FrameResidualBound.exists_unique_solution
    (FrameMatrixResidual.action (matrix data basis)) (FrameMatrixResidual.action inverse)
    q hqone hdefect (force data basis)
  refine ⟨embed data basis values, (reduced_equilibrium data basis hpartition h values).mp hsolution, ?_⟩
  intro other hequilibrium
  obtain ⟨coordinates, hcoordinates⟩ := (range_equals_source_kernel hpartition h other).mp hequilibrium.1
  have hother : Equilibrium data (embed data basis coordinates) := by
    simpa only [hcoordinates] using hequilibrium
  have hequal := hunique coordinates ((reduced_equilibrium data basis hpartition h coordinates).mpr hother)
  rw [← hcoordinates, hequal]

/-- The residual enclosure bounds the same source coordinates that generate
    physical equilibrium. Requested-field and reaction bounds must subsequently
    be obtained by enclosing their source-defined recovery expressions. -/
theorem enclosed_equilibrium (hpartition : PartitionValid data) (h : GlobalBasisValid data basis)
    (inverse : Index data basis → Index data basis → ℝ)
    (estimate : Coordinates data basis) (q eta : ℝ)
    (hqzero : 0 ≤ q) (hqone : q < 1) (hetazero : 0 ≤ eta)
    (hrows : ∀ row, (∑ column,
      |FrameMatrixResidual.defect (matrix data basis) inverse row column|) ≤ q)
    (hresidual : ∀ row, |FrameMatrixResidual.action inverse
      (force data basis - FrameMatrixResidual.action (matrix data basis) estimate) row| ≤ eta) :
    ∃ values, Equilibrium data (embed data basis values) ∧
      ∀ index, estimate index - eta/(1-q) ≤ values index ∧
        values index ≤ estimate index + eta/(1-q) := by
  obtain ⟨values, hvalues, _⟩ := FrameMatrixResidual.enclosed_solution
    (matrix data basis) inverse (force data basis) estimate q eta hqzero hqone hetazero hrows hresidual
  exact ⟨values, (reduced_equilibrium data basis hpartition h values).mp hvalues.1, hvalues.2⟩

/-- Physical PSD and symmetry are indispensable here. They are derived from
    the source member properties, not inferred from the inverse certificate. -/
theorem positive_physical_stiffness (hpartition : PartitionValid data)
    (hbasis : GlobalBasisValid data basis)
    (inverse : Index data basis → Index data basis → ℝ) (q : ℝ)
    (hqzero : 0 ≤ q) (hqone : q < 1)
    (hrows : ∀ row, (∑ column,
      |FrameMatrixResidual.defect (matrix data basis) inverse row column|) ≤ q)
    (motion : Motion data) (hadmissible : SourceAllows data motion) (hnonzero : motion ≠ 0) :
    0 < stiffnessWork data motion motion := by
  have hpositive := FrameMatrixResidual.positive_stiffness_of_defect
    (matrix data basis) inverse (form data basis) q hqzero hqone hrows
    (matrix_representation data basis) (form_symmetric data basis)
    (form_nonnegative data basis hpartition)
  obtain ⟨values, hvalues⟩ := (range_equals_source_kernel hpartition hbasis motion).mp hadmissible
  have hvaluesNonzero : values ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [← hvalues, hzero]
    exact (embedding data basis).map_zero
  have hresult := hpositive values hvaluesNonzero
  change 0 < stiffnessWork data (embed data basis values) (embed data basis values) at hresult
  simpa only [hvalues] using hresult

/-- The physical conclusion is tied to the source accepted by the partition
    compiler, and to the basis accepted for that same partition. -/
theorem checked_source_equilibrium (source : RationalFrame.Source)
    (hcompile : checkedPartition source = some data)
    (hbasis : checkedGlobalBasis data = some basis)
    (inverse : Index data basis → Index data basis → ℝ) (q : ℝ)
    (hqzero : 0 ≤ q) (hqone : q < 1)
    (hrows : ∀ row, (∑ column,
      |FrameMatrixResidual.defect (matrix data basis) inverse row column|) ≤ q) :
    data.source = source ∧ ∃! motion, Equilibrium data motion := by
  have hpartition := checkedPartition_source hcompile
  exact ⟨hpartition.1, unique_equilibrium data basis hpartition.2
    (checkedGlobalBasis_valid hbasis) inverse q hqzero hqone hrows⟩

end
end InclinedFrameReduced
