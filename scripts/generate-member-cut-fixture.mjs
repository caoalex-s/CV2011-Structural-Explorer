/** Generate a Lean fixture solely from a fixed synthetic adapter invocation.
 * Only validated rational digits are embedded; model IDs never enter Lean code. */
import { registerHooks } from 'node:module';
import { writeFile } from 'node:fs/promises';

registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { createEvidenceEnvelope } = await import('../web/model-evidence.ts');
const { adaptEvidenceSnapshot, verifyExactCutArtifact } = await import('../web/exact-cut-adapter.ts');
const target = process.argv[2];
if (!target) throw Error('Provide a temporary output path');

const model = {
    nodes: [{ id: 'synthetic-start', x: 0, y: 0 }, { id: 'synthetic-end', x: 1, y: 0 }],
    members: [{ id: 'synthetic-member', a: 'synthetic-start', b: 'synthetic-end', EA: 1, EI: 1 }],
    supports: [{ id: 'synthetic-support', member: 'synthetic-member', t: 0.5, kind: 'roller', angle: 90 }],
    loads: [
        { id: 'synthetic-left', member: 'synthetic-member', kind: 'distributed', t: 0, end: 0.5, fx: 0, fy: 0, mz: 0, qEnd: 2 },
        { id: 'synthetic-right', member: 'synthetic-member', kind: 'distributed', t: 0.5, end: 1, fx: 0, fy: 2, mz: 0, qEnd: 0 },
        { id: 'synthetic-point', member: 'synthetic-member', kind: 'force', t: 0.5, end: 1, fx: 0, fy: -1, mz: 0, qEnd: 0 },
    ],
};
const query = { member: 'synthetic-member', parameter: 0.5, cutSide: 'left', quantity: 'M', units: 'kN m', signConvention: 'sagging positive' };
const snapshot = await createEvidenceEnvelope(model, query);
const artifact = await adaptEvidenceSnapshot(snapshot);
await verifyExactCutArtifact(snapshot, artifact);
const member = artifact.members[0];
if (member.cuts.length !== 3 || member.intervals.length !== 2 || artifact.actions.length !== 1 || artifact.supports.length !== 1 ||
    member.cuts[1].location.kind !== 'interior' || artifact.actions[0].location.kind !== 'interior' ||
    artifact.supports[0].location.kind !== 'interior' || artifact.actions[0].cutIndex !== 1 || artifact.supports[0].cutIndex !== 1)
    throw Error('Synthetic adapter topology did not match the intended fixture');
function real(value) {
    if (!value || !/^-?(0|[1-9][0-9]*)$/.test(value.numerator) || !/^[1-9][0-9]*$/.test(value.denominator))
        throw Error('Unsafe rational in generated fixture');
    return `((${value.numerator} : ℝ) / ${value.denominator})`;
}
const cut0 = real(member.cuts[0].parameter), cut1 = real(member.cuts[1].parameter), cut2 = real(member.cuts[2].parameter);
const leftStart = real(member.intervals[0].verticalEndpoints[0]), leftEnd = real(member.intervals[0].verticalEndpoints[1]);
const rightStart = real(member.intervals[1].verticalEndpoints[0]), rightEnd = real(member.intervals[1].verticalEndpoints[1]);
const pointFy = real(artifact.actions[0].components.fy);
if (!/^[a-f0-9]{64}$/.test(artifact.artifactDigest)) throw Error('Invalid synthetic artifact digest');
const source = `-- Synthetic adapter artifact SHA-256: ${artifact.artifactDigest}
import MemberCutAdapter
open Polynomial MeasureTheory intervalIntegral FrameInterfaces FrameTransform FrameAssemblyModel MemberCutAdapter
noncomputable section

-- All rational literals below come from a synthetic adapter artifact.
def cutParameter : Fin 1 → Fin 1 → ℝ := fun _ _ => ${cut1}
def model : Model 2 1 1 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun _ => ⟨0, 1, ⟨1, 0⟩, none, none⟩
  segmentMember := fun _ => 0
  segmentLeft := fun i => if i = 0 then .endSide (0, false) else .interior 0 0
  segmentRight := fun i => if i = 0 then .interior 0 0 else .endSide (0, true)
  segmentLength := fun _ => 1/2
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun i => if i = 0 then ${leftStart} else ${rightStart}
  segmentVerticalEnd := fun i => if i = 0 then ${leftEnd} else ${rightEnd}

def actions : Fin 1 → PointAction 1 1 := fun _ => ⟨.interior 0 0, ![0, ${pointFy}, 0]⟩
def supports : Fin 1 → SupportInput 1 1 := fun _ => ⟨.interior 0 0, .roller, 0, 1, false, false, false⟩
def properties : Fin 1 → ℝ := fun _ => 1

theorem generated_chain : IntervalChain ${cut0} ${cut2} [(${cut0}, ${cut1}), (${cut1}, ${cut2})] := by
  apply IntervalChain.step
  · norm_num
  · apply IntervalChain.single
    norm_num

example (t : ℝ) (h0 : ${cut0} ≤ t) (h1 : t ≤ ${cut2}) :
    ∃ piece ∈ [(${cut0}, ${cut1}), (${cut1}, ${cut2})], piece.1 ≤ t ∧ t ≤ piece.2 := by
  exact chain_coverage generated_chain t h0 h1

example (p : Polynomial ℝ) :
    chainWork p 1 [(${cut0}, ${cut1}), (${cut1}, ${cut2})] =
      1 * (∫ t in ${cut0}..${cut2}, p.eval t) := by
  exact chain_polynomial_work generated_chain p 1

example : ExactContract model actions supports cutParameter properties properties properties := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, model]
  · intro segment
    fin_cases segment <;> norm_num [model, locationParameter, cutParameter]
  · intro member t ht0 ht1
    fin_cases member
    by_cases ht : t ≤ 1/2
    · refine ⟨0, ?_⟩
      norm_num [model, locationParameter, cutParameter]
      constructor <;> linarith
    · refine ⟨1, ?_⟩
      norm_num [model, locationParameter, cutParameter]
      constructor <;> linarith
  · intro a b hne hmember
    fin_cases a <;> fin_cases b <;> norm_num [model, locationParameter, cutParameter] at *
  · intro member left right hl hr hleft hright hpos
    fin_cases member
    have leftCases : left = .endSide (0, false) ∨ left = .interior 0 0 ∨ left = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hleft
      fin_cases i <;> simp [model] at hi <;> aesop
    have rightCases : right = .endSide (0, false) ∨ right = .interior 0 0 ∨ right = .endSide (0, true) := by
      obtain ⟨i, hi⟩ := hright
      fin_cases i <;> simp [model] at hi <;> aesop
    rcases leftCases with rfl | rfl | rfl <;> rcases rightCases with rfl | rfl | rfl <;>
      norm_num [locationParameter, cutParameter] at *
  · intro member
    fin_cases member
    exact ⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩⟩
  · intro member cut h
    fin_cases member
    fin_cases cut
    norm_num [cutParameter]
  · intro action
    fin_cases action
    exact ⟨0, Or.inr rfl⟩
  · intro support
    fin_cases support
    exact ⟨0, Or.inr rfl⟩
  · intro member
    fin_cases member
    norm_num [model]
  · intro support hkind
    fin_cases support
    norm_num [supports]
  · intro member
    fin_cases member
    norm_num [properties]
  · intro segment
    fin_cases segment <;> norm_num [model, properties, cutParameter, locationParameter]
  · intro segment
    fin_cases segment <;> norm_num [model, properties]
  · intro side direction stiffness hactive hlaw
    rcases side with ⟨member, ending⟩
    fin_cases member
    cases ending <;> fin_cases direction <;>
      simp [directionLaw, endConnection, referenceMember, incident, endNode, model, rigidConnection] at hlaw

example : model.segmentVerticalStart 0 = 0 ∧ model.segmentVerticalEnd 0 = 2 ∧
    model.segmentVerticalStart 1 = 2 ∧ model.segmentVerticalEnd 1 = 0 := by
  norm_num [model]
example : resultant 1 0 1 1 1 = 1 ∧ firstMoment 1 0 1 1 1 = 1/2 := by
  norm_num [resultant, firstMoment]
example : resultant 1 0 (1/2) ${leftStart} ${leftEnd} + resultant 1 (1/2) 1 ${rightStart} ${rightEnd} = 1 ∧
    firstMoment 1 0 (1/2) ${leftStart} ${leftEnd} + firstMoment 1 (1/2) 1 ${rightStart} ${rightEnd} = 1/2 := by
  norm_num [resultant, firstMoment]

-- Equal resultant and first moment do not determine work against t^3.
example : (∫ t in (0:ℝ)..1, t^3) = 1/4 := by
  norm_num [intervalIntegral.integral_pow]
example : (∫ t in (0:ℝ)..(1/2), 4*t^4) + (∫ t in (1/2:ℝ)..1, (4*t^3-4*t^4)) = 3/16 := by
  have hleft : (∫ t in (0:ℝ)..(1/2), 4*t^4) = 1/40 := by
    rw [intervalIntegral.integral_const_mul]
    norm_num [intervalIntegral.integral_pow]
  have hright : (∫ t in (1/2:ℝ)..1, (4*t^3-4*t^4)) = 13/80 := by
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      norm_num [intervalIntegral.integral_pow]
    · exact (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _
  linarith

`;
await writeFile(target, source, 'utf8');
console.log(`Generated synthetic adapter fixture from artifact ${artifact.artifactDigest}`);
