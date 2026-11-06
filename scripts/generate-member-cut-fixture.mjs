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
// A separate fixed synthetic model checks partial overlapping sources and an
// end-side release. Every emitted literal is validated and read from the adapter.
const detailedModel = {
    nodes: [{ id: 'shared', x: 0, y: 0 }, { id: 'left', x: -1, y: 0 }, { id: 'right', x: 1, y: 0 }],
    members: [
        { id: 'reference', a: 'left', b: 'shared', EA: 1, EI: 1 },
        { id: 'released', a: 'shared', b: 'right', EA: 1, EI: 1,
            connectionA: { axial: 'free', transverse: 7, rotation: 'free' } },
    ],
    supports: [{ id: 'side-support', member: 'released', t: 0, kind: 'fixed', angle: 0 }],
    loads: [
        { id: 'first', member: 'released', kind: 'distributed', t: 0.25, end: 0.75, fx: 0, fy: -2, mz: 0, qEnd: 2 },
        { id: 'second', member: 'released', kind: 'distributed', t: 0.5, end: 1, fx: 0, fy: 1, mz: 0, qEnd: -1 },
        { id: 'couple', member: 'released', kind: 'moment', t: 0, end: 1, fx: 0, fy: 0, mz: 5, qEnd: 0 },
    ],
};
const detailed = await adaptEvidenceSnapshot(await createEvidenceEnvelope(detailedModel, { ...query, member: 'released' }));
const detailedMember = detailed.members[1];
const overlap = detailedMember.intervals.find(interval => interval.contributions.length === 2);
const law = detailedMember.endLaws[0], detailedAction = detailed.actions[0], detailedSupport = detailed.supports[0];
if (!overlap || law.axial.kind !== 'free' || law.transverse.kind !== 'spring' || law.rotation.kind !== 'free' ||
    law.effectiveReference !== 'reference' || detailedAction.location.kind !== 'endSide' ||
    detailedAction.location.memberIndex !== 1 || detailedAction.location.end !== 'a' ||
    detailedSupport.location.kind !== 'endSide' || detailedSupport.location.memberIndex !== 1 || detailedSupport.location.end !== 'a')
    throw Error('Detailed adapter ownership or source coverage changed');
const [src0, src1] = overlap.contributions;
const oa0 = real(src0.sourceInterval[0]), ob0 = real(src0.sourceInterval[1]);
const oa1 = real(src1.sourceInterval[0]), ob1 = real(src1.sourceInterval[1]);
const oq00 = real(src0.sourceEndpoints[0]), oq01 = real(src0.sourceEndpoints[1]);
const oq10 = real(src1.sourceEndpoints[0]), oq11 = real(src1.sourceEndpoints[1]);
const ou = real(overlap.from), ov = real(overlap.to);
const oq0 = real(overlap.verticalEndpoints[0]), oq1 = real(overlap.verticalEndpoints[1]);
const sideMoment = real(detailedAction.components.mz), sideSpring = real(law.transverse.stiffness);
const loadedSpans = detailedMember.intervals.filter(interval => interval.contributions.length > 0);
if (loadedSpans.length !== 3) throw Error('Expected three loaded elementary intervals');
// A missing source is padded with an identically zero affine source on the
// target interval, keeping containment true without inventing load work.
const padded = loadedSpans.map(interval => [0, 1].map(index => {
    const contribution = interval.contributions.find(item => item.sourceIndex === index);
    return contribution ?? { sourceInterval: [interval.from, interval.to], sourceEndpoints: [
        { numerator: '0', denominator: '1' }, { numerator: '0', denominator: '1' }] };
}));
const selectSpan = values => `fun k => if k = 0 then ${values[0]} else if k = 1 then ${values[1]} else ${values[2]}`;
const selectSources = values => `fun k i => if i = 0 then (${selectSpan(values.map(pair => pair[0]))}) k else (${selectSpan(values.map(pair => pair[1]))}) k`;
const familyA = selectSources(padded.map(pair => pair.map(item => real(item.sourceInterval[0]))));
const familyB = selectSources(padded.map(pair => pair.map(item => real(item.sourceInterval[1]))));
const familyQ0 = selectSources(padded.map(pair => pair.map(item => real(item.sourceEndpoints[0]))));
const familyQ1 = selectSources(padded.map(pair => pair.map(item => real(item.sourceEndpoints[1]))));
const familyU = selectSpan(loadedSpans.map(interval => real(interval.from)));
const familyV = selectSpan(loadedSpans.map(interval => real(interval.to)));
const familyStart = selectSpan(loadedSpans.map(interval => real(interval.verticalEndpoints[0])));
const familyEnd = selectSpan(loadedSpans.map(interval => real(interval.verticalEndpoints[1])));
const restricted00 = real(src0.restrictedEndpoints[0]), restricted01 = real(src0.restrictedEndpoints[1]);
const restricted10 = real(src1.restrictedEndpoints[0]), restricted11 = real(src1.restrictedEndpoints[1]);
if (!/^[a-f0-9]{64}$/.test(detailed.artifactDigest)) throw Error('Invalid detailed artifact digest');
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

-- Detailed adapter artifact SHA-256: ${detailed.artifactDigest}
def sourceA : Fin 2 → ℝ := fun i => if i = 0 then ${oa0} else ${oa1}
def sourceB : Fin 2 → ℝ := fun i => if i = 0 then ${ob0} else ${ob1}
def sourceQ0 : Fin 2 → ℝ := fun i => if i = 0 then ${oq00} else ${oq10}
def sourceQ1 : Fin 2 → ℝ := fun i => if i = 0 then ${oq01} else ${oq11}
def overlapDensity : Polynomial ℝ := 4 * X^4 - X^3

theorem overlapEndpoints :
    (∑ i : Fin 2, affine (sourceA i) (sourceB i) (sourceQ0 i) (sourceQ1 i) ${ou}) = ${oq0} ∧
    (∑ i : Fin 2, affine (sourceA i) (sourceB i) (sourceQ0 i) (sourceQ1 i) ${ov}) = ${oq1} := by
  norm_num [Fin.sum_univ_succ, sourceA, sourceB, sourceQ0, sourceQ1, affine]

example : (∫ t in ${ou}..${ov}, overlapDensity.eval t) =
    (${ov}-${ou}) * (∫ z in (0:ℝ)..1, intervalAffine ${oq0} ${oq1} z *
      (X^3 : Polynomial ℝ).eval (pullback ${ou} ${ov} z)) := by
  have h := overlap_interval_work (Fin 2) sourceA sourceB sourceQ0 sourceQ1 ${ou} ${ov} 1
    overlapDensity (X^3) (by norm_num) (by intro i; fin_cases i <;> norm_num [sourceA, sourceB])
    (by intro i; fin_cases i <;> norm_num [sourceA, sourceB]) (by
      intro t
      simp [Fin.sum_univ_succ, sourceA, sourceB, sourceQ0, sourceQ1, overlapDensity, affine]
      ring)
  rw [overlapEndpoints.1, overlapEndpoints.2] at h
  simpa using h

def familyA : Fin 3 → Fin 2 → ℝ := ${familyA}
def familyB : Fin 3 → Fin 2 → ℝ := ${familyB}
def familyQ0 : Fin 3 → Fin 2 → ℝ := ${familyQ0}
def familyQ1 : Fin 3 → Fin 2 → ℝ := ${familyQ1}
def familyU : Fin 3 → ℝ := ${familyU}
def familyV : Fin 3 → ℝ := ${familyV}
def familyStart : Fin 3 → ℝ := ${familyStart}
def familyEnd : Fin 3 → ℝ := ${familyEnd}
def familyDensity : Fin 3 → Polynomial ℝ := fun k =>
  if k = 0 then 8*X^4-4*X^3 else if k = 1 then 4*X^4-X^3 else 3*X^3-4*X^4

theorem familyEndpoints (k : Fin 3) :
    (∑ i : Fin 2, affine (familyA k i) (familyB k i) (familyQ0 k i) (familyQ1 k i) (familyU k)) = familyStart k ∧
    (∑ i : Fin 2, affine (familyA k i) (familyB k i) (familyQ0 k i) (familyQ1 k i) (familyV k)) = familyEnd k := by
  fin_cases k <;> norm_num [Fin.sum_univ_succ, familyA, familyB, familyQ0, familyQ1,
    familyU, familyV, familyStart, familyEnd, affine]

example : (∑ k : Fin 3, (∫ t in familyU k..familyV k, (familyDensity k).eval t)) =
    ∑ k : Fin 3, (familyV k-familyU k) * (∫ z in (0:ℝ)..1,
      intervalAffine (familyStart k) (familyEnd k) z * (X^3 : Polynomial ℝ).eval (pullback (familyU k) (familyV k) z)) := by
  have h := overlap_finite_interval_work (Fin 3) (Fin 2) familyA familyB familyQ0 familyQ1 familyU familyV 1
    familyDensity (X^3)
    (by intro k; fin_cases k <;> norm_num [familyU, familyV])
    (by intro k i; fin_cases k <;> fin_cases i <;> norm_num [familyA, familyB])
    (by intro k i; fin_cases k <;> fin_cases i <;> norm_num [familyA, familyB, familyU, familyV])
    (by intro k t; fin_cases k <;> simp [Fin.sum_univ_succ, familyA, familyB, familyQ0, familyQ1,
      familyDensity, affine] <;> ring)
  simp only [one_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [(familyEndpoints k).1, (familyEndpoints k).2]

def overlapLocalDofs : FrameInterfaces.LocalDofs := ![0, 1/8, 3/4, 0, 27/64, 27/16]
def overlapVirtual : Polynomial ℝ := (C ${ou} + C (${ov}-${ou}) * X)^3
def localSourceQ0 : Fin 2 → ℝ := fun i => if i = 0 then ${restricted00} else ${restricted10}
def localSourceQ1 : Fin 2 → ℝ := fun i => if i = 0 then ${restricted01} else ${restricted11}
def localA : Fin 2 → ℝ := fun _ => 0
def localB : Fin 2 → ℝ := fun _ => 1

example : (∑ i : Fin 6, LocalFrameFields.consistentLoad (${ov}-${ou}) 0 0 ${oq0} ${oq1} i * overlapLocalDofs i) =
    (${ov}-${ou}) * (∫ z in (0:ℝ)..1, intervalAffine ${oq0} ${oq1} z * overlapVirtual.eval z) := by
  have h := overlap_rotated_consistent_work (Fin 2) localA localB localSourceQ0 localSourceQ1
    overlapLocalDofs (${ov}-${ou}) 1 0 ${oq0} ${oq1} overlapVirtual
    (by intro i; norm_num [localA, localB]) (by intro i; norm_num [localA, localB]) (by
      intro t
      simp [FrameVirtualWork.loadDensity, FrameVirtualWork.axialShape, FrameVirtualWork.transverseShape,
        overlapLocalDofs, overlapVirtual, localA, localB, localSourceQ0, localSourceQ1,
        Fin.sum_univ_succ, affine]
      ring)
  norm_num [localA, localB, localSourceQ0, localSourceQ1, Fin.sum_univ_succ, affine, pullback] at h ⊢
  exact h

-- For this nonzero work, omitting the Jacobian changes the value fourfold.
example : (∫ t in ${ou}..${ov}, overlapDensity.eval t) ≠
    (∫ z in (0:ℝ)..1, intervalAffine ${oq0} ${oq1} z * (X^3 : Polynomial ℝ).eval (pullback ${ou} ${ov} z)) := by
  norm_num [overlapDensity, intervalAffine, pullback, Polynomial.eval_sub, Polynomial.eval_mul,
    intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]


def releasedModel : Model 3 2 0 2 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun i => if i = 0 then ⟨1, 0, ⟨1, 0⟩, none, none⟩
    else ⟨0, 2, ⟨1, 0⟩, some ⟨.released, .spring ${sideSpring}, .released⟩, none⟩
  segmentMember := fun i => i
  segmentLeft := fun i => .endSide (i, false)
  segmentRight := fun i => .endSide (i, true)
  segmentLength := fun _ => 1
  segmentEA := fun _ => 1
  segmentEI := fun _ => 1
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def sideRotation : Coordinate releasedModel → ℝ := fun coordinate =>
  match coordinate with
  | .inl _ => 0
  | .inr slip => if slip.val.1 = (1, false) ∧ slip.val.2 = 2 then 1 else 0

def sideCouple : PointAction 2 0 := ⟨.endSide (1, false), ![0, 0, ${sideMoment}]⟩
def hubCouple : PointAction 2 0 := ⟨.endSide (0, true), ![0, 0, ${sideMoment}]⟩
def sideSupport : SupportInput 2 0 := ⟨.endSide (1, false), .fixed, 0, 0, false, false, false⟩
def hubSupport : SupportInput 2 0 := ⟨.endSide (0, true), .fixed, 0, 0, false, false, false⟩

theorem rotationReleased : directionLaw (endConnection releasedModel (1, false)) 2 = .released := by rfl
example : directionLaw (endConnection releasedModel (1, false)) 0 = .released := by rfl
example : directionLaw (endConnection releasedModel (1, false)) 1 = .spring ${sideSpring} := by rfl
theorem rotationSlip : hasSlip releasedModel (1, false) 2 := by
  constructor
  · exact ⟨1, Or.inl rfl⟩
  · rw [rotationReleased]
    intro h
    cases h

theorem releasedSideMotion : sideMotion releasedModel sideRotation (.endSide (1, false)) = ![0, 0, 1] := by
  classical
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, sideRotation,
    releasedModel, endNode, rotationSlip] <;> try split_ifs <;> try norm_num <;> try contradiction
  all_goals exact rotationSlip

theorem hubSideMotion : sideMotion releasedModel sideRotation (.endSide (0, true)) = 0 := by
  classical
  funext i
  fin_cases i <;> simp [sideMotion, referenceMotion, endMotion, slipValue, sideRotation,
    releasedModel, endNode] <;> split_ifs <;> norm_num

example : pointActionWork releasedModel sideCouple sideRotation = ${sideMoment} := by
  simp [pointActionWork, sideCouple, FrameTransform.work, releasedSideMotion]
example : pointActionWork releasedModel hubCouple sideRotation = 0 := by
  simp [pointActionWork, hubCouple, FrameTransform.work, hubSideMotion]
example : supportRow releasedModel sideSupport (![0, 0, 1]) sideRotation = 1 := by
  simp [supportRow, sideSupport, FrameTransform.work, releasedSideMotion]
example : supportRow releasedModel hubSupport (![0, 0, 1]) sideRotation = 0 := by
  simp [supportRow, hubSupport, FrameTransform.work, hubSideMotion]

-- Equal resultant and first moment do not determine work against t^3.
example : (∫ t in (0:ℝ)..1, t^3) = 1/4 := by
  norm_num [integral_pow]
example : (∫ t in (0:ℝ)..(1/2), 4*t^4) + (∫ t in (1/2:ℝ)..1, (4*t^3-4*t^4)) = 3/16 := by
  have hleft : (∫ t in (0:ℝ)..(1/2), 4*t^4) = 1/40 := by
    rw [intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
  have hright : (∫ t in (1/2:ℝ)..1, (4*t^3-4*t^4)) = 13/80 := by
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      norm_num [integral_pow]
    · exact (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _
  linarith

`;
await writeFile(target, source, 'utf8');
console.log(`Generated synthetic adapter fixture from artifact ${artifact.artifactDigest}`);

