/** Generate only fixed synthetic expressions; never interpolate source IDs. */
import { registerHooks } from 'node:module';
import { writeFile } from 'node:fs/promises';
import { emitExactExpression as emit } from './exact-geometry-expressions.mjs';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { createEvidenceEnvelope } = await import('../web/model-evidence.ts');
const { adaptEvidenceSnapshot, verifyExactCutArtifact } = await import('../web/exact-cut-adapter.ts');
const target = process.argv[2];
if (!target) throw Error('A temporary fixture path is required');
const model = {
    nodes: [{ id: 'a', x: 2, y: 3 }, { id: 'b', x: 3, y: 4 }],
    members: [
        { id: 'forward', a: 'a', b: 'b', EA: 2, EI: 3 },
        { id: 'reverse', a: 'b', b: 'a', EA: 2, EI: 3,
            connectionA: { axial: 'free', transverse: 7, rotation: 'free' } },
    ],
    supports: [
        { id: 'guided', member: 'forward', t: 0.5, kind: 'guided', angle: 37 },
        { id: 'custom', member: 'reverse', t: 0, kind: 'custom', angle: 19,
            fixX: true, fixY: false, fixRotation: false },
    ],
    loads: [{ id: 'nearby', member: 'forward', t: 0.5 + 2 ** -30, end: 1,
        kind: 'force', fx: 0, fy: 1, mz: 0, qEnd: 0 }],
};
const query = { member: 'forward', parameter: 0.5, cutSide: 'left', quantity: 'M',
    units: 'kN m', signConvention: 'sagging positive' };
const envelope = await createEvidenceEnvelope(model, query);
const artifact = await adaptEvidenceSnapshot(envelope);
await verifyExactCutArtifact(envelope, artifact);
if (artifact.status !== 'pending-not-formally-verified' || artifact.bindings.checker !== null || artifact.bindings.result !== null)
    throw Error('Synthetic evidence status changed');
// Recompute binding rejects semantically altered synthetic expressions; this
// is an untrusted consistency check, not a proof of the TypeScript compiler.
for (const mutate of [
    copy => { copy.members[0].geometry.cosine.args[0].numerator = '-1'; },
    copy => { copy.supports[0].axes.cosine.args[0].args[1].args[1].numerator = '181'; },
    copy => { copy.members[0].cuts[1].position.x.args[0].numerator = '3'; },
]) {
    const changed = structuredClone(artifact);
    mutate(changed);
    let rejected = false;
    try { await verifyExactCutArtifact(envelope, changed); } catch { rejected = true; }
    if (!rejected) throw Error('Altered synthetic geometry unexpectedly accepted');
}
const first = artifact.members[0], second = artifact.members[1], guided = artifact.supports[0];
if (first.cuts.length !== 4 || first.intervals.length !== 3 || guided.cutIndex !== 1 ||
    second.endLaws[0].transverse.kind !== 'spring') throw Error('Synthetic fixture topology changed');
const position = cut => `(${emit(cut.position.x)}, ${emit(cut.position.y)})`;
const artifactHash = artifact.artifactDigest;
if (!/^[a-f0-9]{64}$/.test(artifactHash)) throw Error('Invalid artifact digest');
const source = `-- Synthetic adapter artifact SHA-256: ${artifactHash}
import ExactGeometry
open Polynomial FrameInterfaces FrameTransform FrameAssemblyModel ExactGeometry
noncomputable section

def a : Point := (${emit(artifact.nodes[0].x)}, ${emit(artifact.nodes[0].y)})
def b : Point := (${emit(artifact.nodes[1].x)}, ${emit(artifact.nodes[1].y)})
def emittedDX : ℝ := ${emit(first.geometry.dx)}
def emittedDY : ℝ := ${emit(first.geometry.dy)}
def emittedLength : ℝ := ${emit(first.geometry.length)}
def emittedCos : ℝ := ${emit(first.geometry.cosine)}
def emittedSin : ℝ := ${emit(first.geometry.sine)}
def emittedCut1 : ℝ := ${emit(first.cuts[1].parameter)}
def emittedCut2 : ℝ := ${emit(first.cuts[2].parameter)}
def emittedPoint1 : Point := ${position(first.cuts[1])}
def emittedPoint2 : Point := ${position(first.cuts[2])}
def emittedSpan : ℝ := ${emit(first.intervals[1].length)}
def emittedAngle : ℝ := ${emit(guided.axes.angleDegrees)}
def emittedAxisCos : ℝ := ${emit(guided.axes.cosine)}
def emittedAxisSin : ℝ := ${emit(guided.axes.sine)}
def reversedCos : ℝ := ${emit(second.geometry.cosine)}
def reversedSin : ℝ := ${emit(second.geometry.sine)}
def reversedLength : ℝ := ${emit(second.geometry.length)}

example : a ≠ b := by norm_num [a, b]
example : emittedDX = dx a b ∧ emittedDY = dy a b := by norm_num [emittedDX, emittedDY, dx, dy, a, b]
example : emittedLength = distance a b := by norm_num [emittedLength, distance, dx, dy, a, b]
example : emittedCos = (direction a b).cosine ∧ emittedSin = (direction a b).sine := by
  norm_num [emittedCos, emittedSin, direction, distance, dx, dy, a, b]
example : emittedPoint1 = position a b emittedCut1 ∧ emittedPoint2 = position a b emittedCut2 := by
  norm_num [emittedPoint1, emittedPoint2, emittedCut1, emittedCut2, position, dx, dy, a, b]
example : emittedCut1 < emittedCut2 := by norm_num [emittedCut1, emittedCut2]
example : emittedSpan = distance (position a b emittedCut1) (position a b emittedCut2) := by
  rw [segment_distance a b emittedCut1 emittedCut2 (by norm_num [emittedCut1, emittedCut2])]
  norm_num [emittedSpan, emittedCut1, emittedCut2, distance, dx, dy, a, b] <;> ring
example : emittedAxisCos = degreeCos emittedAngle ∧ emittedAxisSin = degreeSin emittedAngle := by
  norm_num [emittedAxisCos, emittedAxisSin, emittedAngle, degreeCos, degreeSin]
example : emittedAxisCos^2 + emittedAxisSin^2 = 1 := by
  have h := degree_axis_normalized emittedAngle
  simpa [emittedAxisCos, emittedAxisSin, emittedAngle, degreeCos, degreeSin] using h
example : reversedLength = emittedLength ∧ reversedCos = -emittedCos ∧ reversedSin = -emittedSin := by
  norm_num [reversedLength, reversedCos, reversedSin, emittedLength, emittedCos, emittedSin] <;> ring
-- A finite model instance. The structural obligations are explicit and are
-- discharged for this synthetic encoding only; they do not verify a builder.
def syntheticModel : Model 2 2 1 3 where
  joints := fun _ => ⟨.rigid, 1, none⟩
  member := fun m => if m.val = 0 then ⟨0, 1, ⟨emittedCos, emittedSin⟩, none, none⟩
    else ⟨1, 0, ⟨reversedCos, reversedSin⟩, some ⟨.released, .spring ${emit(second.endLaws[0].transverse.stiffness)}, .released⟩, none⟩
  segmentMember := fun s => if s.val = 2 then 1 else 0
  segmentLeft := fun s => if s.val = 0 then .endSide (0, false) else if s.val = 1 then .interior 0 0 else .endSide (1, false)
  segmentRight := fun s => if s.val = 0 then .interior 0 0 else if s.val = 1 then .endSide (0, true) else .endSide (1, true)
  segmentLength := fun s => if s.val = 0 then distance a emittedPoint1 else if s.val = 1 then distance emittedPoint1 b else distance b a
  segmentEA := fun _ => ${emit(first.intervals[0].EA)}
  segmentEI := fun _ => ${emit(first.intervals[0].EI)}
  segmentVerticalStart := fun _ => 0
  segmentVerticalEnd := fun _ => 0

def cutParam : Fin 2 → Fin 1 → ℝ := fun _ _ => emittedCut1
def syntheticActions : Fin 1 → PointAction 2 1 := fun _ => ⟨.interior 0 0, ![0, 1, 0]⟩
def syntheticSupports : Fin 2 → SupportInput 2 1 := fun s => if s.val = 0 then
  ⟨.interior 0 0, .guided, emittedAxisCos, emittedAxisSin, false, false, false⟩
  else ⟨.endSide (1, false), .custom, 0, 0, true, false, false⟩
def nodePos : Fin 2 → Point := fun n => if n.val = 0 then a else b
def memberEA : Fin 2 → ℝ := fun _ => ${emit(first.intervals[0].EA)}
def memberEI : Fin 2 → ℝ := fun _ => ${emit(first.intervals[0].EI)}
def segmentStart : Fin 3 → Point := fun s => if s.val = 0 then a else if s.val = 1 then emittedPoint1 else b
def segmentEnd : Fin 3 → Point := fun s => if s.val = 0 then emittedPoint1 else if s.val = 1 then b else a
def supportAngles : Fin 2 → ℝ := fun _ => emittedAngle

example : supportDirections (syntheticSupports 0) =
    [![0, 0, 1], ![emittedAxisCos, emittedAxisSin, 0]] := by rfl
example : supportDirections (syntheticSupports 1) = [![1, 0, 0]] := by rfl
example : ¬ 0 < distance a a := by norm_num [distance, dx, dy]
example : ¬ 0 < (0:ℝ) ∧ ¬ 0 < (-1:ℝ) := by norm_num
example : ¬ ((-2:ℝ) > 0) ∧ ¬ ((-7:ℝ) > 0) := by norm_num
example : (1:ℝ)^2 + (1:ℝ)^2 ≠ 1 := by norm_num
example : distance a b * (1:ℝ) ≠ dx a b := by
  have hs := distance_squared a b
  norm_num [a, b, dx, dy] at hs ⊢
  nlinarith

example (q : Coordinate syntheticModel → ℝ) :
    supportRow syntheticModel (syntheticSupports 0) ![0, 0, 1] q =
      sideMotion syntheticModel q (.interior 0 0) 2 := by
  simp [supportRow, syntheticSupports, FrameTransform.work]
example (q : Coordinate syntheticModel → ℝ) :
    supportRow syntheticModel (syntheticSupports 0) ![emittedAxisCos, emittedAxisSin, 0] q =
      emittedAxisCos * sideMotion syntheticModel q (.interior 0 0) 0 +
        emittedAxisSin * sideMotion syntheticModel q (.interior 0 0) 1 := by
  simp [supportRow, syntheticSupports, FrameTransform.work]

theorem syntheticStructure : StructuralPremises syntheticModel syntheticActions syntheticSupports cutParam := by
  constructor
  · intro segment
    fin_cases segment <;> simp [segmentOwnershipValid, locationBelongs, syntheticModel]
  · intro segment
    fin_cases segment <;> norm_num [syntheticModel, locationParameter, cutParam, emittedCut1]
  · intro member t ht0 ht1
    fin_cases member
    · by_cases ht : t ≤ 1/2
      · refine ⟨0, ?_⟩
        norm_num [syntheticModel, locationParameter, cutParam, emittedCut1]
        constructor <;> linarith
      · refine ⟨1, ?_⟩
        norm_num [syntheticModel, locationParameter, cutParam, emittedCut1]
        constructor <;> linarith
    · refine ⟨2, ?_⟩
      norm_num [syntheticModel, locationParameter]
      exact ⟨ht0, ht1⟩
  · intro x y hxy hm
    fin_cases x <;> fin_cases y <;> norm_num [syntheticModel, locationParameter, cutParam, emittedCut1] at *
  · intro member left right hl hr hleft hright hpos
    have lc : left = .endSide (0, false) ∨ left = .interior 0 0 ∨ left = .endSide (0, true) ∨
        left = .endSide (1, false) ∨ left = .endSide (1, true) := by
      obtain ⟨i, hi⟩ := hleft
      fin_cases i <;> simp [syntheticModel] at hi <;> aesop
    have rc : right = .endSide (0, false) ∨ right = .interior 0 0 ∨ right = .endSide (0, true) ∨
        right = .endSide (1, false) ∨ right = .endSide (1, true) := by
      obtain ⟨i, hi⟩ := hright
      fin_cases i <;> simp [syntheticModel] at hi <;> aesop
    rcases lc with rfl | rfl | rfl | rfl | rfl <;> rcases rc with rfl | rfl | rfl | rfl | rfl <;>
      fin_cases member <;> norm_num [locationBelongs, locationParameter, cutParam, emittedCut1] at *
  · intro member
    fin_cases member
    · exact ⟨⟨0, Or.inl rfl⟩, ⟨1, Or.inr rfl⟩⟩
    · exact ⟨⟨2, Or.inl rfl⟩, ⟨2, Or.inr rfl⟩⟩
  · intro member cut hc
    fin_cases member <;> fin_cases cut <;> norm_num [cutParam, emittedCut1]
  · intro action
    fin_cases action
    exact ⟨0, Or.inr rfl⟩
  · intro support
    fin_cases support
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨2, Or.inl rfl⟩

theorem syntheticGeometry : GeometryCorrespondence syntheticModel nodePos cutParam memberEA memberEI segmentStart segmentEnd := by
  constructor
  · intro m
    fin_cases m <;> norm_num [syntheticModel, nodePos, direction, distance, dx, dy, a, b,
      emittedCos, emittedSin, reversedCos, reversedSin, emittedLength] <;> ring
  · intro s
    fin_cases s <;> norm_num [syntheticModel, segmentStart, nodePos, position, locationParameter,
      cutParam, emittedCut1, emittedPoint1, a, b, dx, dy]
  · intro s
    fin_cases s <;> norm_num [syntheticModel, segmentEnd, nodePos, position, locationParameter,
      cutParam, emittedCut1, emittedPoint1, a, b, dx, dy]
  · intro s
    fin_cases s <;> simp [syntheticModel, segmentStart, segmentEnd]
  · intro s
    fin_cases s <;> norm_num [syntheticModel, memberEA, memberEI]

example : segmentEnd 0 = segmentStart 1 := by
  apply correspondence_shared_join syntheticModel nodePos cutParam memberEA memberEI segmentStart segmentEnd syntheticGeometry 0 1
  · rfl
  · rfl

def badPropertyModel : Model 2 2 1 3 := { syntheticModel with segmentEA := fun _ => -2 }
example : ¬ GeometryCorrespondence badPropertyModel nodePos cutParam memberEA memberEI segmentStart segmentEnd := by
  intro geometry
  have h := (geometry.properties 0).1
  norm_num [badPropertyModel, memberEA] at h

def badLengthModel : Model 2 2 1 3 := { syntheticModel with segmentLength := fun _ => emittedLength }
example : ¬ GeometryCorrespondence badLengthModel nodePos cutParam memberEA memberEI segmentStart segmentEnd := by
  intro geometry
  have h := geometry.length 0
  norm_num [badLengthModel, segmentStart, segmentEnd, emittedLength, emittedPoint1, distance, dx, dy, a, b] at h
  field_simp at h

def badSpringModel : Model 2 2 1 3 := { syntheticModel with member := fun m => if m.val = 0 then
  ⟨0, 1, ⟨emittedCos, emittedSin⟩, none, none⟩
  else ⟨1, 0, ⟨reversedCos, reversedSin⟩, some ⟨.released, .spring (-7), .released⟩, none⟩ }
example : ¬ EffectiveSpringPositive badSpringModel := by
  intro positive
  have h := positive (1, false) 1 (-7) (by exact ⟨2, Or.inl rfl⟩) (by rfl)
  norm_num at h

theorem syntheticSupportAxes : SupportAxisCorrespondence syntheticSupports supportAngles := by
  intro s hs
  fin_cases s
  · norm_num [syntheticSupports, supportAngles, emittedAngle, emittedAxisCos, emittedAxisSin, degreeCos, degreeSin]
  · simp [syntheticSupports] at hs

theorem syntheticSprings : SpringInputPositive syntheticModel := by
  constructor
  · intro side connection direction stiffness choice law
    rcases side with ⟨member, ending⟩
    fin_cases member <;> cases ending <;> simp [syntheticModel] at choice
    all_goals cases choice
    all_goals fin_cases direction <;> simp [directionLaw] at law <;> subst stiffness <;> norm_num
  · intro node h
    fin_cases node <;> simp [syntheticModel] at h

example : ExactContract syntheticModel syntheticActions syntheticSupports cutParam
    (memberDistance syntheticModel nodePos) memberEA memberEI := by
  have h := compose_exact_contract syntheticModel syntheticActions syntheticSupports cutParam
    nodePos memberEA memberEI segmentStart segmentEnd supportAngles syntheticStructure syntheticGeometry
    (by intro m; fin_cases m <;> norm_num [syntheticModel, nodePos, a, b])
    (by intro m; norm_num [memberEA]) (by intro m; norm_num [memberEI]) syntheticSupportAxes syntheticSprings
  exact h.1

example (v : Triple) : toGlobal emittedCos emittedSin (toLocal emittedCos emittedSin v) = v := by
  apply inverse_transform
  have h := direction_normalized a b (by norm_num [a,b])
  norm_num [emittedCos, emittedSin, direction, distance, dx, dy, a, b] at h ⊢
`;
await writeFile(target, source, 'utf8');
console.log(`Generated synthetic geometry fixture from artifact ${artifactHash}`);
