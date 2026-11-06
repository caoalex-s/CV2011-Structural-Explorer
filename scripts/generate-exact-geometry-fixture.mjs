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

def a : Point := (2, 3)
def b : Point := (3, 4)
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
  norm_num [emittedSpan, emittedCut1, emittedCut2, distance, dx, dy, a, b]
example : emittedAxisCos = degreeCos emittedAngle ∧ emittedAxisSin = degreeSin emittedAngle := by
  norm_num [emittedAxisCos, emittedAxisSin, emittedAngle, degreeCos, degreeSin]
example : emittedAxisCos^2 + emittedAxisSin^2 = 1 := by
  have h := degree_axis_normalized emittedAngle
  simpa [emittedAxisCos, emittedAxisSin, emittedAngle, degreeCos, degreeSin] using h
example : reversedLength = emittedLength ∧ reversedCos = -emittedCos ∧ reversedSin = -emittedSin := by
  norm_num [reversedLength, reversedCos, reversedSin, emittedLength, emittedCos, emittedSin]
example (v : Triple) : toGlobal emittedCos emittedSin (toLocal emittedCos emittedSin v) = v := by
  apply inverse_transform
  have h := direction_normalized a b (by norm_num [a,b])
  simpa [emittedCos, emittedSin, direction, distance, dx, dy, a, b] using h
`;
await writeFile(target, source, 'utf8');
console.log(`Generated synthetic geometry fixture from artifact ${artifactHash}`);
