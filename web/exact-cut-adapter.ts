/** Exact, untrusted member segmentation for a frozen evidence snapshot.
 * No solver, verifier, network call or mutation of the input is performed here. */
import { createEvidenceEnvelope, parseEvidenceModel } from './model-evidence.js';
import { endConnection, referenceMember } from './engine.js';
import type { ConnectionRule, Load, Model, Support } from './engine.js';

type Rat = { n: bigint; d: bigint };
type EncodedRat = { numerator: string; denominator: string };
type Expression = { op: string; args: (Expression | EncodedRat)[] };
type Source = { kind: 'member-end' | 'support' | 'force' | 'moment' | 'distributed'; index: number; id: string; role: string };
type ExactLocation = { kind: 'endSide'; memberIndex: number; end: 'a' | 'b'; nodeId: string } |
    { kind: 'interior'; memberIndex: number; cutIndex: number };

const numericSemantics = 'parsed-finite-binary64-as-exact-binary-rational; signed-zero-normalized';
const implementationIdentity = 'cv2011-exact-member-cut-adapter/1';
const enginePolicy = 'engine.ts/toFixed-8-endpoint-1e-8-map-cutoff-1e-15/v1';

function gcd(a: bigint, b: bigint): bigint {
    while (b !== 0n) [a, b] = [b, a % b];
    return a < 0n ? -a : a;
}
function rat(n: bigint, d = 1n): Rat {
    if (d === 0n) throw Error('Zero rational denominator');
    if (d < 0n) { n = -n; d = -d; }
    const factor = gcd(n, d);
    return { n: n / factor, d: d / factor };
}
const add = (a: Rat, b: Rat) => rat(a.n * b.d + b.n * a.d, a.d * b.d);
const neg = (a: Rat) => rat(-a.n, a.d);
const sub = (a: Rat, b: Rat) => add(a, neg(b));
const mul = (a: Rat, b: Rat) => rat(a.n * b.n, a.d * b.d);
const div = (a: Rat, b: Rat) => rat(a.n * b.d, a.d * b.n);
const compare = (a: Rat, b: Rat) => a.n * b.d < b.n * a.d ? -1 : a.n * b.d > b.n * a.d ? 1 : 0;
const encode = (value: Rat): EncodedRat => ({ numerator: value.n.toString(), denominator: value.d.toString() });
const key = (value: Rat) => `${value.n}/${value.d}`;
const zero = rat(0n), one = rat(1n), two = rat(2n), three = rat(3n), six = rat(6n);
const expr = (op: string, ...args: (Expression | EncodedRat)[]): Expression => ({ op, args });

/** Decode IEEE-754 bits, including subnormals, without a decimal conversion. */
export function exactBinary64(value: number): EncodedRat {
    return encode(fromBinary64(value));
}
function fromBinary64(value: number): Rat {
    if (!Number.isFinite(value)) throw Error('Expected a finite binary64 number');
    if (value === 0) return zero;
    const buffer = new ArrayBuffer(8), view = new DataView(buffer);
    view.setFloat64(0, value, false);
    const bits = view.getBigUint64(0, false);
    const sign = (bits >> 63n) === 0n ? 1n : -1n;
    const exponent = Number((bits >> 52n) & 0x7ffn);
    const fraction = bits & ((1n << 52n) - 1n);
    const mantissa = exponent === 0 ? fraction : (1n << 52n) + fraction;
    const power = exponent === 0 ? -1074 : exponent - 1023 - 52;
    return power >= 0 ? rat(sign * (mantissa << BigInt(power))) : rat(sign * mantissa, 1n << BigInt(-power));
}
function canonical(value: unknown): string {
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return JSON.stringify(value);
    if (typeof value === 'number' && Number.isFinite(value)) return JSON.stringify(value === 0 ? 0 : value);
    if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
    if (value && typeof value === 'object') return `{${Object.entries(value as Record<string, unknown>)
        .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
        .map(([name, child]) => `${JSON.stringify(name)}:${canonical(child)}`).join(',')}}`;
    throw Error('Unsupported artifact value');
}
async function sha256(value: string): Promise<string> {
    const digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(value));
    return [...new Uint8Array(digest)].map(byte => byte.toString(16).padStart(2, '0')).join('');
}
function deepFreeze<T>(value: T): T {
    if (value && typeof value === 'object') {
        for (const child of Object.values(value)) deepFreeze(child);
        Object.freeze(value);
    }
    return value;
}
function connectionRule(rule: ConnectionRule) {
    return typeof rule === 'number' ? { kind: 'spring', stiffness: encode(fromBinary64(rule)) } : { kind: rule };
}
function endLaw(model: Model, memberIndex: number, end: 'a' | 'b') {
    const member = model.members[memberIndex], nodeId = member[end];
    const node = model.nodes.find(item => item.id === nodeId)!;
    const reference = referenceMember(model, nodeId)!;
    const explicit = end === 'a' ? member.connectionA : member.connectionB;
    const reason = reference === member.id ? 'reference-rigid' : explicit ? 'explicit' :
        node.joint === 'pinned' ? 'pinned-default' : node.joint === 'semi-rigid' ? 'semi-rigid-default' : 'rigid-default';
    const law = endConnection(model, member, end);
    return { end, nodeId, requestedReference: node.referenceMember ?? null, effectiveReference: reference,
        referenceReason: node.referenceMember === undefined ? 'first-incident' : 'requested', reason,
        axial: connectionRule(law.axial), transverse: connectionRule(law.transverse), rotation: connectionRule(law.rotation) };
}
function axes(support: Support) {
    const angle = encode(fromBinary64(support.angle));
    const radians = expr('multiply', angle, expr('divide', expr('pi'), encode(rat(180n))));
    return { angleDegrees: angle, cosine: expr('cos', radians), sine: expr('sin', radians),
        status: support.kind === 'roller' || support.kind === 'guided' ? 'pending-exact-trigonometry' : 'not-required' };
}
function supportRows(support: Support) {
    const fixedX = [encode(one), encode(zero), encode(zero)];
    const fixedY = [encode(zero), encode(one), encode(zero)];
    const fixedRotation = [encode(zero), encode(zero), encode(one)];
    const inclined = [axes(support).cosine, axes(support).sine, encode(zero)];
    if (support.kind === 'pin') return [fixedX, fixedY];
    if (support.kind === 'fixed') return [fixedX, fixedY, fixedRotation];
    if (support.kind === 'roller') return [inclined];
    if (support.kind === 'guided') return [fixedRotation, inclined];
    return [support.fixX ? fixedX : null, support.fixY ? fixedY : null,
        support.fixRotation ? fixedRotation : null].filter(row => row !== null);
}
function location(memberIndex: number, member: Model['members'][number], cutIndex: number, t: Rat): ExactLocation {
    if (compare(t, zero) === 0) return { kind: 'endSide', memberIndex, end: 'a', nodeId: member.a };
    if (compare(t, one) === 0) return { kind: 'endSide', memberIndex, end: 'b', nodeId: member.b };
    return { kind: 'interior', memberIndex, cutIndex };
}
function loadValue(load: Load, t: Rat): Rat {
    const a = fromBinary64(load.t), b = fromBinary64(load.end);
    const qa = fromBinary64(load.fy), qb = fromBinary64(load.qEnd);
    return add(qa, mul(sub(qb, qa), div(sub(t, a), sub(b, a))));
}
function resultantCoefficient(u: Rat, v: Rat, q0: Rat, q1: Rat): Rat {
    return div(mul(sub(v, u), add(q0, q1)), two);
}
function firstMomentCoefficient(u: Rat, v: Rat, q0: Rat, q1: Rat): Rat {
    const width = sub(v, u);
    return add(mul(u, resultantCoefficient(u, v, q0, q1)),
        div(mul(mul(width, width), add(q0, mul(two, q1))), six));
}
function encodeComponents(load: Load) {
    const fx = load.kind === 'force' ? fromBinary64(load.fx) : zero;
    const fy = load.kind === 'force' ? fromBinary64(load.fy) : zero;
    const mz = load.kind === 'moment' ? fromBinary64(load.mz) : zero;
    return { fx: encode(fx), fy: encode(fy), mz: encode(mz) };
}
function sourceFields(load: Load) {
    return { t: encode(fromBinary64(load.t)), end: encode(fromBinary64(load.end)), fx: encode(fromBinary64(load.fx)),
        fy: encode(fromBinary64(load.fy)), mz: encode(fromBinary64(load.mz)), qEnd: encode(fromBinary64(load.qEnd)) };
}
function obligations(memberIndex: number, intervals: unknown[], cuts: unknown[], actions: unknown[], supports: unknown[], geometry: unknown, endLaws: unknown, properties: unknown) {
    const entries = [
        ['ownership', 'preflight-witness', { memberIndex, intervals }],
        ['ordered', 'preflight-witness', { memberIndex, cuts }],
        ['coverage', 'preflight-witness', { memberIndex, cuts }],
        ['disjointInteriors', 'preflight-witness', { memberIndex, intervals }],
        ['canonicalLocations', 'preflight-witness', { memberIndex, cuts }],
        ['memberEnds', 'preflight-witness', { memberIndex, cuts }],
        ['interiorCuts', 'preflight-witness', { memberIndex, cuts }],
        ['actionLocations', 'preflight-witness', { memberIndex, actions }],
        ['supportLocations', 'preflight-witness', { memberIndex, supports }],
        ['orientationNormalized', 'pending-geometry-proof', { memberIndex, geometry }],
        ['supportNormalized', 'pending-trigonometric-proof', { memberIndex, supports }],
        ['positiveMember', 'pending-expression-proof', { memberIndex, geometry, properties }],
        ['segmentLengthMatches', 'pending-expression-proof', { memberIndex, intervals }],
        ['segmentPropertiesMatch', 'preflight-witness', { memberIndex, intervals }],
        ['positiveSpring', 'preflight-witness', { memberIndex, endLaws }],
        ['endpointGeometryCorrespondence', 'pending-geometry-proof', { memberIndex, geometry, cuts }],
    ] as const;
    const genericTheorems: Record<string, string> = { ordered: 'MemberCutAdapter.chain_interval_bounds',
        coverage: 'MemberCutAdapter.chain_coverage', disjointInteriors: 'MemberCutAdapter.chain_disjoint_interiors' };
    return entries.map(([name, status, witness]) => ({ name, proposition: name === 'endpointGeometryCorrespondence' ? 'endpoint geometry correspondence (adapter schema)' : `ExactContract.${name}`,
        status, theorem: genericTheorems[name] ?? null, witness, checkedInstance: false }));
}

/** Create a locally bound exact artifact. A digest identifies an untrusted
 * adapter output; it is not a checked model, proof receipt or solver certificate. */
export async function adaptEvidenceSnapshot(input: Awaited<ReturnType<typeof createEvidenceEnvelope>>) {
    const captured = structuredClone(input);
    if (captured.schema !== 'cv2011-local-evidence' || captured.version !== 1 ||
        captured.numericSemantics !== numericSemantics || captured.status !== 'pending-not-formally-verified') throw Error('Unsupported evidence snapshot');
    const snapshot = await createEvidenceEnvelope(captured.model, captured.query);
    for (const part of ['mechanical', 'display', 'query'] as const) {
        if (captured.bindings[part] !== snapshot.bindings[part]) throw Error(`Stale ${part} binding`);
    }
    if (captured.bindings.rawSource !== null && !/^[a-f0-9]{64}$/.test(captured.bindings.rawSource)) throw Error('Invalid raw source binding');
    const model = parseEvidenceModel(snapshot.model);
    const allActions: unknown[] = [], allSupports: unknown[] = [], members: unknown[] = [], discrepancies: unknown[] = [];
    for (const [memberIndex, member] of model.members.entries()) {
        const a = model.nodes.find(node => node.id === member.a)!, b = model.nodes.find(node => node.id === member.b)!;
        const xa = fromBinary64(a.x), ya = fromBinary64(a.y), dx = sub(fromBinary64(b.x), xa), dy = sub(fromBinary64(b.y), ya);
        const length = expr('sqrt', expr('add', expr('square', encode(dx)), expr('square', encode(dy))));
        const cosine = expr('divide', encode(dx), length), sine = expr('divide', encode(dy), length);
        const sourceCuts = new Map<string, { t: Rat; numeric: number; sources: Source[] }>();
        const addCut = (numeric: number, source: Source) => {
            const t = fromBinary64(numeric), k = key(t);
            const entry = sourceCuts.get(k) ?? { t, numeric, sources: [] };
            entry.sources.push(source);
            sourceCuts.set(k, entry);
        };
        addCut(0, { kind: 'member-end', index: memberIndex, id: member.id, role: 'a' });
        addCut(1, { kind: 'member-end', index: memberIndex, id: member.id, role: 'b' });
        model.supports.forEach((support, index) => {
            if (support.member === member.id) addCut(support.t, { kind: 'support', index, id: support.id, role: 'location' });
        });
        model.loads.forEach((load, index) => {
            if (load.member !== member.id) return;
            addCut(load.t, { kind: load.kind, index, id: load.id, role: load.kind === 'distributed' ? 'start' : 'location' });
            if (load.kind === 'distributed') addCut(load.end, { kind: 'distributed', index, id: load.id, role: 'end' });
        });
        const ordered = [...sourceCuts.values()].sort((x, y) => compare(x.t, y.t));
        const cuts = ordered.map((cut, cutIndex) => ({ index: cutIndex, parameter: encode(cut.t),
            location: location(memberIndex, member, cutIndex, cut.t), sources: cut.sources,
            adjacentIntervals: [cutIndex > 0 ? cutIndex - 1 : null, cutIndex < ordered.length - 1 ? cutIndex : null],
            position: { x: expr('add', encode(xa), expr('multiply', encode(cut.t), encode(dx))),
                y: expr('add', encode(ya), expr('multiply', encode(cut.t), encode(dy))) } }));
        const cutIndex = (t: number) => ordered.findIndex(cut => compare(cut.t, fromBinary64(t)) === 0);
        const memberActions = model.loads.flatMap((load, index) => load.member === member.id && load.kind !== 'distributed' ? [{
            index, id: load.id, kind: load.kind, cutIndex: cutIndex(load.t), location: cuts[cutIndex(load.t)].location,
            components: encodeComponents(load), sourceFields: sourceFields(load),
        }] : []);
        const memberSupports = model.supports.flatMap((support, index) => support.member === member.id ? [{
            index, id: support.id, kind: support.kind, cutIndex: cutIndex(support.t), location: cuts[cutIndex(support.t)].location,
            axes: axes(support), rows: supportRows(support), custom: { fixX: !!support.fixX, fixY: !!support.fixY, fixRotation: !!support.fixRotation },
        }] : []);
        allActions.push(...memberActions); allSupports.push(...memberSupports);
        const intervals = ordered.slice(0, -1).map((left, index) => {
            const right = ordered[index + 1], u = left.t, v = right.t;
            const contributions = model.loads.flatMap((load, sourceIndex) => {
                if (load.member !== member.id || load.kind !== 'distributed') return [];
                const start = fromBinary64(load.t), end = fromBinary64(load.end);
                if (compare(u, start) < 0 || compare(v, end) > 0) return [];
                const q0 = loadValue(load, u), q1 = loadValue(load, v);
                return [{ sourceIndex, sourceId: load.id, sourceInterval: [encode(start), encode(end)],
                    sourceEndpoints: [encode(fromBinary64(load.fy)), encode(fromBinary64(load.qEnd))],
                    restrictedEndpoints: [encode(q0), encode(q1)], sourceFields: sourceFields(load) }];
            });
            let total0 = zero, total1 = zero;
            for (const contribution of contributions) {
                const q0 = contribution.restrictedEndpoints[0], q1 = contribution.restrictedEndpoints[1];
                total0 = add(total0, rat(BigInt(q0.numerator), BigInt(q0.denominator)));
                total1 = add(total1, rat(BigInt(q1.numerator), BigInt(q1.denominator)));
            }
            const resultant = resultantCoefficient(u, v, total0, total1);
            const firstMoment = firstMomentCoefficient(u, v, total0, total1);
            const globalMoment = add(mul(xa, resultant), mul(dx, firstMoment));
            return { index, memberIndex, memberId: member.id, leftCut: index, rightCut: index + 1,
                from: encode(u), to: encode(v), left: cuts[index].location, right: cuts[index + 1].location,
                length: expr('multiply', length, encode(sub(v, u))), EA: encode(fromBinary64(member.EA)), EI: encode(fromBinary64(member.EI)),
                cosine, sine, contributions, verticalEndpoints: [encode(total0), encode(total1)],
                localAxialEndpoints: [expr('multiply', sine, encode(total0)), expr('multiply', sine, encode(total1))],
                localTransverseEndpoints: [expr('multiply', cosine, encode(total0)), expr('multiply', cosine, encode(total1))],
                resultant: expr('multiply', length, encode(resultant)),
                firstMomentAboutOriginalStart: expr('multiply', expr('square', length), encode(firstMoment)),
                globalMomentAboutOrigin: expr('multiply', length, encode(globalMoment)) };
        });
        const engineCuts = ordered.map(cut => {
            const rounded = Number(cut.numeric.toFixed(8));
            const keyKind = rounded < 1e-8 ? 'a' : rounded > 1 - 1e-8 ? 'b' : 'interior';
            const originalEndMapping = cut.numeric < 1e-8 ? 'a' : cut.numeric > 1 - 1e-8 ? 'b' : 'interior';
            return { exact: encode(cut.t), sources: cut.sources, roundedBinary64: exactBinary64(rounded), keyKind, originalEndMapping,
                changed: compare(cut.t, fromBinary64(rounded)) !== 0,
                endpointSnap: keyKind !== 'interior' && compare(cut.t, keyKind === 'a' ? zero : one) !== 0 };
        });
        const groups = new Map<string, number[]>();
        engineCuts.forEach((cut, index) => {
            const group = cut.keyKind === 'interior' ? canonical(cut.roundedBinary64) : cut.keyKind;
            groups.set(group, [...(groups.get(group) ?? []), index]);
        });
        const merged = [...groups.values()].filter(indices => indices.length > 1);
        discrepancies.push({ memberIndex, memberId: member.id, policy: enginePolicy, cuts: engineCuts, mergedExactCuts: merged,
            zeroLengthOrCollapsedIntervals: intervals.filter(interval => {
                const l = engineCuts[interval.leftCut], r = engineCuts[interval.rightCut];
                return l.keyKind === r.keyKind && (l.keyKind !== 'interior' || canonical(l.roundedBinary64) === canonical(r.roundedBinary64));
            }).map(interval => interval.index),
            ownershipDifferences: engineCuts.flatMap((cut, index) => cut.keyKind !== cut.originalEndMapping ? [{ cutIndex: index, roundedLocation: cut.keyKind, originalLocation: cut.originalEndMapping }] : []),
            coverageDifferences: { collapsedIntervals: merged.length > 0, numericalCoverage: 'not-compared' },
            loadBoundaryDifferences: engineCuts.flatMap((cut, index) => cut.changed ? cut.sources.filter(source => source.kind === 'distributed').map(source => ({ cutIndex: index, sourceIndex: source.index, sourceId: source.id, role: source.role })) : []),
            numericalGeometry: 'not-compared', mappingCoefficientDeletion: 'not-compared',
            loadMembership: 'engine-midpoint-on-rounded-cuts-not-certified', numericalEquivalence: 'not-claimed' });
        members.push({ index: memberIndex, id: member.id, startNodeId: member.a, endNodeId: member.b,
            geometry: { origin: { x: encode(xa), y: encode(ya) }, dx: encode(dx), dy: encode(dy), length, cosine, sine,
                status: 'pending-exact-geometry' },
            endLaws: [endLaw(model, memberIndex, 'a'), endLaw(model, memberIndex, 'b')],
            interiorEncoding: { kind: 'symbolic-member-local', interiorCutCount: Math.max(0, cuts.length - 2), rectangularSlots: 'not-allocated' }, cuts, intervals,
            obligations: obligations(memberIndex, intervals, cuts, memberActions, memberSupports,
                { origin: { x: encode(xa), y: encode(ya) }, dx: encode(dx), dy: encode(dy), length, cosine, sine },
                [endLaw(model, memberIndex, 'a'), endLaw(model, memberIndex, 'b')],
                { EA: encode(fromBinary64(member.EA)), EI: encode(fromBinary64(member.EI)) }) });
    }
    // Source arrays retain the input order; member cut tables alone are sorted.
    allActions.sort((a, b) => (a as { index: number }).index - (b as { index: number }).index);
    allSupports.sort((a, b) => (a as { index: number }).index - (b as { index: number }).index);
    const artifact = { schema: 'cv2011-exact-member-cut-artifact', version: 1, implementationIdentity,
        numericSemantics, status: 'pending-not-formally-verified',
        bindings: { mechanical: snapshot.bindings.mechanical, display: snapshot.bindings.display, query: snapshot.bindings.query,
            rawSource: captured.bindings.rawSource, rawSourceStatus: captured.bindings.rawSource === null ? 'not-provided' : 'inherited-from-snapshot',
            exactAdapter: null, theoremBundle: null, checker: null, result: null },
        nodes: model.nodes.map((node, index) => ({ index, id: node.id, x: encode(fromBinary64(node.x)), y: encode(fromBinary64(node.y)),
            joint: node.joint ?? 'rigid', rotationStiffness: node.rotationStiffness === undefined ? null : encode(fromBinary64(node.rotationStiffness)),
            requestedReference: node.referenceMember ?? null })),
        members, actions: allActions, supports: allSupports, discrepancies,
        coverage: { preflight: 'untrusted-generated-witnesses', genericTheorems: 'see-pinned-proof-bundle',
            syntheticInstances: 'separate-ci-only', privateInstances: 'pending', geometry: 'pending', engineEquivalence: 'not-claimed' } };
    const artifactDigest = await sha256(canonical(artifact));
    return deepFreeze({ ...artifact, artifactDigest });
}

/** Recompute the entire artifact from its snapshot; this is an untrusted local
 * consistency check, not a kernel checker or a numerical solver certificate. */
export async function verifyExactCutArtifact(
    snapshot: Awaited<ReturnType<typeof createEvidenceEnvelope>>,
    candidate: Awaited<ReturnType<typeof adaptEvidenceSnapshot>>,
): Promise<void> {
    const expected = await adaptEvidenceSnapshot(snapshot);
    if (canonical(candidate) !== canonical(expected)) throw Error('Adapter artifact does not match the snapshot');
}
