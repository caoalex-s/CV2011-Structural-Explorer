/** Decode named values from the exact packet returned by the compiled ABI.
 * Call only after that same byte array receives code 1. Parsing supplies no
 * mathematical acceptance; it preserves the checked identities for display.
 */
import type { Rational } from './portal-candidate.js';
import { frameLimits, frameQueryConvention } from './frame-candidate.js';


export interface CheckedFramePoint {
    owner: 'node' | 'member'; id: string; index: number;
    parameter: Rational; x: Rational; y: Rational;
    motion: Rational[]; reaction?: Rational[];
}
export interface CheckedFrameValues {
    faces: { node: string; member: string; end: 'a' | 'b'; released: boolean;
        rotation: Rational; moment?: Rational; reaction?: Rational }[];
    kind: 'solution' | 'mechanism'; points: CheckedFramePoint[];
    query: { member: string; parameter: Rational; cutSide: 'left' | 'right';
        quantity: string; units: string; signConvention: string };
    readouts: Rational[]; loadWork: Rational;
}

export function decodeAcceptedHingePacket(bytes: Uint8Array): CheckedFrameValues {
    if (bytes.length > frameLimits.bytes) throw Error('Checker packet exceeds the display limit.');
    const text = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    if (!/^[\x20-\x7e\n]*$/.test(text)) throw Error('Invalid checker packet characters.');
    const fields = text.split('\n');
    if (fields.length > 6000) throw Error('Too many checker packet fields.');
    let position = 0;
    const token = (): string => {
        if (position >= fields.length) throw Error('Truncated checker packet.');
        return fields[position++];
    };
    const natural = (maximum: number): number => {
        const value = token();
        if (!/^(0|[1-9]\d{0,2})$/.test(value) || Number(value) > maximum) throw Error('Invalid checker count or index.');
        return Number(value);
    };
    const rational = (): Rational => {
        const numerator = token(), denominator = token();
        if (!/^-?(0|[1-9]\d{0,127})$/.test(numerator) || numerator === '-0' ||
            !/^[1-9]\d{0,127}$/.test(denominator)) throw Error('Invalid checker rational.');
        return { numerator, denominator };
    };
    const identifier = (): string => {
        const hex = token();
        if (!/^(?:[0-9a-f]{4}){1,256}$/.test(hex)) throw Error('Invalid checker identifier.');
        let value = '';
        for (let i = 0; i < hex.length; i += 4) value += String.fromCharCode(Number.parseInt(hex.slice(i, i + 4), 16));
        return value;
    };
    const vector = (count: number): Rational[] => Array.from({ length: count }, rational);
    if (token() !== 'CV2011_HINGE_1') throw Error('Unsupported checker packet version.');
    const nodeCount = natural(frameLimits.nodes), memberCount = natural(frameLimits.members);
    const supportCount = natural(frameLimits.supports), loadCount = natural(frameLimits.loads);
    if (!nodeCount || !memberCount) throw Error('Empty checker model.');

    // Read the accepted source identity tables. No candidate-side map labels
    // a checked value, and no rounded drawing coordinates enter this decoder.
    const nodeIds: string[] = [], memberIds: string[] = [];
    const joints: number[] = [], references: number[] = [];
    const endpoints: number[] = [], endRules: number[] = [];
    for (let i = 0; i < nodeCount; i++) {
        nodeIds.push(identifier()); rational(); rational();
        joints.push(natural(2)); references.push(natural(memberCount) - 1); rational();
    }
    for (let i = 0; i < memberCount; i++) {
        memberIds.push(identifier()); endpoints.push(natural(nodeCount - 1), natural(nodeCount - 1));
        rational(); rational();
        endRules.push(natural(2), natural(2));
    }
    for (let i = 0; i < supportCount; i++) {
        identifier(); natural(memberCount - 1); rational(); natural(2); rational();
    }
    for (let i = 0; i < loadCount; i++) {
        identifier(); natural(memberCount - 1); natural(2);
        for (let field = 0; field < 6; field++) rational();
    }
    const member = memberIds[natural(memberCount - 1)], parameter = rational();
    const cutSide = natural(1) ? 'right' : 'left';
    if (natural(1) !== 1) throw Error('Unknown query convention.');
    const mechanism = natural(1) === 1;
    const motionCount = natural(frameLimits.coordinates), freeCount = natural(frameLimits.coordinates);
    const pointCount = natural(frameLimits.points);
    const releaseSides = endRules.flatMap((rule, side) => {
        const node = endpoints[side];
        const reference = references[node] >= 0 ? references[node] : Math.floor(endpoints.indexOf(node) / 2);
        return Math.floor(side / 2) !== reference && (rule === 2 || rule === 0 && joints[node] === 1) ? [side] : [];
    });
    if (motionCount !== 3 * pointCount + releaseSides.length || (mechanism && freeCount !== 0)) throw Error('Invalid checked dimensions.');
    const points: CheckedFramePoint[] = [];
    for (let i = 0; i < pointCount; i++) {
        const owned = natural(1) === 1;
        const index = natural((owned ? memberCount : nodeCount) - 1);
        points.push({ owner: owned ? 'member' : 'node', id: (owned ? memberIds : nodeIds)[index], index,
            parameter: rational(), x: rational(), y: rational(), motion: [] });
    }
    const motion = vector(motionCount);
    let reactions: Rational[] = [], readouts: Rational[] = [];
    if (!mechanism) {
        reactions = vector(motionCount);
        // The positive-factor witness is retained in the packet export. The
        // display consumes its values without allocating a second matrix.
        for (let i = 0; i < freeCount * freeCount + freeCount; i++) rational();
        readouts = vector(6);
    }
    const loadWork = rational();
    const moments = !mechanism ? vector(2 * memberCount) : [];
    if (position !== fields.length) throw Error('Unexpected trailing checker fields.');
    points.forEach((point, i) => {
        point.motion = motion.slice(3 * i, 3 * i + 3);
        if (!mechanism) point.reaction = reactions.slice(3 * i, 3 * i + 3);
    });
    const faces = endpoints.flatMap((node, side) => {
        if (!releaseSides.some(released => endpoints[released] === node)) return [];
        const slot = releaseSides.indexOf(side);
        const point = points.findIndex(item => item.owner === 'node' && item.index === node);
        if (point < 0) throw Error('Missing release point.');
        const coordinate = slot < 0 ? 3 * point + 2 : 3 * pointCount + slot;
        return [{ node: nodeIds[node], member: memberIds[Math.floor(side / 2)],
            end: (side % 2 ? 'b' : 'a') as 'a' | 'b', released: slot >= 0,
            rotation: motion[coordinate], moment: moments[side], reaction: slot >= 0 ? reactions[coordinate] : undefined }];
    });
    return { kind: mechanism ? 'mechanism' : 'solution', points, readouts, loadWork, faces,
        query: { member, parameter, cutSide, ...frameQueryConvention } };
}
