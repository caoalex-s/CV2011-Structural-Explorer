import type { Drawing } from './ideal-truss.js';
import { packet as trussPacket } from './truss-check.js';
import { PortalRuntime, sha256 } from './portal-runtime.js';
export const members = ['BC', 'GC', 'GF'] as const;
export type Query = {
    cut: number;
    side: 'left' | 'right';
    centre: string;
};
export type Term = {
    name: string;
    x: number;
    y: number;
    moment: number;
    radicand: number;
    component: number;
};
export type CheckedSection = {
    terms: Term[];
    reactions: Record<string, number>;
    p: number;
};
export type Receipt = {
    source: Drawing;
    query: Query;
    inputDigest: string;
    report: string;
    reportDigest: string;
    artifact: string;
    elapsedMs: number;
};
export function sectionPacket(drawing: Drawing, query: Query) {
    const original = new TextDecoder().decode(trussPacket(drawing));
    return new TextEncoder().encode(['SECTION1', query.cut, query.side, query.centre, original].join('\n'));
}
export function crossed(drawing: Drawing, cut: number) {
    const jointX = (id: string) => drawing.joints.find(j => j.id === id)!.x;
    return drawing.bars.filter(([a, b]) => (jointX(a) - cut) * (jointX(b) - cut) < 0).map(pair => pair.join(''));
}
function integer(text: string): number {
    const n = Number(text);
    if (!Number.isSafeInteger(n) || String(n) !== text)
        throw Error('Unexpected integer in the checked report.');
    return n;
}
export function decodeSection(report: string, drawing: Drawing, query: Query): CheckedSection {
    const lines = report.split('\n');
    const p = -drawing.joints.find(j => j.id === 'A')!.fy;
    if (lines.shift() !== 'SECTION1' || lines.shift() !== [query.cut, query.side, query.centre, p].join(','))
        throw Error('The report describes a different section.');
    const names = [...members, ...(query.side === 'left' ? ['P'] : ['Dx', 'Dy', 'Ex'])];
    const terms = names.map(name => {
        const fields = lines.shift()?.split(',');
        if (fields?.length !== 6 || fields[0] !== name)
            throw Error('Incomplete section equation.');
        const [x, y, moment, radicand, component] = fields.slice(1).map(integer);
        if (radicand !== x * x + y * y || radicand < 1)
            throw Error('Invalid section direction.');
        return { name, x, y, moment, radicand, component };
    });
    const reactions: Record<string, number> = {};
    for (const name of ['Dx', 'Dy', 'Ex']) {
        const fields = lines.shift()?.split(',');
        if (fields?.length !== 2 || fields[0] !== name)
            throw Error('Incomplete reaction report.');
        reactions[name] = integer(fields[1]);
    }
    if (lines.join('\n') !== 'SUM,0,0,0' || !(['x', 'y', 'moment'] as const).every(axis => terms.reduce((s, t) => s + t[axis] * t.component, 0) === 0))
        throw Error('The substitutions do not balance.');
    return { terms, reactions, p };
}
let runtime: PortalRuntime | undefined;
let version = 0;
export function invalidateSection() { version++; runtime?.invalidate(); }
export async function checkedSection(drawing: Drawing, query: Query) {
    const current = ++version;
    const bytes = sectionPacket(drawing, query);
    if (!runtime || runtime.needsReset) {
        const prefix = location.pathname.includes('/portal-checker/') ? './' : './portal-checker/';
        runtime = new PortalRuntime(new URL(prefix + 'week04-section/worker.mjs', location.href));
    }
    await runtime.ready;
    if (current !== version)
        return;
    const result = await runtime.checkDiagram(bytes, true);
    if (current !== version)
        return;
    if (result.state !== 'accepted' || !(result.report instanceof Uint8Array))
        throw Error('The checker did not accept this drawing and cut.');
    const [inputDigest, reportDigest] = await Promise.all([sha256(bytes), sha256(result.report)]);
    if (current !== version)
        return;
    if (inputDigest !== result.inputDigest || reportDigest !== result.reportDigest)
        throw Error('The checked bytes do not match this request.');
    const report = new TextDecoder().decode(result.report);
    const answer = decodeSection(report, drawing, query);
    return { answer, receipt: { source: drawing, query, inputDigest, reportDigest, report, artifact: runtime.artifact, elapsedMs: 0 } satisfies Receipt };
}
