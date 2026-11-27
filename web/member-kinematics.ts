/** Display only the local displacement and slope enclosed by the checker. */
import { escapeHtml } from './ui.js';
import { math } from './math.js';

export function renderKinematics(bytes: Uint8Array, member: string, label: string): HTMLElement {
    const lines = new TextDecoder('utf-8', { fatal: true }).decode(bytes).split('\n');
    const expectedId = member.split('').map(c => c.charCodeAt(0).toString(16).padStart(4, '0')).join('');
    if (bytes.length > 262144 || lines.shift() !== 'CV2011_MEMBER_KINEMATICS_1' || lines.shift() !== expectedId)
        throw Error('The kinematics report does not match the selected member.');

    const section = document.createElement('section');
    section.dataset.memberKinematics = member;
    function append(tag: string, html: string) {
        const element = document.createElement(tag);
        element.innerHTML = html;
        section.append(element);
    }
    function table(headings: string[]) {
        const element = document.createElement('table');
        const header = element.createTHead().insertRow();
        for (const heading of headings) {
            const th = document.createElement('th');
            th.innerHTML = heading;
            header.append(th);
        }
        section.append(element);
        return element.createTBody();
    }
    function row(body: HTMLTableSectionElement, values: string[]) {
        const tr = body.insertRow();
        for (const value of values) tr.insertCell().innerHTML = value;
    }
    // Round the two ends outward using integers, including negative values.
    function decimal(token: string, upper: boolean) {
        if (!/^-?\d{1,128}\/[1-9]\d{0,127}$/.test(token)) throw Error('Invalid rational endpoint.');
        const [n,d] = token.split('/').map(BigInt);
        const scaled = n * 1000000000n;
        const remainder = scaled % d;
        const value = scaled / d + (upper && remainder > 0n ? 1n : !upper && remainder < 0n ? -1n : 0n);
        const digits = (value < 0n ? -value : value).toString().padStart(10, '0');
        return (value < 0n ? '−' : '') + digits.slice(0, -9) + ('.' + digits.slice(-9)).replace(/0+$/, '').replace(/\.$/, '');
    }
    function range(tokens: string[], start: number) {
        const lo = decimal(tokens[start], false), hi = decimal(tokens[start+1], true);
        return lo === hi ? lo : '[' + lo + ', ' + hi + ']';
    }

    // Merge overlapping enclosures on the same face before rounding for display.
    // A cut can have two different rotations, even at a common physical station.
    function locationText(stations: string[][]) {
        function compare(a: string, b: string) {
            const [an, ad] = a.split('/').map(BigInt), [bn, bd] = b.split('/').map(BigInt);
            const delta = an * bd - bn * ad;
            return delta < 0n ? -1 : delta > 0n ? 1 : 0;
        }
        const intervals = stations.map(entry => ({ piece: Number(entry[2]), lo: entry[5], hi: entry[6] }));
        intervals.sort((a, b) => a.piece - b.piece || compare(a.lo, b.lo));
        const merged: typeof intervals = [];
        for (const interval of intervals) {
            const last = merged.at(-1);
            if (last?.piece === interval.piece && compare(interval.lo, last.hi) <= 0) {
                if (compare(last.hi, interval.hi) < 0) last.hi = interval.hi;
            } else merged.push(interval);
        }
        return merged.map(({ piece, lo, hi }) => 'Piece ' + (piece + 1) + ' · ' + range([lo, hi], 0)).join('; ');
    }

    const slope = math('\\theta'), displacement = math('v');
    append('h3', 'Slope and transverse displacement of ' + escapeHtml(label));
    append('p', `Distance ${math('x')} follows the drawn member. Local transverse displacement ${displacement} is positive to the left when looking from its start towards its end. For a rightward horizontal member, positive ${displacement} is upward. On an incline, global vertical movement also depends on axial displacement. Physical slope ${math(String.raw`\theta=\mathrm{d}v/\mathrm{d}x`)} is positive counterclockwise. On each prismatic piece, ${math(String.raw`EI\,\mathrm{d}\theta/\mathrm{d}x=M`)}. Integrating the moment from the start face gives the slope, and integrating the slope gives ${displacement}. The calculation assumes small rotations and constant ${math('EI')}.`);
    const records = lines.map(line => line.split(' '));
    const ends = table(['Piece', 'Member fraction', `${slope} at start (rad)`, `${slope} at end (rad)`, `${displacement} at start (m)`, `${displacement} at end (m)`]);
    for (const tokens of records.filter(r => r[0] === 'P')) {
        if (tokens.length !== 12) throw Error('Incomplete piece-end values.');
        row(ends, [String(Number(tokens[1])+1), decimal(tokens[2], false) + ' to ' + decimal(tokens[3], true),
            range(tokens,4), range(tokens,6), range(tokens,8), range(tokens,10)]);
    }
    append('h4', 'Whole-member extrema');
    append('p', 'Each value is enclosed over the full member. The distance intervals cover every location attaining that extreme. A distance interval may also contain nearby stations.');
    const extrema = table(['Quantity', 'Extreme', 'Value', 'Distance from drawn start (m)']);
    for (const [code, title] of [['S', `Physical slope ${slope} (rad)`], ['D', `Local displacement ${displacement} (m)`]]) {
        const values = records.find(r => r[0] === code && r[1] === 'bounds');
        if (values?.length !== 6) throw Error('Missing whole-member bounds.');
        for (const [index, kind] of ['Minimum','Maximum'].entries()) {
            const stations = records.filter(r => r[0] === code && r[1] === 'location' && r[3+index] === '1');
            if (!stations.length) throw Error('Missing extremum locations.');

            row(extrema,[title,kind,range(values,2+2*index),locationText(stations)]);
        }
    }
    return section;
}
