/** Dedicated checked portal panel, sharing the ordinary workspace and edit lifecycle. */
import { EvidenceRequests, createEvidenceEnvelope } from './model-evidence.js';
import { portalAmplitude, portalCandidate, encodeCandidate, portalQuery, outputIds, roundedDecimal, profileId } from './portal-candidate.js';
import type { Model } from './engine.js';
import { endConnection, nodeLabels, referenceMember } from './engine.js';
import { memberLabel } from './model-view.js';
import { decodeAcceptedHingePacket } from './frame-hinge-result.js';
import { decodeInclinedReleaseReport } from './frame-inclined-release-result.js';
import { renderInclinedMemberDiagram, renderMemberDiagram } from './member-diagram.js';
import { springExplanation } from './frame-spring-worked.js';
import { PortalRuntime } from './portal-runtime.js';
import { sha256 } from './portal-runtime.js';
import type { CheckerResult } from './portal-runtime.js';
import { validateFrame, frameQueryConvention } from './frame-candidate.js';
import { decodeAcceptedFramePacket } from './frame-result.js';
import { frameDescriptions, frameStatus } from './frame-display.js';
import type { EvidenceQuery } from './model-evidence.js';
import { createFrameWorked } from './frame-worked.js';
import { renderFrameWorked } from './frame-worked-view.js';
import { decodeAcceptedIntervalReport } from './frame-interval-result.js';
import { bindIntervalDisplay, renderIntervalValues } from './frame-interval-display.js';
import { validateIntervalFrame } from './frame-interval-model.js';
import { inclinedDeadlineMilliseconds } from './portal-runtime.js';
import { createIntervalExplanation, renderIntervalExplanation } from './frame-interval-worked.js';

import { renderKinematics } from './member-kinematics.js';

export const isPortalWorkspace = location.pathname.replace(/index\.html$/, '').endsWith('/portal-checker/');
// The same controller serves the main workspace and the compatible scoped URL.
export const isCheckedWorkspace = location.pathname.replace(/index\.html$/, '') === new URL('./', import.meta.url).pathname;
export const portalStorageKey = 'cv2011-checked-portal-model/v1';
const scope = new URL('./', location.href);
const isolationScript = new URL(isPortalWorkspace ? 'isolation-sw.js' : 'main-checker-sw.js', scope).href;
const runtimeUrl = new URL(isPortalWorkspace ? './bundle/worker.mjs' : './portal-checker/bundle/worker.mjs', scope);
const hingeUrl = new URL('../hinge/worker.mjs', runtimeUrl);
const inclinedReleaseUrl = new URL('../inclined-release/worker.mjs', runtimeUrl);
const springUrl = new URL('../spring/worker.mjs', runtimeUrl);
function usesSpring(model: Model): boolean {
    return model.members.some(member => (['a', 'b'] as const).some(end => typeof endConnection(model, member, end).rotation === 'number'));
}
function needsInclinedGeometry(model: Model): boolean {
    return model.supports.some(s => s.kind === 'roller' && ![0,90,180,270].includes(s.angle)) ||
        model.members.some(member => {
            const a = model.nodes.find(n => n.id === member.a)!, b = model.nodes.find(n => n.id === member.b)!;
            return a.x !== b.x && a.y !== b.y;
        });
}
function usesRelease(model: Model): boolean {
    return model.members.some(member => (['a', 'b'] as const).some(end => endConnection(model, member, end).rotation === 'free'));
}
function ownsRegistration(registration: ServiceWorkerRegistration): boolean {
    return registration.scope === scope.href &&
        [registration.active, registration.waiting, registration.installing].filter(worker => worker !== null)
            .every(worker => worker!.scriptURL === isolationScript) &&
        Boolean(registration.active || registration.waiting || registration.installing);
}

export function createPortalPanel(modelAtPresent: () => Model, changeUniformLoad: (value: number) => void,
    changeSectionParameter: (value: number) => void, storageKey = portalStorageKey, prepareReload: () => void = () => {},
    onDiagram?: (source:Model, member:string, rows:HTMLElement)=>void) {
    if (!isCheckedWorkspace) return { update(_member: string, _parameter: number) {} };
    const host = document.createElement('section');
    host.className = 'portal-certificate';
    host.innerHTML = `<h2>Worked solution</h2>
      <p id="portal-introduction">Generate a solution for the current drawing and selected section. Local checking supports rigid frames with horizontal and vertical members.</p>
      <button id="frame-generate">Generate worked solution</button>
      <button id="frame-collapse" hidden aria-expanded="true">Collapse solution</button>
      <label hidden>Uniform load (kN/m) <input id="portal-amplitude" type="number" step="any" value="-5"></label>
      <button id="portal-activate">Enable local checking</button><button id="portal-reset" hidden>Reset checker</button>
      <button id="portal-deactivate" hidden>Disable local checking</button>
      <label id="frame-side-label">Section limit <select id="frame-side"><option value="right">Right</option><option value="left">Left</option></select></label>
      <label id="frame-parameter-label">Member parameter t <input id="frame-parameter" type="number" min="0" max="1" step="any" value="0.5"></label>
      <p id="portal-status" role="status">Local checking is off. Generate enables checking and reloads this workspace once.</p>
      <div id="frame-worked-output"></div>
      <details><summary>Verification, scope, and exact certificate</summary><div id="portal-readouts"></div>
      <button id="frame-export" hidden>Export exact certificate</button>
      <p id="portal-scope">The main canvas draws numerical curves. Acceptance uses a compiled Lean checker and relies on its compiler, runtime, decoder, and input binding. Each edit does not invoke the Lean kernel.</p><pre id="portal-certificate"></pre></details>`;
    document.getElementById('worked-panel')!.replaceChildren(host);
    const overviewNote = document.createElement('p');
    overviewNote.id = 'frame-overview-convention';
    overviewNote.className = 'small frame-overview-note';
    overviewNote.textContent = 'Numerical overview: interpolated values use the right-hand convention at interior jumps and the inward limit at member ends. The checked worked solution uses the section limit selected below.';
    document.getElementById('section-results')!.before(overviewNote);
    const status = host.querySelector<HTMLElement>('#portal-status')!;
    const readouts = host.querySelector<HTMLElement>('#portal-readouts')!;
    const certificate = host.querySelector<HTMLElement>('#portal-certificate')!;
    const amplitude = host.querySelector<HTMLInputElement>('#portal-amplitude')!;
    const activate = host.querySelector<HTMLButtonElement>('#portal-activate')!;
    const deactivate = host.querySelector<HTMLButtonElement>('#portal-deactivate')!;
    const reset = host.querySelector<HTMLButtonElement>('#portal-reset')!;
    const cutSide = host.querySelector<HTMLSelectElement>('#frame-side')!;
    const sectionParameter = host.querySelector<HTMLInputElement>('#frame-parameter')!;
    const exportButton = host.querySelector<HTMLButtonElement>('#frame-export')!;
    const generate = host.querySelector<HTMLButtonElement>('#frame-generate')!;
    const collapse = host.querySelector<HTMLButtonElement>('#frame-collapse')!;
    const workedOutput = host.querySelector<HTMLElement>('#frame-worked-output')!;
    const requests = new EvidenceRequests();
    let runtime: PortalRuntime | null = null;
    let debounce: ReturnType<typeof setTimeout> | undefined;
    let member = 'BC', parameter = 0.5;
    let enabled = false;
    let startingNow = false;
    let exportText = '';
    let acceptedGeneration: (() => void) | null = null;
    const generationStorage = storageKey + '/generate';
    let pendingGeneration = sessionStorage.getItem(generationStorage);
    sessionStorage.removeItem(generationStorage);
    const sideStorage = storageKey + '/cut-side';
    // At a member endpoint only its inward face can be selected, even while
    // a newly selected checker is still starting and the selector is updating.
    const generationKey = () => JSON.stringify({ model: modelAtPresent(), member, parameter,
        side: parameter === 0 ? 'right' : parameter === 1 ? 'left' : cutSide.value });
    try {
        const saved = JSON.parse(sessionStorage.getItem(sideStorage) || 'null');
        if (saved?.model === JSON.stringify(modelAtPresent()) && ['left', 'right'].includes(saved.side)) cutSide.value = saved.side;
    } catch { /* A fresh query is checked even when view restoration fails. */ }
    window.addEventListener('beforeunload', () => sessionStorage.setItem(sideStorage,
        JSON.stringify({ model: JSON.stringify(modelAtPresent()), side: cutSide.value })));

    let diagramRuntime: PortalRuntime | null = null;
    let kinematicsRuntime: PortalRuntime | null = null;
    let cancelProposal: (() => void) | undefined;
    function intervalProposal(model: Model, query: EvidenceQuery): Promise<Uint8Array<ArrayBuffer>> {
        cancelProposal?.();
        return new Promise((resolve, reject) => {
            const worker = new Worker(new URL('./member-kinematics-proposal.js', import.meta.url), { type: 'module' });
            const cancel = () => { finish(); reject(Error('The drawing or request changed.')); };
            function finish() {
                window.clearTimeout(timer);
                worker.terminate();
                if (cancelProposal === cancel) cancelProposal = undefined;
            }
            const timer = window.setTimeout(() => { finish(); reject(Error('Proposal time limit reached.')); }, 30000);
            cancelProposal = cancel;
            worker.onerror = () => { finish(); reject(Error('Could not prepare the source packet.')); };
            worker.onmessage = ({ data }) => {
                finish();
                if (data instanceof Uint8Array && data.buffer instanceof ArrayBuffer) resolve(new Uint8Array(data.buffer, data.byteOffset, data.byteLength));
                else reject(Error(String(data)));
            };
            worker.postMessage({ model, query, released: usesRelease(model) });
        });
    }
    function clear(message: string) {
        cancelProposal?.();
        diagramRuntime?.dispose(); diagramRuntime = null;
        kinematicsRuntime?.dispose(); kinematicsRuntime = null;
        status.textContent = message; readouts.replaceChildren(); certificate.textContent = '';
        exportText = ''; exportButton.hidden = true;
        acceptedGeneration = null; workedOutput.replaceChildren(); collapse.hidden = true;
        workedOutput.hidden = false;
    }
    function stop() { clearTimeout(debounce); requests.invalidate(); runtime?.dispose(); runtime = null; enabled = false; }
    async function start() {
        stop(); clear('Starting local checker…');
        startingNow = true;
        try {
            const drawing = modelAtPresent();
            runtime = new PortalRuntime(usesSpring(drawing) ? springUrl : usesRelease(drawing) ? (needsInclinedGeometry(drawing) ? inclinedReleaseUrl : hingeUrl) : runtimeUrl);
        }
        catch (error) { startingNow = false; reset.hidden = false; clear(`Checking unavailable: ${String(error)}`); return; }
        const starting = runtime;
        starting.onFailure = reason => {
            if (starting !== runtime) return;
            requests.invalidate(); enabled = false; startingNow = false; reset.hidden = false; clear(reason);
        };
        try {
            await starting.ready;
            if (starting !== runtime) return;
            if (!starting.supportsAffineFrames && !starting.supportsHingeFrames) throw Error('The loaded checker does not support this frame.');
            enabled = true; startingNow = false; activate.hidden = true; deactivate.hidden = false; reset.hidden = false;
            if (starting.supportsFrames) {
                amplitude.closest('label')!.hidden = true;
                host.querySelector<HTMLElement>('#frame-side-label')!.hidden = false;
                host.querySelector<HTMLElement>('#frame-parameter-label')!.hidden = false;
                host.querySelector('#portal-scope')!.textContent = 'The checker covers linear Euler–Bernoulli frames with positive EA and EI, fixed or pin supports, and rollers at 0, 90, 180, or 270 degrees. Point forces, couples, and linearly varying vertical loads may act over partial or overlapping member intervals. Distributed loads may change sign. Drawing labels are downward positive; the stored global-y forces are upward positive. Up to 8 members, 16 nodes, 16 active points, 16 segments, 16 supports, and 16 loads are supported within the arithmetic and one-second limits. Inputs retain their exact parsed binary64 values. Source and certificate rationals allow 128 digits, with 256 digits for normalized candidate intermediates and 513 before reduction. The packet limit is 1 MiB. A limit or timeout is inconclusive. N is positive in tension, M is positive in sagging, dM/dx = V, global y is upward, and rotation is counterclockwise. The main canvas draws numerical curves. In the whole-member worked solution, the sketch uses the checked polynomial coefficients. The tables give the checked section values and extrema. Acceptance relies on the proved compiled checker, its compiler and runtime, and the decoder and input binding. Edits are checked locally without invoking the Lean kernel.';
                if (starting.supportsInclinedFrames) {
                    host.querySelector('#portal-introduction')!.textContent = 'Generate a solution for the current rigid frame and selected section. For inclined members and rollers at arbitrary finite angles, the worked solution gives checked intervals for the selected section and whole-member shear and moment extrema.';
                    host.querySelector('#portal-scope')!.textContent = `The checker covers linear Euler–Bernoulli frames with positive EA and EI and rigid joints. Supports may be fixed, pinned, or rollers at arbitrary finite degree angles. Point forces, couples, and linearly varying vertical loads may act over partial or overlapping member intervals. Original parsed binary64 coordinates, angles, and actions define the real model. Up to 8 members, 16 nodes, 16 active points, 16 segments, 16 supports, and 16 loads are admitted within the arithmetic budget and 1 MiB packet limit. The exact-cardinal route has a one-second deadline. Inclined requests have a ${inclinedDeadlineMilliseconds / 1000}-second deadline and are cancelled when the drawing or selected section changes. A timeout or failed enclosure check is inconclusive and does not establish a mechanism. N is positive in tension, M is positive in sagging with dM/dx = V, global y is upward, and rotation is counterclockwise. The main canvas draws numerical curves. Acceptance relies on the proved compiled checker, its compiler and runtime, and the decoder and input binding.`;
                }
            }
            if (starting.supportsHingeFrames) {
                host.querySelector('#portal-introduction')!.textContent = 'Generate the worked solution to see the selected member’s shear and moment diagrams and the rotations at its hinges.';
                host.querySelector('#portal-scope')!.textContent = 'This checker supports rotational releases on horizontal and vertical members with shared joint translations and cardinal roller restraints. For a stable frame, the worked solution uses each member’s own end rotations to recover its fields. The compiled checker also checks admissible mechanism motions.';
            }
            if (starting.supportsInclinedReleases) {
                host.querySelector('#portal-introduction')!.textContent = 'Generate the worked solution to inspect shear and moment along the selected member and the end rotations and moments at released joints.';
                host.querySelector('#portal-scope')!.textContent = 'Inclined members and roller directions use interval arithmetic. A release preserves the joint translations and gives the member end its own rotation. An inconclusive calculation leaves stability undetermined.';
            }
            if (starting.supportsSprings) {
                host.querySelector('#portal-introduction')!.textContent = 'Generate the shear and moment diagrams for the selected member and inspect the rotations and transmitted couple at each spring.';
                host.querySelector('#portal-scope')!.textContent = 'The checker uses the rotational stiffness specified at each connected end. Translations are shared at the joint. The whole-member check uses the specified spring stiffness and the solved equilibrium. On inclined members the table encloses physical locations and ordinates. A failed interval check leaves stability undetermined.';
            }
            update(member, parameter);
        } catch (error) { if (starting === runtime) { stop(); startingNow = false; reset.hidden = false; clear(`Checking unavailable: ${String(error)}`); } }
    }
    async function displayFrame(result: CheckerResult, envelope: Awaited<ReturnType<typeof createEvidenceEnvelope>>,
        token: { revision: number; request: number }, checker: PortalRuntime, sourceBytes: Uint8Array) {
        if (result.state !== 'accepted') {
            const detail = typeof result.message === 'string' ? ` ${result.message}` : '';
            clear(`Check ${result.state}.${detail}`); return;
        }
        if (!(result.packet instanceof Uint8Array) || typeof result.packetDigest !== 'string') throw Error('Missing accepted packet.');
        const packet = new Uint8Array(result.packet);
        const packetDigest = result.packetDigest;
        // Capture both byte containers before the first digest await. Worker
        // object fields are not the source of displayed mathematical values.
        const report = (result.frameProtocol === 'inclined' || result.frameProtocol === 'inclined-release' || result.frameProtocol === 'spring') && result.report instanceof Uint8Array
            ? new Uint8Array(result.report) : null;
        const reportDigest = result.reportDigest;
        if (await sha256(packet) !== packetDigest) throw Error('Accepted packet identity changed.');
        if (!requests.isCurrent(token) || checker !== runtime) return;
        function drawDiagram(source: Model, member: string, receipt: object, route: 'diagram' | 'joint-diagram' | 'inclined-diagram') {
            diagramRuntime?.dispose();
            const extra = new PortalRuntime(new URL('../' + route + '/worker.mjs', runtimeUrl));
            diagramRuntime = extra;
            const progress = document.createElement('p');
            progress.textContent = 'Checking the whole-member diagrams…';
            workedOutput.append(progress);
            const current = () => requests.isCurrent(token) && checker === runtime && diagramRuntime === extra;
            let combined = { ...receipt };
            function record(part: object) {
                combined = { ...combined, ...part };
                exportText = JSON.stringify(combined, null, 2);
                certificate.textContent = exportText;
            }
            cancelProposal?.();
            kinematicsRuntime?.dispose();
            const kinematics = new PortalRuntime(new URL('../member-kinematics/worker.mjs', runtimeUrl));
            kinematicsRuntime = kinematics;
            const kinematicsProgress = document.createElement('p');
            kinematicsProgress.textContent = 'Checking member slope and transverse displacement…';
            workedOutput.append(kinematicsProgress);
            const active = () => current() && kinematicsRuntime === kinematics;
            void (async () => {
                try {
                    await kinematics.ready;
                    if (!active()) return;
                    const captured = JSON.parse(new TextDecoder().decode(sourceBytes));
                    let witness = packet;
                    if (result.frameProtocol !== 'inclined' && result.frameProtocol !== 'inclined-release' && result.frameProtocol !== 'spring') {
                        witness = await intervalProposal(captured.model, captured.query);
                    }
                    const digest = await sha256(witness);
                    if (!active()) return;
                    const checked = await kinematics.checkDiagram(witness);
                    if (!active()) return;
                    if (checked.state !== 'accepted' || checked.inputDigest !== digest || checked.frameProtocol !== 'diagram'
                        || !(checked.report instanceof Uint8Array) || await sha256(checked.report) !== checked.reportDigest)
                        throw Error('The source or extrema could not be enclosed.');
                    const sourceDigest = await sha256(sourceBytes);
                    if (!active()) return;
                    const selected = source.members.find(m => m.id === member)!;
                    kinematicsProgress.replaceWith(renderKinematics(checked.report, member, memberLabel(source, selected)));
                    record({ kinematics: { protocol: 'CV2011_MEMBER_KINEMATICS_1', sourceDigest, basePacketDigest: packetDigest,
                        packetDigest: digest, packet: new TextDecoder().decode(witness), artifact: kinematics.artifact,
                        bundle: kinematics.bundle, reportDigest: checked.reportDigest, report: new TextDecoder().decode(checked.report) } });
                } catch (error) {
                    if (active()) kinematicsProgress.textContent = 'Slope and displacement check inconclusive. ' + String(error);
                } finally { kinematics.dispose(); }
            })();
            void (async () => {
                try {
                    await extra.ready;
                    if (!current()) return;
                    const checked = await extra.checkDiagram(packet);
                    if (!current()) return;
                    if (checked.state !== 'accepted' || checked.frameProtocol !== 'diagram' || checked.inputDigest !== packetDigest ||
                        !(checked.report instanceof Uint8Array) || await sha256(checked.report) !== checked.reportDigest)
                        throw Error('Whole-member bounds could not be certified.');
                    if (!current()) return;
                    const selected = source.members.find(m => m.id === member)!;
                    const start = source.nodes.find(n => n.id === selected.a)!;
                    const end = source.nodes.find(n => n.id === selected.b)!;
                    const label = memberLabel(source, selected);
                    const diagram = route === 'inclined-diagram'
                        ? renderInclinedMemberDiagram(checked.report, selected.id, label, end.x - start.x, end.y - start.y)
                        : renderMemberDiagram(checked.report, selected.id, label, Math.sign(end.x - start.x));
                    progress.replaceWith(diagram);
                    onDiagram?.(source,member,diagram);
                    record({ diagram: { protocol: route === 'inclined-diagram' ? 'CV2011_INCLINED_DIAGRAM_1' : 'CV2011_DIAGRAM_1',
                        artifact: extra.artifact, bundle: extra.bundle, packetDigest, reportDigest: checked.reportDigest,
                        report: new TextDecoder().decode(checked.report) } });
                } catch (error) {
                    if (current()) progress.textContent = 'Whole-member check inconclusive. ' + String(error);
                } finally { extra.dispose(); }
            })();
        }
        if (checker.supportsInclinedReleases) {
            if (result.frameProtocol !== (checker.supportsSprings ? 'spring' : 'inclined-release') || !report || typeof reportDigest !== 'string' || await sha256(report) !== reportDigest)
                throw Error('Missing or changed inclined release report.');
            if (!requests.isCurrent(token) || checker !== runtime) return;
            const source = JSON.parse(new TextDecoder().decode(sourceBytes));
            const drawing: Model = source.model;
            const values = decodeInclinedReleaseReport(report, checker.supportsSprings);
            bindIntervalDisplay({ ...drawing, nodes: drawing.nodes.map(n => ({ ...n, joint: 'rigid' })),
                members: drawing.members.map(({connectionA, connectionB, ...m}) => m) }, source.query, values);
            const labels = nodeLabels(drawing);
            const selected = drawing.members.find(m => m.id === values.query.member)!;
            const first = drawing.nodes.find(node => node.id === selected.a)!;
            const last = drawing.nodes.find(node => node.id === selected.b)!;
            const dx = last.x - first.x, dy = last.y - first.y;
            const length = Math.hypot(dx, dy);
            const direction = `Local x runs from ${labels.get(first.id)} to ${labels.get(last.id)}. The member spans ΔX = ${dx} m and ΔY = ${dy} m. Its direction cosines are c ≈ ${(dx/length).toFixed(6)} and s ≈ ${(dy/length).toFixed(6)}. A global force (Fx, Fy) has local components cFx + sFy along the member and −sFx + cFy transverse to it.`;
            const faceLines = values.faces.map(face => {
                const m = drawing.members.find(m => m.id === face.member);
                const end = face.end === 0 ? 'a' : 'b';
                if (!m || m[end] !== face.node || (endConnection(drawing, m, end).rotation !== 'rigid') !== face.released)
                    throw Error('Member end differs from the captured drawing.');
                const role = typeof endConnection(drawing, m, end).rotation === 'number' ? 'spring-connected end rotation' : face.released ? 'independent released-end rotation' :
                    referenceMember(drawing, face.node) === m.id ? 'reference rotation at the joint' : 'shares the reference rotation';
                const couples = drawing.loads.filter(load => load.kind === 'moment' && load.member === m.id && load.t === face.end);
                const actions = couples.length ? `Applied ${couples.length === 1 ? 'couple' : 'couples'} on this end as drawn, ${couples.map(load => `${load.mz} kN m`).join(', ')} (counterclockwise positive).` : 'No couple is applied to this end.';
                return `Node ${labels.get(face.node)}, member ${memberLabel(drawing, m)} (${role}). Shared displacement ux ≈ ${roundedDecimal(face.ux.midpoint, 6)} m, uy ≈ ${roundedDecimal(face.uy.midpoint, 6)} m. Rotation ≈ ${roundedDecimal(face.rotation.midpoint, 6)} rad. ${actions} Section moment ≈ ${roundedDecimal(face.moment.midpoint, 6)} kN m.`;
            });
            const presentation = renderIntervalValues(values, drawing);
            const render = (element: HTMLElement) => {
                element.innerHTML = presentation;
                const title = document.createElement('h3'); title.textContent = checker.supportsSprings ? 'Member ends at rotational springs' : 'Member ends at released joints';
                for (const line of springExplanation(drawing, values)) element.append(line);
                element.prepend(title, ...faceLines.map(text => { const line = document.createElement('p'); line.textContent = text; return line; }));
            };
            status.textContent = checker.supportsSprings ? 'Accepted by the compiled rotational spring checker.' : 'Accepted by the compiled inclined release checker.';
            render(readouts);
            const receipt = { protocol: checker.supportsSprings ? 'CV2011_ROTATIONAL_SPRING_1' : 'CV2011_INCLINED_RELEASE_1', ...token, bindings: envelope.bindings,
                artifact: checker.artifact, bundle: checker.bundle, inputDigest: result.inputDigest, packetDigest, reportDigest,
                sourceRequest: source, values, packet: new TextDecoder().decode(packet), report: new TextDecoder().decode(report) };
            exportText = JSON.stringify(receipt, null, 2);
            certificate.textContent = exportText; exportButton.hidden = false;
            acceptedGeneration = () => {
                if (!requests.isCurrent(token) || checker !== runtime) return;
                render(workedOutput); workedOutput.hidden = false; collapse.hidden = false;
                const axes = document.createElement('p'); axes.textContent = direction;
                workedOutput.prepend(axes);
                collapse.textContent = 'Collapse solution'; collapse.setAttribute('aria-expanded', 'true');
                drawDiagram(drawing, values.query.member, receipt, needsInclinedGeometry(drawing) ? 'inclined-diagram' : 'joint-diagram');
            };
            if (pendingGeneration === generationKey()) { pendingGeneration = null; acceptedGeneration(); }
            return;
        }
        if (checker.supportsHingeFrames) {
            if (result.frameProtocol !== 'hinge') throw Error('Unexpected release checker response.');
            const frame = decodeAcceptedHingePacket(packet);
            const sourceRequest = JSON.parse(new TextDecoder().decode(sourceBytes));
            const drawing: Model = sourceRequest.model;
            const labels = nodeLabels(drawing);
            const memberName = (id: string) => {
                const member = drawing.members.find(item => item.id === id);
                if (!member) throw Error('Accepted member missing from the captured drawing.');
                return memberLabel(drawing, member);
            };
            const nodeName = (id: string) => {
                const label = labels.get(id);
                if (!label) throw Error('Accepted node missing from the captured drawing.');
                return label;
            };
            status.textContent = frame.kind === 'solution' ? 'Accepted by the compiled hinge checker.' : frameStatus(frame);
            const lines = frameDescriptions({ ...frame, query: { ...frame.query, member: memberName(frame.query.member) },
                points: frame.points.map(point => ({ ...point, id: point.owner === 'member' ? memberName(point.id) : nodeName(point.id) })) });
            for (const face of frame.faces) {
                const description = face.released ? 'independent released-end rotation' :
                    referenceMember(drawing, face.node) === face.member ? 'reference rotation at the joint' : 'shares the reference rotation';
                lines.push(`Node ${nodeName(face.node)}, member ${memberName(face.member)} (${description}). Rotation ${roundedDecimal(face.rotation, 6)}${frame.kind === 'solution' ? ' rad' : ' in the mechanism motion'}.` +
                    (face.moment ? ` Section moment ${roundedDecimal(face.moment, 3)} kN m.` : '') +
                    (face.reaction && face.reaction.numerator !== '0' ? ` Separate end restraint moment ${roundedDecimal(face.reaction, 3)} kN m.` : ''));
            }
            const paragraphs = (items: string[]) => items.map(item => {
                const line = document.createElement('p'); line.textContent = item; return line;
            });
            readouts.replaceChildren(...paragraphs(lines));
            const receipt = { protocol: 'CV2011_HINGE_1', ...token, bindings: envelope.bindings,
                artifact: checker.artifact, bundle: checker.bundle, inputDigest: result.inputDigest, packetDigest,
                theorem: 'HingeFrame.Wire.accepted_bytes', sourceRequest,
                packet: new TextDecoder().decode(packet), values: frame, drawingLabels: lines };
            exportText = JSON.stringify(receipt, null, 2);
            certificate.textContent = exportText; exportButton.hidden = false;
            acceptedGeneration = () => {
                if (!requests.isCurrent(token) || checker !== runtime) return;
                const teaching = ['The connected ends move together horizontally and vertically. Each released end has its own rotation.'];
                if (frame.kind === 'solution') teaching.push('Balance moments on each released end. With no applied couple or rotational restraint there, the internal end moment is zero. A couple acts on the member selected in the drawing.');
                workedOutput.replaceChildren(...paragraphs([...teaching, ...lines]));
                workedOutput.hidden = false; collapse.hidden = false; collapse.textContent = 'Collapse solution';
                collapse.setAttribute('aria-expanded', 'true');
                if (frame.kind === 'solution') drawDiagram(drawing, frame.query.member, receipt, 'joint-diagram');
            };
            if (pendingGeneration === generationKey()) { pendingGeneration = null; acceptedGeneration(); }
            return;
        }
        if (result.frameProtocol === 'inclined') {
            if (!report || typeof reportDigest !== 'string' || await sha256(report) !== reportDigest)
                throw Error('Missing or changed accepted interval report.');
            if (!requests.isCurrent(token) || checker !== runtime) return;
            const values = decodeAcceptedIntervalReport(report);
            const sourceRequest = JSON.parse(new TextDecoder().decode(sourceBytes));
            bindIntervalDisplay(sourceRequest.model, sourceRequest.query, values);
            const presentation = renderIntervalValues(values, sourceRequest.model);
            const receipt = { protocol: 'CV2011_INCLINED_1', reportProtocol: 'CV2011_INCLINED_RESULT_1',
                ...token, bindings: envelope.bindings, artifact: result.artifact, bundle: checker.bundle,
                inputDigest: result.inputDigest, packetDigest, reportDigest,
                theorem: 'InclinedFrameIntervalReportSound.checkReport_sound', sourceRequest, values,
                packet: new TextDecoder().decode(packet), report: new TextDecoder().decode(report) };
            status.textContent = 'Accepted by the compiled proved checker: unique linear equilibrium with checked output intervals.';
            readouts.innerHTML = presentation;
            exportText = JSON.stringify(receipt, null, 2);
            certificate.textContent = exportText; exportButton.hidden = false;
            acceptedGeneration = () => {
                if (!requests.isCurrent(token) || checker !== runtime) return;
                let diagramReceipt: object = receipt;
                try {
                    const explanation = createIntervalExplanation(sourceRequest.model, sourceRequest.query, values);
                    workedOutput.innerHTML = renderIntervalExplanation(explanation, values, sourceRequest.model);
                    diagramReceipt = { ...receipt, explanation };
                    exportText = JSON.stringify(diagramReceipt, null, 2);
                    certificate.textContent = exportText;
                } catch {
                    workedOutput.innerHTML = '<p>The separate numerical calculation could not reproduce a suitable teaching substitution. The accepted intervals and their accuracy bounds remain available below.</p>' + presentation;
                }
                drawDiagram(sourceRequest.model, sourceRequest.query.member, diagramReceipt, 'inclined-diagram');
                workedOutput.hidden = false; collapse.hidden = false;
                collapse.textContent = 'Collapse solution'; collapse.setAttribute('aria-expanded', 'true');
            };
            if (pendingGeneration === generationKey()) { pendingGeneration = null; acceptedGeneration(); }
            return;
        }
        const frame = decodeAcceptedFramePacket(packet);
        status.textContent = `${frameStatus(frame)} Checked section: ${frame.query.cutSide} limit.`;
        readouts.replaceChildren(...frameDescriptions(frame).map(text => {
            const line = document.createElement('p'); line.textContent = text; return line;
        }));
        const receipt = { protocol: 'CV2011_FRAME_1', ...token, bindings: envelope.bindings,
            artifact: result.artifact, bundle: checker.bundle, inputDigest: result.inputDigest,
            packetDigest: result.packetDigest, theorem: 'RationalFrameSoundness.acceptance_actual_frame',
            sourceRequest: JSON.parse(new TextDecoder().decode(sourceBytes)), values: frame,
            packet: new TextDecoder().decode(packet) };
        exportText = JSON.stringify(receipt, null, 2);
        certificate.textContent = exportText; exportButton.hidden = false;
        acceptedGeneration = () => {
            if (!requests.isCurrent(token) || checker !== runtime) return;
            try {
                const report = createFrameWorked(receipt.sourceRequest.model, receipt.sourceRequest.query, frame,
                    { ...token, bindings: envelope.bindings, artifact: result.artifact, bundle: checker.bundle,
                        inputDigest: result.inputDigest, packetDigest });
                workedOutput.innerHTML = renderFrameWorked(report);
                workedOutput.hidden = false; collapse.hidden = false;
                collapse.textContent = 'Collapse solution'; collapse.setAttribute('aria-expanded', 'true');
                exportText = JSON.stringify({ ...receipt, workedSolution: report }, null, 2);
                certificate.textContent = exportText;
                if (frame.kind !== 'solution') return;
                drawDiagram(receipt.sourceRequest.model, frame.query.member, { ...receipt, workedSolution: report }, 'diagram');
            } catch (error) {
                workedOutput.textContent = `The checked results remain available in Verification. The explanatory solution could not be generated: ${String(error)}`;
            }
        };
        if (pendingGeneration === generationKey()) { pendingGeneration = null; acceptedGeneration(); }
    }
    function display(result: CheckerResult, envelope: Awaited<ReturnType<typeof createEvidenceEnvelope>>, token: { revision: number; request: number }) {
        if (result.state !== 'accepted' || !Array.isArray(result.checked) || result.checked.length !== 21) {
            clear(`Check failed: ${result.state}.`); return;
        }
        const checked = result.checked;
        // Only values decoded from the accepted ABI packet enter this panel.
        status.textContent = 'Accepted by the compiled proved checker.';
        const descriptions = [
            `BC midpoint moment: ${roundedDecimal(checked[19], 3)} kN m (sagging positive)`,
            `BC midpoint vertical displacement: ${roundedDecimal(checked[20], 3, 1000n)} mm (upward positive)`,
            `Base A: Fx ${roundedDecimal(checked[13], 3)} kN, Fy ${roundedDecimal(checked[14], 3)} kN, Mz ${roundedDecimal(checked[15], 3)} kN m`,
            `Base D: Fx ${roundedDecimal(checked[16], 3)} kN, Fy ${roundedDecimal(checked[17], 3)} kN, Mz ${roundedDecimal(checked[18], 3)} kN m`,
            'Displayed decimals are rounded from the exact certificate below.',
        ];
        readouts.replaceChildren(...descriptions.map(text => { const line = document.createElement('p'); line.textContent = text; return line; }));
        certificate.textContent = JSON.stringify({ profile: profileId, query: portalQuery, ...token,
            bindings: envelope.bindings, artifact: result.artifact, bundle: runtime?.bundle, inputDigest: result.inputDigest,
            theorem: 'PortalSoundness.acceptance_actual_portal', amplitude: checked[0],
            stabilityWitness: 'PortalSoundness.fixed_inverse',
            reactionTheorem: 'PortalSoundness.accepted_grouped_reactions',
            values: Object.fromEntries(outputIds.map((name, i) => [name, checked[i + 1]])) }, null, 2);
    }
    function update(nextMember: string, nextParameter: number) {
        member = nextMember; parameter = nextParameter;
        if (pendingGeneration !== generationKey()) pendingGeneration = null;
        sectionParameter.value = String(parameter);
        clearTimeout(debounce); runtime?.invalidate(); requests.invalidate();
        clear(enabled ? 'Checking current drawing…' : 'Generate enables local checking and reloads this workspace once.');
        let snapshot: Model;
        let query: EvidenceQuery;
        let frameMode: 'exact' | 'inclined' | 'hinge' = 'exact';
        try {
            // Capture before any asynchronous work, including hashing and debounce.
            snapshot = structuredClone(modelAtPresent());
            if (startingNow) { clear('Starting local checker…'); return; }
            const spring = usesSpring(snapshot);
            const hinge = spring || usesRelease(snapshot);
            if (enabled && runtime && (runtime.supportsHingeFrames !== hinge ||
                runtime.supportsSprings !== spring || hinge && runtime.supportsInclinedReleases !== (spring || needsInclinedGeometry(snapshot)))) { void start(); return; }
            if (!runtime || runtime.supportsFrames) {
                if (parameter === 0) cutSide.value = 'right';
                if (parameter === 1) cutSide.value = 'left';
                cutSide.options[0].disabled = parameter === 1;
                cutSide.options[1].disabled = parameter === 0;
                query = { member, parameter, cutSide: cutSide.value as 'left' | 'right', ...frameQueryConvention };
                if (hinge) frameMode = 'hinge';
                else try {
                    validateFrame(snapshot, query);
                    // Long binary fractions can exhaust exact elimination. Keep every
                    // source byte and ask the same ABI to check an interval proposal.
                    if (runtime?.supportsInclinedFrames && snapshot.loads.some(load => load.kind === 'distributed' &&
                        [load.t, load.end].some(t => !Number.isInteger(t * 1024)))) frameMode = 'inclined';
                }
                catch (error) {
                    if (runtime && !runtime.supportsInclinedFrames || !(error instanceof Error) || !error.message.startsWith('Unsupported:')) throw error;
                    validateIntervalFrame(snapshot, query);
                    frameMode = 'inclined';
                }
            } else {
                const value = portalAmplitude(snapshot);
                amplitude.value = String(value);
                if (member !== 'BC' || parameter !== 0.5) throw new Error('Unsupported query: select BC at its midpoint.');
                query = portalQuery;
            }
            requests.update(snapshot, query);
        } catch (error) { clear(String(error)); return; }
        if (!enabled || !runtime) return;
        // An edit cancels synchronous inclined arithmetic by terminating its
        // worker. Recreate the checker before submitting the captured revision.
        if (runtime.needsReset) { void start(); return; }
        const checker = runtime, token = requests.begin();
        debounce = setTimeout(async () => {
            try {
                const bytes = checker.supportsFrames
                    ? new TextEncoder().encode(JSON.stringify({ model: snapshot, query }))
                    : encodeCandidate(portalCandidate(portalAmplitude(snapshot)));
                const envelope = await createEvidenceEnvelope(snapshot, query);
                if (!requests.isCurrent(token) || checker !== runtime) return;
                const result = checker.supportsFrames ? await checker.checkFrame(bytes, frameMode) : await checker.check(bytes);
                if (!requests.isCurrent(token) || checker !== runtime) return;
                const current = requests.accept(token, result);
                if (checker.supportsFrames) await displayFrame(current, envelope, token, checker, bytes);
                else display(current, envelope, token);
            } catch (error) { if (requests.isCurrent(token)) clear(String(error)); }
        }, 150);
    }
    cutSide.onchange = () => update(member, parameter);
    generate.onclick = () => {
        if (acceptedGeneration) { acceptedGeneration(); return; }
        pendingGeneration = generationKey();
        if (!enabled) {
            if (runtime) {
                if (!startingNow) void start();
                return;
            }
            activate.click(); return;
        }

    };
    collapse.onclick = () => {
        workedOutput.hidden = !workedOutput.hidden;
        collapse.textContent = workedOutput.hidden ? 'Expand solution' : 'Collapse solution';
        collapse.setAttribute('aria-expanded', String(!workedOutput.hidden));
    };
    sectionParameter.oninput = () => {
        const value = sectionParameter.valueAsNumber;
        if (!Number.isFinite(value) || value < 0 || value > 1) {
            requests.invalidate(); runtime?.invalidate(); clear('Enter a member parameter from 0 to 1.'); return;
        }
        changeSectionParameter(value);
        update(member, value);
    };
    exportButton.onclick = () => {
        if (!exportText) return;
        const url = URL.createObjectURL(new Blob([exportText], { type: 'application/json' }));
        const link = document.createElement('a'); link.href = url; link.download = 'checked-frame.json'; link.click();
        setTimeout(() => URL.revokeObjectURL(url), 0);
    };
    amplitude.oninput = () => {
        const value = amplitude.valueAsNumber;
        if (!Number.isFinite(value)) { requests.invalidate(); runtime?.invalidate(); clear('Enter a finite uniform load.'); return; }
        changeUniformLoad(value);
        // A blank/nonfinite edit invalidates without changing the stored model.
        // Re-entering that same finite value must still start a fresh request.
        update(member, parameter);
    };
    activate.onclick = async () => {
        stop(); clear('Enabling local checking…');
        try {
            localStorage.setItem(storageKey, JSON.stringify(modelAtPresent()));
            prepareReload();
            const existing = await navigator.serviceWorker.getRegistrations();
            const ancestor = existing.find(registration => scope.href.startsWith(registration.scope) && registration.scope !== scope.href);
            const knownMain = new URL('../main-checker-sw.js', scope).href;
            if (ancestor && !(isPortalWorkspace && [ancestor.active, ancestor.waiting, ancestor.installing]
                .filter(worker => worker !== null).every(worker => worker!.scriptURL === knownMain)))
                throw new Error('Another service worker controls this workspace.');
            if (existing.some(registration => registration.scope === scope.href && !ownsRegistration(registration))) throw new Error('Another service worker owns this scope.');
            const registration = await navigator.serviceWorker.register(isolationScript, { scope: scope.href });
            if (registration.scope !== scope.href) throw new Error('Unexpected checker scope');
            // An activation error must still leave an exact-scope cleanup path.
            deactivate.hidden = false;
            await new Promise<void>((resolve, reject) => {
                const changed = () => {
                    if (navigator.serviceWorker.controller?.scriptURL !== isolationScript) return;
                    clearTimeout(timer); navigator.serviceWorker.removeEventListener('controllerchange', changed); resolve();
                };
                const timer = setTimeout(() => {
                    navigator.serviceWorker.removeEventListener('controllerchange', changed);
                    reject(new Error('Activation timeout'));
                }, 10000);
                navigator.serviceWorker.addEventListener('controllerchange', changed);
                changed();
            });
            if (pendingGeneration === generationKey()) sessionStorage.setItem(generationStorage, pendingGeneration);
            location.reload();
        } catch (error) { clear(String(error)); }
    };
    deactivate.onclick = async () => {
        pendingGeneration = null;
        stop(); clear('Disabling local checking…');
        localStorage.setItem(storageKey, JSON.stringify(modelAtPresent()));
        prepareReload();
        sessionStorage.removeItem(generationStorage);
        for (const registration of await navigator.serviceWorker.getRegistrations()) {
            if (ownsRegistration(registration)) await registration.unregister();
        }
        if (isPortalWorkspace) location.href = new URL('../', scope).href;
        else location.reload();
    };
    reset.onclick = () => void start();
    if (navigator.serviceWorker.controller?.scriptURL === isolationScript) {
        deactivate.hidden = false;
        if (crossOriginIsolated) void start();
    }
    return { update };
}
