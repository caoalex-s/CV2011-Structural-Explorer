/** Dedicated checked portal panel, sharing the ordinary workspace and edit lifecycle. */
import { EvidenceRequests, createEvidenceEnvelope } from './model-evidence.js';
import { portalAmplitude, portalCandidate, encodeCandidate, portalQuery, outputIds, roundedDecimal, profileId } from './portal-candidate.js';
import type { Model } from './engine.js';
import { PortalRuntime } from './portal-runtime.js';
import { sha256 } from './portal-runtime.js';
import type { CheckerResult } from './portal-runtime.js';
import { validateFrame, frameQueryConvention } from './frame-candidate.js';
import { decodeAcceptedFramePacket } from './frame-result.js';
import { frameDescriptions, frameStatus } from './frame-display.js';
import type { EvidenceQuery } from './model-evidence.js';
import { createFrameWorked } from './frame-worked.js';
import { renderFrameWorked } from './frame-worked-view.js';

export const isPortalWorkspace = location.pathname.replace(/index\.html$/, '').endsWith('/portal-checker/');
// The same controller serves the main workspace and the compatible scoped URL.
export const isCheckedWorkspace = location.pathname.replace(/index\.html$/, '') === new URL('./', import.meta.url).pathname;
export const portalStorageKey = 'cv2011-checked-portal-model/v1';
const scope = new URL('./', location.href);
const isolationScript = new URL(isPortalWorkspace ? 'isolation-sw.js' : 'main-checker-sw.js', scope).href;
const runtimeUrl = new URL(isPortalWorkspace ? './bundle/worker.mjs' : './portal-checker/bundle/worker.mjs', scope);
function ownsRegistration(registration: ServiceWorkerRegistration): boolean {
    return registration.scope === scope.href &&
        [registration.active, registration.waiting, registration.installing].filter(worker => worker !== null)
            .every(worker => worker!.scriptURL === isolationScript) &&
        Boolean(registration.active || registration.waiting || registration.installing);
}

export function createPortalPanel(modelAtPresent: () => Model, changeUniformLoad: (value: number) => void,
    changeSectionParameter: (value: number) => void, storageKey = portalStorageKey, prepareReload: () => void = () => {}) {
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
      <p id="portal-scope">Diagram curves remain numerical. Acceptance uses a compiled Lean checker and relies on its compiler, runtime, decoder, and input binding. Each edit does not invoke the Lean kernel.</p><pre id="portal-certificate"></pre></details>`;
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
    let generationRequested = false;
    const generationStorage = storageKey + '/generate';
    const sideStorage = storageKey + '/cut-side';
    const generationKey = () => JSON.stringify({ model: modelAtPresent(), member, parameter, side: cutSide.value });
    try {
        const saved = JSON.parse(sessionStorage.getItem(sideStorage) || 'null');
        if (saved?.model === JSON.stringify(modelAtPresent()) && ['left', 'right'].includes(saved.side)) cutSide.value = saved.side;
    } catch { /* A fresh query is checked even when view restoration fails. */ }
    window.addEventListener('beforeunload', () => sessionStorage.setItem(sideStorage,
        JSON.stringify({ model: JSON.stringify(modelAtPresent()), side: cutSide.value })));

    function clear(message: string) {
        status.textContent = message; readouts.replaceChildren(); certificate.textContent = '';
        exportText = ''; exportButton.hidden = true;
        acceptedGeneration = null; workedOutput.replaceChildren(); collapse.hidden = true;
        workedOutput.hidden = false;
    }
    function stop() { clearTimeout(debounce); requests.invalidate(); runtime?.dispose(); runtime = null; enabled = false; }
    async function start() {
        stop(); clear('Starting local checker…');
        startingNow = true;
        try { runtime = new PortalRuntime(runtimeUrl); }
        catch (error) { startingNow = false; reset.hidden = false; clear(`Checking unavailable: ${String(error)}`); return; }
        const starting = runtime;
        starting.onFailure = reason => {
            if (starting !== runtime) return;
            requests.invalidate(); enabled = false; startingNow = false; reset.hidden = false; clear(reason);
        };
        try {
            await starting.ready;
            if (starting !== runtime) return;
            if (!starting.supportsAffineFrames) throw Error('This checker bundle predates affine-load support. Refresh after the updated checker is published.');
            enabled = true; startingNow = false; activate.hidden = true; deactivate.hidden = false; reset.hidden = false;
            if (starting.supportsFrames) {
                amplitude.closest('label')!.hidden = true;
                host.querySelector<HTMLElement>('#frame-side-label')!.hidden = false;
                host.querySelector<HTMLElement>('#frame-parameter-label')!.hidden = false;
                host.querySelector('#portal-scope')!.textContent = 'The checker covers linear Euler–Bernoulli frames with positive EA and EI, fixed or pin supports, and rollers at 0, 90, 180, or 270 degrees. Point forces, couples, and linearly varying vertical loads may act over partial or overlapping member intervals. Distributed loads may change sign. Drawing labels are downward positive; the stored global-y forces are upward positive. Up to 8 members, 16 nodes, 16 active points, 16 segments, 16 supports, and 16 loads are supported within the arithmetic and one-second limits. Inputs retain their exact parsed binary64 values. Source and certificate rationals allow 128 digits, with 256 digits for normalized candidate intermediates and 513 before reduction. The packet limit is 1 MiB. A limit or timeout is inconclusive. N is positive in tension, M is positive in sagging, dM/dx = V, global y is upward, and rotation is counterclockwise. Diagram curves remain numerical. Acceptance relies on the proved compiled checker, its compiler and runtime, and the decoder and input binding. Edits are checked locally without invoking the Lean kernel.';
            }
            update(member, parameter);
            // A single explicit Generate survives only the activation reload of
            // the same saved drawing. Subsequent edits revoke generation intent.
            if (sessionStorage.getItem(generationStorage) === generationKey()) generationRequested = true;
            sessionStorage.removeItem(generationStorage);
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
        if (await sha256(packet) !== result.packetDigest) throw Error('Accepted packet identity changed.');
        if (!requests.isCurrent(token) || checker !== runtime) return;
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
            } catch (error) {
                workedOutput.textContent = `The checked results remain available in Verification. The explanatory solution could not be generated: ${String(error)}`;
            }
        };
        if (generationRequested) { generationRequested = false; acceptedGeneration(); }
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
        generationRequested = false;
        sectionParameter.value = String(parameter);
        clearTimeout(debounce); runtime?.invalidate(); requests.invalidate();
        clear(enabled ? 'Checking current drawing…' : 'Generate enables local checking and reloads this workspace once.');
        let snapshot: Model;
        let query: EvidenceQuery;
        try {
            // Capture before any asynchronous work, including hashing and debounce.
            snapshot = structuredClone(modelAtPresent());
            if (!runtime || runtime.supportsFrames) {
                if (parameter === 0) cutSide.value = 'right';
                if (parameter === 1) cutSide.value = 'left';
                cutSide.options[0].disabled = parameter === 1;
                cutSide.options[1].disabled = parameter === 0;
                query = { member, parameter, cutSide: cutSide.value as 'left' | 'right', ...frameQueryConvention };
                validateFrame(snapshot, query);
            } else {
                const value = portalAmplitude(snapshot);
                amplitude.value = String(value);
                if (member !== 'BC' || parameter !== 0.5) throw new Error('Unsupported query: select BC at its midpoint.');
                query = portalQuery;
            }
            requests.update(snapshot, query);
        } catch (error) { clear(String(error)); return; }
        if (!enabled || !runtime) return;
        const checker = runtime, token = requests.begin();
        debounce = setTimeout(async () => {
            try {
                const bytes = checker.supportsFrames
                    ? new TextEncoder().encode(JSON.stringify({ model: snapshot, query }))
                    : encodeCandidate(portalCandidate(portalAmplitude(snapshot)));
                const envelope = await createEvidenceEnvelope(snapshot, query);
                if (!requests.isCurrent(token) || checker !== runtime) return;
                const result = checker.supportsFrames ? await checker.checkFrame(bytes) : await checker.check(bytes);
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
        if (!enabled) {
            sessionStorage.setItem(generationStorage, generationKey());
            if (runtime) {
                if (startingNow) generationRequested = true;
                else void start();
                return;
            }
            activate.click(); return;
        }
        generationRequested = true;
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
            location.reload();
        } catch (error) { clear(String(error)); }
    };
    deactivate.onclick = async () => {
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
