/** Dedicated checked portal panel, sharing the ordinary workspace and edit lifecycle. */
import { EvidenceRequests, createEvidenceEnvelope } from './model-evidence.js';
import { portalAmplitude, portalCandidate, encodeCandidate, portalQuery, outputIds, roundedDecimal, profileId } from './portal-candidate.js';
import type { Model } from './engine.js';
import { PortalRuntime } from './portal-runtime.js';
import type { CheckerResult } from './portal-runtime.js';

export const isPortalWorkspace = location.pathname.replace(/index\.html$/, '').endsWith('/portal-checker/');
export const portalStorageKey = 'cv2011-checked-portal-model/v1';
const scope = new URL('./', location.href);
const isolationScript = new URL('isolation-sw.js', scope).href;
function ownsRegistration(registration: ServiceWorkerRegistration): boolean {
    return registration.scope === scope.href &&
        [registration.active, registration.waiting, registration.installing].some(worker => worker?.scriptURL === isolationScript);
}

export function createPortalPanel(modelAtPresent: () => Model, changeUniformLoad: (value: number) => void) {
    if (!isPortalWorkspace) return { update(_member: string, _parameter: number) {} };
    const host = document.createElement('section');
    host.className = 'portal-certificate';
    host.innerHTML = `<h2>Checked portal response</h2>
      <p>Keep the original portal and vary its uniform BC load. Positive load acts upward.</p>
      <label>Uniform load (kN/m) <input id="portal-amplitude" type="number" step="any" value="-5"></label>
      <button id="portal-activate">Enable local checking</button><button id="portal-reset" hidden>Reset checker</button>
      <button id="portal-deactivate" hidden>Disable local checking</button>
      <p id="portal-status" role="status">Local checking is off.</p><div id="portal-readouts"></div>
      <details><summary>Scope and exact certificate</summary><p>The checked values cover joint displacements, both base reactions, and BC midpoint moment and vertical displacement. Diagram curves remain numerical. Acceptance uses a compiled Lean checker and relies on its compiler, runtime, decoder, and input binding. Each edit does not invoke the Lean kernel.</p><pre id="portal-certificate"></pre></details>`;
    document.getElementById('workspace')!.prepend(host);
    const status = host.querySelector<HTMLElement>('#portal-status')!;
    const readouts = host.querySelector<HTMLElement>('#portal-readouts')!;
    const certificate = host.querySelector<HTMLElement>('#portal-certificate')!;
    const amplitude = host.querySelector<HTMLInputElement>('#portal-amplitude')!;
    const activate = host.querySelector<HTMLButtonElement>('#portal-activate')!;
    const deactivate = host.querySelector<HTMLButtonElement>('#portal-deactivate')!;
    const reset = host.querySelector<HTMLButtonElement>('#portal-reset')!;
    const requests = new EvidenceRequests();
    let runtime: PortalRuntime | null = null;
    let debounce: ReturnType<typeof setTimeout> | undefined;
    let member = 'BC', parameter = 0.5;
    let enabled = false;

    function clear(message: string) { status.textContent = message; readouts.replaceChildren(); certificate.textContent = ''; }
    function stop() { clearTimeout(debounce); requests.invalidate(); runtime?.dispose(); runtime = null; enabled = false; }
    async function start() {
        stop(); clear('Starting local checker…');
        runtime = new PortalRuntime();
        const starting = runtime;
        try {
            await starting.ready;
            if (starting !== runtime) return;
            enabled = true; activate.hidden = true; deactivate.hidden = false; reset.hidden = false;
            update(member, parameter);
        } catch (error) { if (starting === runtime) clear(`Checking unavailable: ${String(error)}`); }
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
            values: Object.fromEntries(outputIds.map((name, i) => [name, checked[i + 1]])) }, null, 2);
    }
    function update(nextMember: string, nextParameter: number) {
        member = nextMember; parameter = nextParameter;
        clearTimeout(debounce); runtime?.invalidate(); requests.invalidate();
        clear(enabled ? 'Checking…' : 'Enable local checking to check this portal.');
        let snapshot: Model;
        try {
            // Capture before any asynchronous work, including hashing and debounce.
            snapshot = structuredClone(modelAtPresent());
            const value = portalAmplitude(snapshot);
            amplitude.value = String(value);
            if (member !== 'BC' || parameter !== 0.5) throw new Error('Unsupported query: select BC at its midpoint.');
            requests.update(snapshot, portalQuery);
        } catch (error) { clear(String(error)); return; }
        if (!enabled || !runtime) return;
        const checker = runtime, token = requests.begin();
        debounce = setTimeout(async () => {
            try {
                const bytes = encodeCandidate(portalCandidate(portalAmplitude(snapshot)));
                const envelope = await createEvidenceEnvelope(snapshot, portalQuery);
                if (!requests.isCurrent(token) || checker !== runtime) return;
                const result = await checker.check(bytes);
                if (!requests.isCurrent(token) || checker !== runtime) return;
                display(requests.accept(token, result), envelope, token);
            } catch (error) { if (requests.isCurrent(token)) clear(String(error)); }
        }, 150);
    }
    amplitude.oninput = () => {
        const value = amplitude.valueAsNumber;
        if (!Number.isFinite(value)) { requests.invalidate(); runtime?.invalidate(); clear('Enter a finite uniform load.'); return; }
        changeUniformLoad(value);
    };
    activate.onclick = async () => {
        stop(); clear('Enabling local checking…');
        try {
            localStorage.setItem(portalStorageKey, JSON.stringify(modelAtPresent()));
            const existing = await navigator.serviceWorker.getRegistrations();
            if (existing.some(registration => scope.href.startsWith(registration.scope) && registration.scope !== scope.href)) throw new Error('Another service worker controls this workspace.');
            if (existing.some(registration => registration.scope === scope.href && !ownsRegistration(registration))) throw new Error('Another service worker owns this scope.');
            const registration = await navigator.serviceWorker.register(isolationScript, { scope: scope.href });
            if (registration.scope !== scope.href) throw new Error('Unexpected checker scope');
            // An activation error must still leave an exact-scope cleanup path.
            deactivate.hidden = false;
            await navigator.serviceWorker.ready;
            if (!navigator.serviceWorker.controller) await new Promise<void>((resolve, reject) => {
                const timer = setTimeout(() => reject(new Error('Activation timeout')), 10000);
                navigator.serviceWorker.addEventListener('controllerchange', () => { clearTimeout(timer); resolve(); }, { once: true });
            });
            location.reload();
        } catch (error) { clear(String(error)); }
    };
    deactivate.onclick = async () => {
        stop(); clear('Disabling local checking…');
        localStorage.setItem(portalStorageKey, JSON.stringify(modelAtPresent()));
        for (const registration of await navigator.serviceWorker.getRegistrations()) {
            if (ownsRegistration(registration)) await registration.unregister();
        }
        location.href = new URL('../', scope).href;
    };
    reset.onclick = () => void start();
    if (navigator.serviceWorker.controller?.scriptURL === isolationScript) {
        deactivate.hidden = false;
        if (crossOriginIsolated) void start();
    }
    return { update };
}
