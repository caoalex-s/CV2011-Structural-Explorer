// Explicit activation only. Importing this module does not register a worker.
import { Checker } from './harness.mjs';

const scope = new URL('./', import.meta.url);
const expectedScope = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/checker-preview/64b31158/';
const shim = new URL('./isolation-sw.js', scope).href;
const reloadKey = 'checker-preview:64b31158:reload-pending';
const status = document.querySelector('#status');
const output = document.querySelector('output');
const activateButton = document.querySelector('#activate');
const checkButton = document.querySelector('#check');
const resetButton = document.querySelector('#reset');
const deactivateButton = document.querySelector('#deactivate');
let checker = null;
let busy = false;

export const examples = Object.freeze({
    zero: '0\n1\n0\n7', positive: '10\n1\n5\n1', negative: '-10\n1\n-5\n1',
    fraction: '3\n7\n3\n14',
    large: '123456789012345678901234567890123456789012345678901234567890\n1\n123456789012345678901234567890123456789012345678901234567890\n2',
    wrong: '10\n1\n6\n1', malformed: '0\n0\n0\n1',
});
export const preview = { get checker() { return checker; }, get scope() { return scope.href; } };

function closeChecker() {
    if (!checker) return;
    if (checker.current) {
        clearTimeout(checker.current.timer);
        checker.current.resolve({ state: 'stale' });
        checker.current = null;
    }
    checker.worker.terminate();
    checker = null;
}

function fail(error) {
    closeChecker();
    busy = false;
    activateButton.disabled = true;
    checkButton.disabled = true;
    resetButton.disabled = true;
    deactivateButton.disabled = false;
    status.textContent = `Preview stopped: ${error.message}. Deactivate and leave before another explicit attempt.`;
}

async function startChecker() {
    if (!crossOriginIsolated || typeof SharedArrayBuffer !== 'function' ||
        navigator.serviceWorker.controller?.scriptURL !== shim) throw new Error('Preview isolation is unavailable');
    closeChecker();
    checker = new Checker();
    const ready = await checker.ready;
    if (!ready.isolated || ready.sharedArrayBuffer !== 'function') throw new Error('Checker worker is not isolated');
    status.textContent = 'Ready. Checks run in this browser using the recovered compiled artifact.';
    activateButton.disabled = true;
    checkButton.disabled = false;
    resetButton.disabled = false;
    deactivateButton.disabled = false;
    busy = false;
}

async function waitForPreviewControl() {
    await new Promise((resolve, reject) => {
        const finish = () => {
            if (navigator.serviceWorker.controller?.scriptURL !== shim) return;
            clearTimeout(timer);
            navigator.serviceWorker.removeEventListener('controllerchange', finish);
            resolve();
        };
        const timer = setTimeout(() => {
            navigator.serviceWorker.removeEventListener('controllerchange', finish);
            reject(new Error('Preview activation timed out'));
        }, 15000);
        navigator.serviceWorker.addEventListener('controllerchange', finish);
        finish();
    });
}

activateButton.addEventListener('click', async () => {
    if (busy) return;
    busy = true;
    activateButton.disabled = true;
    deactivateButton.disabled = true;
    try {
        if (scope.href !== expectedScope || !isSecureContext || !navigator.serviceWorker) {
            throw new Error('Activation is limited to the approved HTTPS preview URL');
        }
        const controlling = navigator.serviceWorker.controller;
        if (controlling && controlling.scriptURL !== shim) throw new Error('Another service worker controls this page');
        const existing = (await navigator.serviceWorker.getRegistrations()).find(item => item.scope === scope.href);
        if (existing && [existing.active, existing.waiting, existing.installing].some(worker => worker && worker.scriptURL !== shim)) {
            throw new Error('The preview scope has an unexpected worker');
        }
        if (controlling && crossOriginIsolated) return await startChecker();
        status.textContent = 'Activating this preview directory. One reload will follow.';
        await navigator.serviceWorker.register(shim, { scope: scope.href, updateViaCache: 'none' });
        await waitForPreviewControl();
        sessionStorage.setItem(reloadKey, '1');
        location.reload();
    } catch (error) { fail(error); }
});

checkButton.addEventListener('click', async () => {
    const active = checker;
    if (!active || busy) return;
    let response;
    try { response = await active.check(examples[document.querySelector('#example').value]); }
    catch (error) { fail(error); return; }
    if (active !== checker) return;
    const descriptions = { accepted: 'Accepted: 2 × x = a.', rejected: 'Rejected: 2 × x differs from a.',
        malformed: 'Malformed input: the rational encoding is invalid.', stale: 'Superseded by a newer check.',
        limit: 'Input exceeds the checker limit.', timeout: 'Checker timed out. Reset or deactivate the preview.' };
    output.textContent = descriptions[response.state] ?? 'The checker returned an error.';
});

resetButton.addEventListener('click', async () => {
    if (busy) return;
    busy = true;
    checkButton.disabled = true;
    resetButton.disabled = true;
    deactivateButton.disabled = true;
    output.textContent = 'No check has run since reset.';
    try { await startChecker(); } catch (error) { fail(error); }
});

deactivateButton.addEventListener('click', async () => {
    if (busy) return;
    busy = true;
    deactivateButton.disabled = true;
    activateButton.disabled = true;
    checkButton.disabled = true;
    resetButton.disabled = true;
    closeChecker();
    sessionStorage.removeItem(reloadKey);
    try {
        if (scope.href !== expectedScope) throw new Error('Unexpected preview URL');
        // Never unregister another scope or remove origin-wide caches/storage.
        const exact = (await navigator.serviceWorker.getRegistrations()).find(item => item.scope === scope.href);
        if (exact) await exact.unregister();
        location.replace(new URL('../../', scope));
    } catch (error) { fail(error); }
});

// Only a user-triggered activation can leave this one-use continuation marker.
if (sessionStorage.getItem(reloadKey) === '1') {
    sessionStorage.removeItem(reloadKey);
    busy = true;
    activateButton.disabled = true;
    deactivateButton.disabled = true;
    startChecker().catch(fail); // Failure stops here; there is no second reload.
}
