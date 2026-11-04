import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';

// Browser imports use emitted .js filenames. Resolve their source counterparts
// here to test the same module before the static build.
const webDirectory = new URL('../web/', import.meta.url).href;
registerHooks({
    resolve(specifier, context, next) {
        if (context.parentURL?.startsWith(webDirectory) && specifier.startsWith('./') && specifier.endsWith('.js')) {
            return next(specifier.replace(/\.js$/, '.ts'), context);
        }
        return next(specifier, context);
    },
});
const { createLearningSession } = await import('../web/learning-session.ts');

function browserFixture(t) {
    const storage = () => {
        const values = new Map();
        return { getItem: key => values.get(key) ?? null, setItem: (key, value) => values.set(key, value) };
    };
    const elements = new Map();
    const globals = {
        localStorage: storage(),
        sessionStorage: storage(),
        location: { hostname: '127.0.0.1', origin: 'http://127.0.0.1:9876' },
        document: { getElementById(id) {
            if (!elements.has(id)) elements.set(id, { textContent: '', value: '' });
            return elements.get(id);
        } },
    };
    for (const [name, value] of Object.entries(globals)) {
        const descriptor = Object.getOwnPropertyDescriptor(globalThis, name);
        Object.defineProperty(globalThis, name, { configurable: true, value });
        t.after(() => {
            if (descriptor) Object.defineProperty(globalThis, name, descriptor);
            else delete globalThis[name];
        });
    }
    return globals;
}

function attemptContext() {
    return {
        model: example('beam'), section: 0.5, step: 'moment', side: 'compression',
        hintUsed: true, solutionRevealed: false,
    };
}

test('offline attempts preserve their original model and remain unverified', async t => {
    const browser = browserFixture(t);
    t.mock.method(globalThis, 'fetch', () => { throw Error('Offline record must not call a server.'); });
    const session = createLearningSession({ notify() {}, onConnectionChange() {} });
    const context = attemptContext();
    const originalLoad = context.model.loads[0].fy;
    const attempt = await session.record(context, 'submit', '20*8/4', 'kN m');
    context.model.loads[0].fy = -500;
    const saved = JSON.parse(browser.localStorage.getItem('cv2011-attempts'));
    assert.equal(saved.length, 1);
    assert.equal(saved[0].model.loads[0].fy, originalLoad);
    assert.equal(attempt.model.loads[0].fy, originalLoad);
    assert.equal(saved[0].courseId, 'local-unassigned');
    assert.equal(saved[0].answer, '20*8/4');
    assert.equal(saved[0].side, 'compression');
    assert.equal(saved[0].hintUsed, true);
    assert.equal(saved[0].solutionRevealed, false);
    assert.equal(saved[0].result.status, 'unresolved');
    assert.equal(saved[0].synced, undefined);
});

test('connected attempts snapshot before the response and never persist credentials in records', async t => {
    const browser = browserFixture(t);
    const sent = [];
    let finishResponse;
    t.mock.method(globalThis, 'fetch', async (url, options) => {
        if (url.endsWith('/api/health')) return { json: async () => ({ sympy: true,
            localDemo: { courseId: 'TEST-001', token: 'test-token', instructor: 'test-instructor' } }) };
        if (url.endsWith('/api/me')) return { ok: true, json: async () => ({ courseId: 'TEST-001' }) };
        sent.push(JSON.parse(options.body));
        return new Promise(resolve => { finishResponse = () => resolve({ ok: true,
            json: async () => ({ result: { status: 'correct', category: 'correct', message: 'Checked.' } }) }); });
    });
    const session = createLearningSession({ notify() {}, onConnectionChange() {} });
    await session.connect();
    assert.equal(session.connected, true);
    assert.equal(sent.length, 0, 'Connecting does not submit sandbox edits.');
    const context = attemptContext();
    const pending = session.record(context, 'submit', '40', 'kN m');
    context.model.loads[0].fy = -500;
    context.step = 'shear';
    finishResponse();
    const attempt = await pending;
    assert.equal(attempt.step, 'moment');
    assert.equal(attempt.model.loads[0].fy, sent[0].model.loads[0].fy);
    assert.notEqual(attempt.model.loads[0].fy, -500);
    assert.equal(attempt.result.status, 'correct');
    assert.equal(attempt.synced, true);
    const saved = browser.localStorage.getItem('cv2011-attempts');
    assert.doesNotMatch(saved, /test-token|test-instructor/);
    assert.equal(JSON.parse(saved)[0].courseId, 'TEST-001');
    assert.equal(browser.sessionStorage.getItem('cv2011-token'), 'test-token');
});
