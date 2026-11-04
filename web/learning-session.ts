/** Verifier connection and pseudonymous records. Sandbox edits never enter this queue. */
import type { Model } from './engine.js';
import { element as $, escapeHtml as escape, downloadJson as download } from './ui.js';

export interface Attempt {
    id: string;
    timestamp: string;
    courseId: string;
    event: string;
    model: Model;
    section: number;
    step: string;
    answer: string;
    units: string;
    side: string;
    hintUsed: boolean;
    solutionRevealed: boolean;
    result?: {
        status: string;
        category: string;
        message: string;
    };
    synced?: boolean;
}

export interface AttemptContext {
    model: Model;
    section: number;
    step: string;
    side: string;
    hintUsed: boolean;
    solutionRevealed: boolean;
}

interface SessionOptions {
    notify: (message: string) => void;
    onConnectionChange: () => void;
}

/** Initialise once. Credentials stay in browser session storage, never in model exports. */
export function createLearningSession({ notify: toast, onConnectionChange }: SessionOptions) {
    let online = false;
    let localDemo = false;
    const loopback = ['localhost', '127.0.0.1'].includes(location.hostname);
    let config = {
        url: localStorage.getItem('cv2011-api') || (loopback ? location.origin : ''),
        courseId: localStorage.getItem('cv2011-id') || '',
        token: sessionStorage.getItem('cv2011-token') || '',
        instructor: sessionStorage.getItem('cv2011-instructor') || '',
    };
    let attempts: Attempt[] = [];
    try {
        attempts = JSON.parse(localStorage.getItem('cv2011-attempts') || '[]');
    }
    catch {
        attempts = [];
    }

    function saveAttempts(): void {
        localStorage.setItem('cv2011-attempts', JSON.stringify(attempts));
        updateSession();
    }

    async function api(path: string, payload?: unknown, instructor = false): Promise<any> {
        if (!config.url)
            throw Error('No verifier configured.');
        const response = await fetch(config.url.replace(/\/$/, '') + path, {
            method: payload === undefined ? 'GET' : 'POST',
            headers: {
                'Content-Type': 'application/json',
                'Authorization': `Bearer ${instructor ? config.instructor : config.token}`,
            },
            body: payload === undefined ? undefined : JSON.stringify(payload),
            signal: AbortSignal.timeout(path === '/api/worked-solution' ? 60000 : 15000),
        });
        const result = await response.json();
        if (!response.ok)
            throw Error(result.error || 'Request failed');
        return result;
    }
    /** Capture before awaiting the server: later model edits belong to a different attempt. */
    async function record(context: AttemptContext, event: string, answer: string, units: string): Promise<Attempt> {
        const attempt: Attempt = {
            id: crypto.randomUUID(),
            timestamp: new Date().toISOString(),
            courseId: config.courseId || 'local-unassigned',
            event,
            model: structuredClone(context.model),
            section: context.section,
            step: context.step,
            side: context.side,
            hintUsed: context.hintUsed,
            solutionRevealed: context.solutionRevealed,
            answer,
            units,
            result: {
                status: 'unresolved',
                category: 'pending_verification',
                message: 'This submission will be checked after you connect to the verifier. You can export your local records.',
            },
        };
        if (online)
            try {
                const response = await api('/api/attempts', attempt);
                attempt.result = response.result;
                attempt.synced = true;
            }
            catch (error) {
                toast(`Record retained locally: ${String(error)}`);
            }
        attempts.push(attempt);
        saveAttempts();
        return attempt;
    }
    function updateSession() {
        $('session-status').textContent = online ? `${localDemo ? 'Local verification service' : 'Connected verifier'} · ${config.courseId}. ${attempts.filter(a => a.synced).length} recorded events on this device.` : `Local exploration · ${attempts.filter(a => !a.synced).length} events awaiting verification. Connect your course verifier to record class results.`;
    }
    async function connect() {
        online = false;
        localDemo = false;
        if (config.url)
            try {
                const response = await fetch(config.url.replace(/\/$/, '') + '/api/health', { signal: AbortSignal.timeout(3000) });
                const health = await response.json();
                if (health.localDemo && !config.token) {
                    config.courseId = health.localDemo.courseId;
                    config.token = health.localDemo.token;
                    config.instructor = health.localDemo.instructor;
                    sessionStorage.setItem('cv2011-token', config.token);
                    sessionStorage.setItem('cv2011-instructor', config.instructor);
                }
                localDemo = !!health.localDemo;
                online = health.sympy === true && !!config.token;
                if (online) {
                    const identity = await api('/api/me');
                    if (identity.courseId !== config.courseId && config.courseId)
                        throw Error('Course ID does not correspond to this access token.');
                    config.courseId = identity.courseId;
                }
            }
            catch {
                online = false;
            }
        onConnectionChange();
    }
    $('settings-button').onclick = () => {
        $<HTMLInputElement>('api-url').value = config.url;
        $<HTMLInputElement>('course-id').value = config.courseId;
        $<HTMLInputElement>('access-token').value = config.token;
        $<HTMLInputElement>('instructor-token').value = config.instructor;
        $<HTMLDialogElement>('settings').showModal();
    };
    $('save-settings').onclick = async () => {
        config = {
            url: $<HTMLInputElement>('api-url').value.trim(),
            courseId: $<HTMLInputElement>('course-id').value.trim(),
            token: $<HTMLInputElement>('access-token').value.trim(),
            instructor: $<HTMLInputElement>('instructor-token').value.trim(),
        };
        localStorage.setItem('cv2011-api', config.url);
        localStorage.setItem('cv2011-id', config.courseId);
        sessionStorage.setItem('cv2011-token', config.token);
        sessionStorage.setItem('cv2011-instructor', config.instructor);
        await connect();
        toast(online ? 'Connected to the verifier.' : 'Connection unavailable. Records remain on this device.');
    };
    async function renderInsights() {
        const panel = $('insights-panel');
        let records: Attempt[] = attempts, scope = 'Records from this browser';
        if (online && config.instructor)
            try {
                const response = await api('/api/instructor/attempts', undefined, true);
                records = response.attempts;
                scope = 'Instructor view · all records from the connected course service';
            }
            catch (error) {
                toast(String(error));
            }
        const submissions = records.filter(attempt => attempt.event === 'submit');
        const checked = submissions.filter(attempt => ['correct', 'incorrect'].includes(attempt.result?.status || ''));
        const wrong = checked.filter(attempt => attempt.result?.status === 'incorrect');
        const categories: Record<string, number> = {};
        for (const attempt of wrong) {
            const category = attempt.result?.category || 'unclassified';
            categories[category] = (categories[category] || 0) + 1;
        }
        panel.innerHTML = `<div class="panel-label">LEARNING INSIGHTS</div><h2>${escape(scope)}</h2><p>Counts describe submitted concept answers and problem steps. Exploration edits are excluded. An error category describes the observed answer pattern and can require instructor interpretation.</p><div class="insights-cards"><div class="panel"><div class="insight-number">${submissions.length}</div><p>Submitted steps</p></div><div class="panel"><div class="insight-number">${checked.length ? Math.round(100 * (checked.length - wrong.length) / checked.length) + '%' : '—'}</div><p>Correct among checked submissions</p></div><div class="panel"><div class="insight-number">${new Set(records.map(a => a.courseId)).size}</div><p>Pseudonymous IDs</p></div></div><h2>Observed answer patterns</h2>${Object.keys(categories).length ? `<table class="data-table"><thead><tr><th>Pattern</th><th>Occurrences</th></tr></thead><tbody>${Object.entries(categories).map(([name, count]) => `<tr><td>${escape(name.replaceAll('_', ' '))}</td><td>${count}</td></tr>`).join('')}</tbody></table>` : '<p class="small">No checked incorrect submissions in this view.</p>'}<h2>Recent attempts</h2><div style="overflow:auto"><table class="data-table"><thead><tr><th>Course ID</th><th>Step</th><th>Answer</th><th>Result</th><th>Hints / revealed</th></tr></thead><tbody>${submissions.slice(-30).reverse().map(a => `<tr><td>${escape(a.courseId)}</td><td>${escape(a.step.replaceAll('_', ' '))}</td><td>${escape(a.answer)} ${escape(a.units)}</td><td>${escape(a.result?.status || 'unresolved')}</td><td>${a.hintUsed ? 'Hint' : ''} ${a.solutionRevealed ? 'Solution shown' : ''}</td></tr>`).join('')}</tbody></table></div><div class="dialog-buttons"><button id="refresh-insights">Refresh</button><button id="export-attempts">Export these records</button></div>`;
        $('export-attempts').onclick = () => download('cv2011-attempts.json', { exportedAt: new Date().toISOString(), scope, attempts: records });
        $('refresh-insights').onclick = () => void renderInsights();
        panel.insertAdjacentHTML('beforeend', '<button id="sync-attempts">Verify and upload queued attempts for my ID</button>');
        $('sync-attempts').onclick = async () => {
            if (!online) {
                toast('Connect your course verifier first.');
                return;
            }
            let count = 0;
            for (const attempt of attempts.filter(a => !a.synced && (a.courseId === config.courseId || a.courseId === 'local-unassigned'))) {
                try {
                    const response = await api('/api/attempts', { ...attempt, courseId: config.courseId, section: attempt.section ?? 0.5 });
                    attempt.courseId = config.courseId;
                    attempt.result = response.result;
                    attempt.synced = true;
                    count++;
                }
                catch (error) {
                    toast(String(error));
                    break;
                }
            }
            saveAttempts();
            toast(`${count} queued events verified and recorded.`);
            void renderInsights();
        };
    }

    return {
        get connected() { return online; },
        request: api,
        record,
        connect,
        updateStatus: updateSession,
        renderInsights,
    };
}
