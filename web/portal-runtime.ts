/** Trusted worker lifecycle and current-input binding; no mathematical acceptance in JavaScript. */
export type CheckerResult = { state: string; id?: number; artifact?: string; inputDigest?: string;
    checked?: { numerator: string; denominator: string }[]; [key: string]: unknown };
export const sha256 = async (bytes: Uint8Array): Promise<string> =>
    [...new Uint8Array(await crypto.subtle.digest('SHA-256', new Uint8Array(bytes)))].map(byte => byte.toString(16).padStart(2, '0')).join('');

export class PortalRuntime {
    private worker: Worker;
    private sequence = 0;
    private current: { id: number; inputDigest: string; resolve: (result: CheckerResult) => void; timer: ReturnType<typeof setTimeout> } | null = null;
    private stopped = false;
    artifact = '';
    bundle = '';
    supportsFrames = false;
    onFailure: (reason: string) => void = () => {};
    readonly ready: Promise<void>;

    constructor(url = new URL('./bundle/worker.mjs', location.href)) {
        this.worker = new Worker(url, { type: 'module' });
        this.ready = new Promise((resolve, reject) => {
            const timer = setTimeout(() => { this.dispose(); reject(new Error('Checker startup timeout')); }, 30000);
            this.worker.onerror = () => {
                clearTimeout(timer); this.dispose();
                this.onFailure('Checker worker failed. Reset to continue.');
                reject(new Error('Checker worker failed'));
            };
            this.worker.onmessage = ({ data }) => {
                if (data.ready) {
                    if (this.artifact) {
                        if (data.artifact !== this.artifact || data.bundle !== this.bundle) {
                            this.dispose(); this.onFailure('Checker identity changed. Reset to continue.');
                        }
                        return;
                    }
                    clearTimeout(timer);
                    if (data.isolated !== true || typeof data.artifact !== 'string' || typeof data.bundle !== 'string') {
                        this.dispose(); reject(new Error('Checker isolation or identity missing')); return;
                    }
                    this.artifact = data.artifact; this.bundle = data.bundle;
                    this.supportsFrames = Array.isArray(data.protocols) && data.protocols.includes('frame');
                    resolve();
                } else this.receive(data);
            };
        });
    }
    invalidate(): void {
        this.sequence++;
        if (this.current) { clearTimeout(this.current.timer); this.current.resolve({ state: 'stale' }); this.current = null; }
    }
    receive(result: CheckerResult): boolean {
        const pending = this.current;
        if (!pending || result.id !== pending.id || result.artifact !== this.artifact || result.inputDigest !== pending.inputDigest) return false;
        clearTimeout(pending.timer); this.current = null; pending.resolve(result); return true;
    }
    async check(bytes: Uint8Array): Promise<CheckerResult> {
        return this.submit(bytes, 'portal');
    }
    /** Source/query JSON is captured before hashing. Candidate construction
     * and exact checking both run inside the same bounded worker request.
     */
    async checkFrame(bytes: Uint8Array): Promise<CheckerResult> {
        if (!this.supportsFrames) { this.invalidate(); return { state: 'unsupported-runtime' }; }
        return this.submit(bytes, 'frame');
    }
    private async submit(bytes: Uint8Array, protocol: 'portal' | 'frame'): Promise<CheckerResult> {
        this.invalidate();
        const id = this.sequence;
        if (this.stopped) return { state: 'reset-required' };
        const captured = new Uint8Array(bytes);
        const inputDigest = await sha256(captured);
        if (id !== this.sequence) return { state: 'stale' };
        return new Promise(resolve => {
            const timer = setTimeout(() => {
                this.current = null; this.stopped = true; this.worker.terminate();
                this.onFailure('Checker timed out. Reset to continue.'); resolve({ state: 'timeout' });
            }, 1000);
            this.current = { id, inputDigest, resolve, timer };
            this.worker.postMessage({ id, artifact: this.artifact, bytes: captured, protocol });
        });
    }
    dispose(): void { this.invalidate(); this.stopped = true; this.worker.terminate(); }
}
