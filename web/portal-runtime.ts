/** Trusted worker lifecycle and current-input binding; no mathematical acceptance in JavaScript. */
export type CheckerResult = { state: string; id?: number; artifact?: string; inputDigest?: string;
    checked?: { numerator: string; denominator: string }[]; [key: string]: unknown };
export const sha256 = async (bytes: Uint8Array): Promise<string> =>
    [...new Uint8Array(await crypto.subtle.digest('SHA-256', new Uint8Array(bytes)))].map(byte => byte.toString(16).padStart(2, '0')).join('');

// Runtime diagnostic 1 measured 0.80–3.89 s for eight inclined worker fixtures.
// Allow slower devices a bounded margin; larger/expensive models can still time
// out inconclusively. Exact-cardinal requests retain their separate 1 s limit.
export const inclinedDeadlineMilliseconds = 30000;
// A partial load adds internal points to the checked stiffness system.
// This budget applies to its original-coordinate interval and diagram checks.
const partialLoadDeadlineMilliseconds = 150000;

export class PortalRuntime {
    private worker: Worker;
    private sequence = 0;
    private current: { id: number; inputDigest: string; cancelOnEdit: boolean;
        resolve: (result: CheckerResult) => void; timer: ReturnType<typeof setTimeout> } | null = null;
    private stopped = false;
    artifact = '';
    bundle = '';
    supportsFrames = false;
    supportsAffineFrames = false;
    supportsInclinedFrames = false;
    supportsHingeFrames = false;
    supportsSprings = false;
    supportsInclinedReleases = false;
    get needsReset(): boolean { return this.stopped; }
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
                    this.supportsAffineFrames = Array.isArray(data.capabilities) && data.capabilities.includes('affine-vertical-v1');
                    this.supportsInclinedFrames = Array.isArray(data.capabilities) && data.capabilities.includes('inclined-real-v1');
                    this.supportsSprings = Array.isArray(data.capabilities) && data.capabilities.includes('spring-rotation-v1');
                    this.supportsInclinedReleases = this.supportsSprings || Array.isArray(data.capabilities) && data.capabilities.includes('hinge-inclined-v1');
                    this.supportsHingeFrames = this.supportsInclinedReleases || Array.isArray(data.capabilities) && data.capabilities.includes('hinge-cardinal-v1');
                    resolve();
                } else this.receive(data);
            };
        });
    }
    invalidate(): void {
        this.sequence++;
        if (this.current) {
            clearTimeout(this.current.timer);
            // A worker cannot process a cancellation message while synchronous
            // Lean arithmetic runs. Termination makes an edit responsive.
            if (this.current.cancelOnEdit) { this.stopped = true; this.worker.terminate(); }
            this.current.resolve({ state: 'stale' }); this.current = null;
        }
    }
    receive(result: CheckerResult): boolean {
        const pending = this.current;
        if (!pending || !result || result.id !== pending.id || result.artifact !== this.artifact) return false;
        // Input guards run before hashing. Their digestless replies can end a
        // request only as failure, never supply checked values or acceptance.
        if (result.inputDigest === undefined) {
            if (!['inconclusive', 'limit', 'artifact-mismatch'].includes(result.state)) return false;
            clearTimeout(pending.timer);
            this.current = null;
            pending.resolve({ state: result.state, id: pending.id, artifact: this.artifact,
                message: typeof result.message === 'string' ? result.message : undefined });
            return true;
        }
        if (result.inputDigest !== pending.inputDigest) return false;
        clearTimeout(pending.timer); this.current = null; pending.resolve(result); return true;
    }
    async checkDiagram(bytes: Uint8Array, partialLoad = false): Promise<CheckerResult> {
        return this.submit(bytes, 'frame', true, false, partialLoad ? partialLoadDeadlineMilliseconds : undefined);
    }
    async check(bytes: Uint8Array): Promise<CheckerResult> {
        return this.submit(bytes, 'portal');
    }
    /** Source/query JSON is captured before hashing. Candidate construction
     * and exact checking both run inside the same bounded worker request.
     */
    async checkFrame(bytes: Uint8Array, mode: 'exact' | 'inclined' | 'partial' | 'hinge' = 'exact'): Promise<CheckerResult> {
        if (!this.supportsFrames || (mode === 'inclined' || mode === 'partial') && !this.supportsInclinedFrames ||
            mode === 'hinge' && !this.supportsHingeFrames) {
            this.invalidate(); return { state: 'unsupported-runtime' };
        }
        return this.submit(bytes, 'frame', mode !== 'exact', mode === 'inclined' || mode === 'partial', mode === 'partial' ? partialLoadDeadlineMilliseconds : undefined);
    }
    private async submit(bytes: Uint8Array, protocol: 'portal' | 'frame', inclined = false, intervalProposal = false, deadline?:number): Promise<CheckerResult> {
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
            }, deadline ?? (inclined ? inclinedDeadlineMilliseconds : 1000));
            this.current = { id, inputDigest, cancelOnEdit: inclined, resolve, timer };
            this.worker.postMessage({ id, artifact: this.artifact, bytes: captured, protocol, intervalProposal });
        });
    }
    dispose(): void { this.invalidate(); this.stopped = true; this.worker.terminate(); }
}
