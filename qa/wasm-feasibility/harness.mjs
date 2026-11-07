// Test-only current-request binding and a one-second worker watchdog.
// These UI/loader checks are trusted code, separate from the Lean theorem.
const sha256 = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)))
    .map(byte => byte.toString(16).padStart(2, '0')).join('');

export class Checker {
    constructor() {
        this.revision = 0;
        this.current = null;
        this.state = { state: 'initializing' };
        this.worker = new Worker('/worker.mjs', { type: 'module' });
        this.ready = new Promise((resolve, reject) => {
            const timer = setTimeout(() => reject(new Error('Startup timeout')), 30000);
            this.worker.onerror = error => reject(new Error(error.message));
            this.worker.onmessage = ({ data }) => {
                if (data.ready) {
                    clearTimeout(timer);
                    this.artifact = data.artifact;
                    resolve(data);
                } else this.receive(data);
            };
        });
    }

    receive(result) {
        const pending = this.current;
        if (!pending || result.id !== pending.id || result.artifact !== this.artifact ||
            result.inputDigest !== pending.inputDigest) return false;
        clearTimeout(pending.timer);
        this.current = null;
        this.state = result;
        document.querySelector('output').textContent = JSON.stringify(result);
        pending.resolve(result);
        return true;
    }

    async check(value, options = {}) {
        const id = ++this.revision;
        // Invalidate before asynchronous hashing, including edit-then-revert.
        if (this.current) {
            clearTimeout(this.current.timer);
            this.current.resolve({ state: 'stale' });
            this.current = null;
        }
        this.state = { state: 'checking', id };
        document.querySelector('output').textContent = JSON.stringify(this.state);
        const bytes = value instanceof Uint8Array ? value : new TextEncoder().encode(value);
        const inputDigest = await sha256(bytes);
        if (id !== this.revision) return { state: 'stale' };
        return new Promise(resolve => {
            const timer = setTimeout(() => {
                this.worker.terminate();
                this.current = null;
                this.state = { state: 'timeout', id, artifact: this.artifact, inputDigest };
                document.querySelector('output').textContent = JSON.stringify(this.state);
                resolve(this.state);
            }, 1000);
            this.current = { id, inputDigest, resolve, timer };
            this.worker.postMessage({ ...options, id, artifact: this.artifact, bytes });
        });
    }
}
