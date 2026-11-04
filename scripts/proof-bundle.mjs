/** Hash local Lean sources and the pinned dependency graph for a CI receipt. */
import { createHash } from 'node:crypto';
import { readdir, readFile } from 'node:fs/promises';
import { join } from 'node:path';

async function leanSources(directory, relative = '') {
    const result = [];
    for (const entry of await readdir(join(directory, relative), { withFileTypes: true })) {
        if (entry.name === '.lake') continue;
        const name = relative ? `${relative}/${entry.name}` : entry.name;
        if (entry.isDirectory()) result.push(...await leanSources(directory, name));
        else if (entry.isFile() && entry.name.endsWith('.lean')) result.push(name);
    }
    return result;
}

export async function proofBundleHash(directory = 'proofs') {
    const sources = await leanSources(directory);
    if (!sources.includes('RealBeamFields.lean')) throw Error('Real beam proof source is missing.');
    const files = [...sources, 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'].sort();
    const hash = createHash('sha256');
    for (const name of files) {
        const content = await readFile(join(directory, name));
        // Length-prefix names and contents so file boundaries are unambiguous.
        hash.update(`${Buffer.byteLength(name)}:${name}:${content.length}:`);
        hash.update(content);
    }
    return hash.digest('hex');
}

/** Reject stale, incomplete, or differently scoped checked receipts. */
export function currentRealBeamReceipt(receipt, expectedHash) {
    return receipt?.status === 'checked' && receipt.theoremSet === 'point-force-real-fields-v1' &&
        /^[a-f0-9]{64}$/.test(receipt.sourceSha256 || '') && receipt.sourceSha256 === expectedHash;
}
