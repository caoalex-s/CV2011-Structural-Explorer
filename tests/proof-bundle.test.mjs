import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile, rm } from 'node:fs/promises';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { currentRealBeamReceipt, proofBundleHash } from '../scripts/proof-bundle.mjs';

test('real proof receipt changes for local imports and dependency lock changes', async () => {
    const folder = await mkdtemp(join(tmpdir(), 'proof-bundle-'));
    try {
        for (const name of ['RealBeamFields.lean', 'Imported.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
            await writeFile(join(folder, name), name);
        await mkdir(join(folder, 'sub'));
        await writeFile(join(folder, 'sub', 'Nested.lean'), 'nested theorem');
        const initial = await proofBundleHash(folder);
        const receipt = {status: 'checked', theoremSet: 'point-force-real-fields-v1', sourceSha256: initial};
        assert.equal(currentRealBeamReceipt(receipt, initial), true);
        await writeFile(join(folder, 'sub', 'Nested.lean'), 'changed nested theorem');
        assert.equal(currentRealBeamReceipt(receipt, await proofBundleHash(folder)), false);
        await writeFile(join(folder, 'sub', 'Nested.lean'), 'nested theorem');
        await writeFile(join(folder, 'Imported.lean'), 'changed theorem');
        assert.notEqual(await proofBundleHash(folder), initial);
        await writeFile(join(folder, 'Imported.lean'), 'Imported.lean');
        await writeFile(join(folder, 'lake-manifest.json'), 'changed dependency');
        assert.notEqual(await proofBundleHash(folder), initial);
        await rm(join(folder, 'lean-toolchain'));
        await assert.rejects(proofBundleHash(folder));
    } finally { await rm(folder, { recursive: true, force: true }); }
});
