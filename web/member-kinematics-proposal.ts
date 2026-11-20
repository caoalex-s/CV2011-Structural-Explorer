/** Prepare a cardinal drawing for the interval checker off the UI thread.
 * The Lean worker separately validates the resulting packet. */
import { proposeInclinedPacket } from './frame-interval-packet.js';
import { proposeInclinedReleasePacket } from './frame-inclined-release-packet.js';
import type { EvidenceQuery } from './model-evidence.js';
import type { Model } from './engine.js';

self.onmessage = ({ data }: MessageEvent<{ model: Model; query: EvidenceQuery; released: boolean }>) => {
    try {
        const propose = data.released ? proposeInclinedReleasePacket : proposeInclinedPacket;
        const packet = propose(data.model, data.query, 96).packet;
        self.postMessage(packet, { transfer: [packet.buffer] });
    } catch (error) { self.postMessage(String(error)); }
};
