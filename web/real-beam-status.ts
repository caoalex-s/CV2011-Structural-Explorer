/** Gate the real-field theorem label to its exact supported beam family. */
import type { Model } from './engine.js';
import { pointForceWorked } from './point-force-worked.js';

export interface RealBeamReceipt {
    status?: string;
    sourceSha256?: string;
    theoremSet?: string;
}

/** This checks generic-rule applicability, never an instance certificate. */
export function realPointForceApplies(model: Model, section: number, receipt: RealBeamReceipt | undefined): boolean {
    return receipt?.status === 'checked' && receipt.theoremSet === 'point-force-real-fields-v1' &&
        /^[a-f0-9]{64}$/.test(receipt.sourceSha256 || '') && pointForceWorked(model, section) !== null;
}
