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
    const member = model.members[0], load = model.loads[0];
    if (!member || !load || !Number.isFinite(member.EA + member.EI) || member.EA <= 0 ||
        ![load.end, load.mz, load.qEnd].every(Number.isFinite) ||
        model.nodes.some(node => !Number.isFinite(node.x + node.y)) ||
        model.supports.some(support => !Number.isFinite(support.angle))) return false;
    const solution = pointForceWorked(model, section);
    if (!solution || solution.L < 0.02 || Object.values(solution).some(value =>
        typeof value === 'number' && !Number.isFinite(value))) return false;
    return receipt?.status === 'checked' && receipt.theoremSet === 'point-force-real-fields-v1' &&
        /^[a-f0-9]{64}$/.test(receipt.sourceSha256 || '');
}
