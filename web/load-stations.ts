/** Magnetic stations use screen distance. Away from a target, retain the
 * projected binary64 coordinate, including on an oblique member. */
export const loadStations = [0, 1 / 8, 1 / 6, 1 / 4, 1 / 3, 3 / 8, 1 / 2, 5 / 8, 2 / 3, 3 / 4, 5 / 6, 7 / 8, 1];
const names = ['0', '1/8', '1/6', '1/4', '1/3', '3/8', '1/2', '5/8', '2/3', '3/4', '5/6', '7/8', '1'];
export function boundaryStation(t: number, spanPixels: number, enabled: boolean): number {
    const projected = Math.max(0, Math.min(1, t));
    const nearest = loadStations.reduce((best, value) => Math.abs(value - projected) < Math.abs(best - projected) ? value : best);
    return enabled && Math.abs(nearest - projected) <= Math.min(0.02, 7 / spanPixels) ? nearest : projected;
}
export function stationLabel(t: number): string {
    const index = loadStations.indexOf(t);
    return index < 0 ? String(Number(t.toPrecision(5))) : names[index];
}
