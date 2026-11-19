/** Validate byte resources before making the owned request snapshot.
 * Shared buffers are excluded so the captured source cannot change mid-copy.
 * Call synchronously before hashing or any other asynchronous request work.
 */
export function captureCheckerBytes(value         , capacity        )             {
    if (!Number.isInteger(capacity) || capacity <= 0 || capacity > 1048576)
        throw Error('Malformed checker input capacity.');
    if (!(value instanceof Uint8Array) || !(value.buffer instanceof ArrayBuffer))
        throw Error('Malformed checker request bytes.');
    if (value.byteLength > capacity) throw Error('Limit: checker request exceeds input capacity.');
    return new Uint8Array(value);
}
