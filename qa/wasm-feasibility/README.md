# Lean 4.19 browser runtime feasibility gate

This isolated CI experiment asks whether the pinned Lean rational checker can run in a browser after compilation to WebAssembly. `WasmSmoke.accepts a x` decides the exact rational equation `2*x = a`. The separate proof establishes the equation, `x = a/2`, and uniqueness for that same definition. This is a synthetic runtime test; it contains no portal model or structural-response certificate.

The build uses Lean 4.19.0 source and its native Linux compiler, Batteries from the existing dependency lock, Emscripten 3.1.44, and Lean's existing Emscripten/libuv build path. It regenerates the imported Lean modules as C, compiles the runtime and generated code, and repeats the build in a fresh directory. The only external source patch is the libuv patch already contained in the pinned Lean source. No additional runtime portability patch or version change is permitted by this gate.

Run the `Lean 4.19 WASM feasibility` GitHub workflow on the isolated branch. The job has a 40-minute ceiling. One corrected run is allowed for a routine proof/build/harness error; missing platform implementations or substantial runtime porting end the gate. Do not run this script or install these runtimes on Windows. Only public synthetic inputs are used, and no deployment is included.

## Interface and trust

The four newline-separated fields are the numerator and positive denominator of `a`, followed by those of candidate `x`. There is no final newline. Each integer has at most 128 decimal digits, with no leading zero, plus sign, negative zero, whitespace, NUL or non-ASCII byte. Fractions need not be reduced; Lean's `mkRat` normalizes them and represents zero as `0/1`. JavaScript transports bytes and never converts rational components to `Number`.

The exported `input_ptr` and `input_capacity` describe a module-owned 4096-byte input buffer. `checker_check(pointer, length)` rejects any other pointer and checks the length before reading memory. Its result is 0 for mathematical rejection, 1 for acceptance, 2 for malformed input, 3 for a resource limit, or 4 before initialization. The wrapper calls the generated export `smoke_check`, which is Lean's `WasmSmoke.checkStrings`; this constructs rational values and invokes `WasmSmoke.accepts`.

The theorem covers parsed rational values. It does not prove the C decoder, Lean's compiler, generated-code ABI, C/C++ compiler, runtime, browser, loader or request-binding code correct. These are separate trusted components. The test harness checks those boundaries on the actual artifact, including malformed inputs, large integers, altered witnesses, invalid pointers/lengths, stale results and a terminated worker. Such tests provide evidence for the tested cases, not a proof of the compilation chain or decoder.

## Evidence and limits

The workflow preserves the soundness/axiom log, generated C, source and artifact hashes, build commands and receipt. A pinned Playwright version supplies the actual headless Chromium test. After initialization, both the browser interception rule and the static harness server refuse further requests. The harness records startup, 100 steady-state compiled-call timings, payload sizes, initial memory, the 128 MiB memory ceiling, and a one-second per-request worker timeout. Startup includes navigation and artifact loading; check timings exclude messaging and hashing and may be limited by browser timer resolution.

The CI host image and package installer remain build-environment trust assumptions; their resolved versions are recorded. Lean's native Linux release has no published release-asset digest in its GitHub metadata, so its installed compiler digest is recorded rather than checked against a separately authenticated checksum. The pinned source, fixed compiler version, recorded compiler digest and byte comparison of repeated builds make this distinction inspectable. A successful browser test alone cannot establish portal equilibrium, stability, reaction signs, loaded recovery, or a fresh kernel proof for each edit.

Status is pending until the exact-commit CI receipt and independent review are available. A failed runtime build is a failed feasibility gate, even if its Lean proof passes. Unreached artifact/browser checks must remain explicitly untested.
