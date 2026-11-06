# Portal-frame pipeline trial

This trial carries the shipped **Portal frame** through the snapshot, exact adapter, and finite Lean model. The source is `example('frame')` in `web/engine.ts` at baseline `584d32e1d78fc6e2c7baf439e5c048170a687f21`. Its nodes, member order, supports, and distributed load are retained without modification.

The original nodes are A(0,0), B(0,4), C(6,4), and D(6,0), with coordinates in metres. Both bases are fixed, and the beam BC carries 5 kN/m downward over its full length. Every member has axial rigidity EA = 2 000 000 kN and flexural rigidity EI = 20 000 kN m². The member data are:

| Member | Direction | Length (m) | Local axis (cosine, sine) | Exact cuts |
| --- | --- | ---: | --- | --- |
| AB | A to B | 4 | (0, 1) | 0, 1 |
| BC | B to C | 6 | (1, 0) | 0, 1 |
| CD | C to D | 4 | (0, −1) | 0, 1 |

The fixed supports remain on AB at parameter 0 and CD at parameter 1. All six member ends are rigid, with the first incident member providing the joint reference. There are no point actions or interior cuts. The query asks for the sagging-positive bending moment M at the midpoint of BC and does not introduce another cut.

## What the instance checks

The generator invokes the shipped example directly, exports its original model, and passes it through the existing snapshot and adapter functions. `trace.json` records the original model, parser defaults, source-file digest, snapshot bindings, adapter digest, and generated Lean-source digest. Only validated numbers and bounded indices enter the Lean template. These bindings make the instance inspectable but do not prove the parser or emitter correct for arbitrary input.

| Check | Concrete statement or evidence |
| --- | --- |
| Finite topology | `structuralWitness`: one full interval per member, represented endpoints and supports, no interior slots or point actions |
| Geometry | `geometryWitness`: original incidence, orientation, segment endpoints, lengths, and inherited rigidities |
| Exact input contract | `portalContract`: uses `compose_exact_contract` with the actual finite and geometry witnesses |
| Joint and support laws | `referenceOrder`, `rigidEndLaws`, and `fixedSupportRows` |
| Distributed load | `portalLoadRestriction`, `portalLoadTotals`, and `portalLocalLoads`: the original source remains distributed, with resultant −30 kN and global moment −90 kN m about A |
| Load work | `portalConsistentWork`: the actual beam load and length enter the existing consistent-load virtual-work identity |
| Local field recovery | `portalLocalRecovery`: loaded segment fields exist for any supplied model coordinate vector, including the distributed-load particular field |
| Equilibrium interface | `portalConditionalReaction`: the existing equivalence between equilibrium and aggregate reactions is instantiated for this portal |
| Rejection checks | Recomputed artifacts reject changed CD orientation, load endpoints, and support location. Linux CI also rejects a false theorem that CD points upward. |

The generated file itself reports no successful Lean check. The focused Linux workflow writes `kernel-check.json` only after compiling the complete instance, auditing every named theorem against the standard axiom allowlist, and rejecting the false claim. That receipt records the exact commit and generated-source digest. The production snapshot and adapter retain their pending status.

## Numerical response and remaining bridge

The existing browser engine reports a stable response and equal upward reactions of approximately 15.000 kN at A and D. Horizontal reactions are approximately +4.208 kN at A and −4.208 kN at D. With counterclockwise moments positive, the base moments are approximately −5.595 kN m and +5.595 kN m respectively. At the midpoint of BC, the sagging-positive bending moment M is approximately 11.262 kN m and the vertical displacement is approximately −1.720 mm.

Numerical checks test global force and moment balance, fixed-base movements, and joint displacement and rotation continuity. The complete values and residuals are retained in `trace.json`. These observations are separate from the Lean instance checks: no particular global displacement vector, numerical reaction, or midpoint value is certified by this trial.

To certify those response values, a candidate displacement vector must be bound to the actual active model coordinates and checked against the fixed-support constraints and assembled equilibrium equations. A uniqueness claim also requires a portal-specific proof that no admissible mechanism exists. The present local recovery theorem accepts arbitrary end movements and therefore does not discharge these global obligations. General builder/compiler correctness, numerical engine equivalence, and error enclosures also remain outside this instance trial.

## Reproduce and inspect

Run the generator and focused JavaScript checks from the repository root:

```text
node scripts/portal-frame-pilot.mjs qa/local-portal-pilot
node --test tests/portal-frame-pilot.test.mjs
```

The output directory contains `portal-model.json`, `envelope.json`, `adapter.json`, `PortalFramePilot.lean`, and `trace.json`. Generation performs no Lean execution. The workflow **Check shipped portal pilot** checks the public example on Linux and retains these files together with its axiom log and receipt as the `public-portal-frame-pilot` artifact. This trial changes no production interface, verification badge, or deployment.
