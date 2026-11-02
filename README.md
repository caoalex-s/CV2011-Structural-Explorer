# CV2011 Structural Explorer

Structural Explorer lets students draw planar beams and rigid-jointed frames, place supports and loads, and inspect the response as the model changes. Its sandbox displays reactions, normal force, shear force, bending moment, and displacement. A separate problem workspace checks supported beam calculations and records submitted steps under pseudonymous course IDs.

## Run the local pilot

Use Node.js 24 or later and Python 3.12. The browser application has no runtime JavaScript dependencies. SymPy supplies the exact checker in the local service.

```powershell
python -m venv .venv
.venv/Scripts/python.exe -m pip install -r requirements.txt
node scripts/build.mjs
.venv/Scripts/python.exe -m server.app
```

Open <http://127.0.0.1:8765/>. The local service creates a demonstration account named `DEMO-001` and exposes its credentials only in loopback mode. The database and local credentials are saved in `.data/`, which is excluded from Git and the static build. Keep this directory when restarting the pilot to retain the records.

For a fresh checkout on Windows, `start-local.ps1` starts the configured local pilot in a hidden process and opens no extra console window. Its process ID and logs are written under `.data/`. `stop-local.ps1` stops only that recorded process after checking its command line.

## Use the drawing workspace

1. Choose **Blank canvas**, then **Open example**.
2. Select **Draw member** and click its start and end positions. A snapped endpoint on an existing member creates a rigid joint. Crossing members remain unconnected unless a joint is explicitly created.
3. Place pin, roller, or fixed supports on members. Select each support to edit its position and the roller reaction angle.
4. Place concentrated forces or couples. For a distributed load, click both boundaries on the same member. Select it to edit both intensity values.
5. Drag joints, supports, and loads in **Select / move** mode. Use numerical properties for precise values. Undo, redo, pan, zoom, model import, and model export are available.
6. Choose a response layer and move the section slider. The bending-moment display can be placed on the tension or compression side without changing its numerical sign.

The model uses metres, kilonewtons, and kilonewton metres. Global y is positive upwards and rotation is positive counterclockwise. Normal force is positive in tension. Bending moment is positive when the negative local-y side is in tension, with the local x-axis directed from the first member joint to the second.

## Supported analysis

The numerical engine uses linear-elastic, prismatic Euler–Bernoulli frame elements with axial deformation and small displacements. Supports and load boundaries subdivide members while preserving rotational continuity. Linearly varying distributed loads include their consistent nodal loads and polynomial displacement terms. Stability is checked from the rank of the restrained stiffness matrix before solving.

This release supports rigid joints, pins, inclined rollers, fixed supports, point forces, point couples, and vertical distributed loads. It does not yet include internal moment releases, ideal truss elements, shear deformation, buckling, plasticity, or large-displacement mechanisms. The mechanism display shows a linear free motion. Near-singular systems can be reported as unstable or poorly conditioned according to the numerical tolerance.

Section values are interpolated between 41 samples per analysis segment in the browser. The exact guided checker evaluates the requested position directly. Diagram peaks shown in the canvas are sampled peaks, and the displaced shape uses an explicitly displayed magnification.

## Guided solutions and verification

Guided checking covers a single horizontal beam drawn left to right, one pin, and one roller with a vertical reaction. Supports may lie inside the span. The checker handles multiple point forces, applied couples, and partial uniform or linearly varying distributed loads. It checks vertical reactions, section normal force, shear force, bending moment, and vertical displacement.

Computed diagrams and reactions are initially hidden in problem mode. Students can submit arithmetic expressions, request hints, reveal derivations, and reveal the computed response. The symbolic checker accepts exact equivalent arithmetic and compatible unit conversions. Rounded numerical submissions use a 0.1% tolerance with a small absolute floor. An unsupported expression is marked unresolved instead of being treated as an incorrect mathematical result.

The verification layers have distinct scopes:

| Layer | Scope |
| --- | --- |
| TypeScript tests | Numerical beam/frame benchmarks, constraints, sign conventions, and geometry changes |
| SymPy | Exact two-support beam reactions, section forces, and integrated displacements, including equilibrium and support conditions |
| Cross-language tests | Forty generated mixed-load beams compared between the independent TypeScript and SymPy formulations |
| Lean | Reaction-numerator equilibrium identities after clearing input denominators, and inversion of the plotting side |

Lean does not currently certify the drawing-to-model translation, floating-point solver, or displacement derivations. `proofs/StructuralProofs.lean` states the exact theorems and assumptions. The deployment workflow runs the pinned Lean toolchain and audits the reported axioms before marking the published proof metadata as checked. A local build can reuse the committed CI receipt only when its proof-source SHA-256 is unchanged.

## Learning records

The pilot records submissions, hints, solution reveals, model snapshots, section positions, units, selected diagram side, server verification results, and server timestamps. Sandbox edits are excluded. Tokens authenticate accounts independently of their pseudonymous course IDs. The instructor view aggregates verified submissions and shows the evidence behind broad answer patterns such as opposite signs or a factor of 1000. These patterns do not establish a unique misconception from a numerical answer alone.

When the verifier is unavailable, events remain in browser storage with unresolved status. **Learning insights → Verify and upload queued attempts for my ID** submits these records after a connection is established. Export is available for both model files and learning records. Published GitHub files contain application code and synthetic test cases; the private database remains local.

The agreed pilot uses a local verification and record service. GitHub Pages hosts the sandbox interface and local record queue. A Pages visitor needs a reachable verifier to receive server-verified grades and contribute to a shared class record. For the local pilot, use the local application URL to access the complete workflow.

## Development and deployment

```powershell
npm install --ignore-scripts
npm run check
npm test
.venv/Scripts/python.exe -m unittest discover -s tests -p 'test_*.py' -v
node scripts/build.mjs
```

Run `lake build --wfail` inside `proofs/` to check the formal library with the pinned toolchain. GitHub Actions runs the checks before publishing `dist/` to Pages. The build copies only files from `web/` and excludes server code, account credentials, and student records.

The optional Dockerfile packages the Python service and browser application for a later hosted pilot. Hosted mode requires `EXPLORER_INSTRUCTOR_TOKEN`, an explicit `EXPLORER_ORIGINS` allowlist, and persistent `EXPLORER_DATA` storage. Issue each course account with `python -m server.app --issue CV2011-0042` and distribute the returned token privately. Place a hosted service behind HTTPS and apply host-level request limits. No hosted student-record service is configured for this pilot.

## Next releases

- Internal hinges and ideal trusses, with mechanism examples and force-method explanations.
- A problem catalogue with stable problem versions and instructor-defined tasks.
- Equation-entry checking and section free-body diagrams, including alternative valid solution paths.
- Expanded Lean proofs and explicit links from each supported solution step to its checked rule.
- Cohort analysis of first attempts, later corrections, and hint use across problem versions.
