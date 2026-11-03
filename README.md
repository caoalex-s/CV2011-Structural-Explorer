# CV2011 Structural Explorer

[Open the GitHub Pages interface](https://caoalex-s.github.io/CV2011-Structural-Explorer/) · [Build and verification status](https://github.com/caoalex-s/CV2011-Structural-Explorer/actions)

Structural Explorer lets students draw planar beams and frames, place supports and loads, and inspect the response as the model changes. Its sandbox displays reactions, normal force, shear force, bending moment, and displacement. A separate problem workspace checks supported beam calculations and records submitted steps under pseudonymous course IDs.

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
3. Use **Add / edit joint** to insert a joint on a member. Select a joint to choose rigid continuity, a pin, a rotational spring, or member-specific constraints. Node labels follow the tutorial sequence A, B, C, …, Z, AA, … automatically. Inserting a joint places its label between the existing member ends. Model identifiers remain unchanged when the displayed labels update.
4. Place pin, roller, fixed, or guided supports on members. Select each support to edit its position and constraint direction. **Custom** support properties allow separate restraints of global x, global y, and rotation.
5. Place concentrated forces or couples. For a distributed load, click both boundaries on the same member. Select it to edit both intensity values. At a joint, **Attached member** identifies the member side receiving the load or ground restraint.
6. Drag joints, supports, and loads in **Select / move** mode. Use numerical properties for precise values. Undo, redo, pan, zoom, model import, and model export are available.
7. Choose a response layer and move the section slider. The bending-moment display can be placed on the tension or compression side without changing its numerical sign.

The model uses metres, kilonewtons, and kilonewton metres. Global y is positive upwards and rotation is positive counterclockwise. Normal force is positive in tension. Bending moment is positive when the negative local-y side is in tension, with the local x-axis directed from the first member joint to the second.

## Supported analysis

The numerical engine uses linear-elastic, prismatic Euler–Bernoulli frame elements with axial deformation and small displacements. Supports and load boundaries subdivide members while preserving rotational continuity. Linearly varying distributed loads include their consistent nodal loads and polynomial displacement terms. Stability is checked from the rank of the restrained stiffness matrix before solving.

This release supports rigid joints, internal hinges, finite connection springs, member-specific releases, inclined rollers, fixed supports, guided supports, point forces, point couples, and vertical distributed loads. Ideal truss elements, shear deformation, buckling, plasticity, and large-displacement mechanisms are outside its scope. The mechanism display shows a linear free motion. Near-singular systems can be reported as unstable or poorly conditioned according to the numerical tolerance.

Section values are interpolated between 41 samples per analysis segment in the browser. The exact guided checker evaluates the requested position directly. Diagram peaks shown in the canvas are sampled peaks, and the displaced shape uses an explicitly displayed magnification.

## Joint connections and course notation

The structural symbols follow the shared CV2011 `cv2011figures` library: navy members, teal applied actions, ochre reactions, hollow hinge circles, the triangular pin support, and the sliding-bearing form of the roller support. Node labels use italic capital letters. Force arrows remain collinear with their application points, including inclined and negative reactions. Applied and reaction moments use point-centred 270° arcs with tangential arrowheads. Moving a label or extending an arrow never changes its moment arm.

Internal connections and ground restraints are separate model objects. A pin support restrains two translations and leaves rotation free at the selected member side. It does not insert an internal hinge into a continuous beam. The new examples show an internal hinge, a semi-rigid connection, a continuous beam with a pinned branch, and an internal sliding joint.

| Internal connection | Relative movement and force transfer |
| --- | --- |
| Rigid | Axial translation, transverse translation, and rotation are continuous |
| Pinned | Translations are continuous; relative rotation is free |
| Semi-rigid | Translations are continuous; moment follows M = kθ Δθ |
| Member-specific | Each local axial, local transverse, and rotational direction can be continuous, released, or connected by a positive linear spring |

Connections relate member ends to the displayed **Reference member** at their common node. At a joint with more than two members, each non-reference end has its own connection to that reference. This permits a continuous main beam and a separately pinned branch. Changing the reference changes that connection arrangement and is a modelling choice. A free direction transfers no connection action, while a finite spring adds relative movement according to its stiffness. Translational stiffness is entered in kN/m and rotational stiffness in kN m/rad.

The end movements are represented explicitly and rigid directions are tied exactly. Spring energy is kδ²/2 in each independent relative direction. This uses the same mechanical interpretation as a [zero-length connection between coincident member ends](https://opensees.github.io/OpenSeesDocumentation/user/manual/model/elements/zeroLength.html). The implementation is a separate TypeScript formulation. Numerical tests check analytical spring deflections, hinge equilibrium, rotated local directions, mixed connections, and released mechanisms. These joint calculations remain outside the current SymPy and Lean proof scopes.

A spiral denotes a rotational spring, and a diamond identifies general member-specific constraints. These are labelled extensions to the inspected course library, which supplies no semi-rigid spring glyph. For a sliding joint, the circle and parallel rails indicate the released direction. The properties panel states the actual constraints for every member end. Coincident ground restraints have a unique combined reaction even when its division between duplicate restraints is not unique.

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

`proofs/StructuralProofs.lean` states the general reaction and plotting identities. The deployment workflow runs the pinned Lean toolchain and audits the reported axioms before marking that library as checked. A local build can reuse its committed CI receipt only when the proof-source SHA-256 is unchanged.

### Read the course-method derivation

Choose **Show worked solution** beneath the section readouts. The five method tabs cover section equilibrium, double integration, moment-area, virtual work, and superposition. Expressions use the current loads and coordinates, including partial linearly varying loads, concentrated couples, and overhangs. The view gives the full piecewise N/V/M functions, slope and vertical displacement functions, boundary and continuity conditions, and values at the selected cut. It refreshes after sandbox edits. Problem mode requires an explicit reveal and records that learning event.

The sequence follows the course beam-force lectures and Part 2 Lectures 2.2–2.6 and 2.9. These derivations cover a single prismatic horizontal beam with one pin and one vertical roller, up to 12 loads, and no internal joint releases or springs. Frames and other support arrangements retain their numerical sandbox response. Horizontal displacement and shear deformation are outside this worked-solution view.

`proofs/BeamCertificate.lean` defines exact rational polynomial operations. For each supported model, the service constructs a downloadable Lean certificate that independently reconstructs section equilibrium from the encoded point and distributed actions. It checks all polynomial coefficients, force and moment jumps, differential polynomial identities, support conditions, displacement and slope continuity, and the displayed moment-area and unit-load calculations. Superposition certifies the sum of the symbolic per-load contributions. It does not certify each contribution's derivation separately.

The certificate uses ordinary `decide`, and the service requires a successful compiler result for every generated theorem. Its axiom audit permits only Lean's standard propositional-extensionality axiom (`propext`) and rejects unproved claims (`sorryAx`) and compiler-trust axioms. Its scope is exact rational polynomial algebra. The physical idealisation, drawing translation, interpretation of formal polynomial differentiation and integration as real calculus, and floating-point canvas solver remain outside the certificate. A successful build of the general library alone does not mark a current worked solution as checked.

Local Lean execution is disabled by default. A security alert occurred when attempting to start the downloaded Windows compiler during development, and no antivirus exception was added. GitHub's Linux runner checks public synthetic examples and publishes receipts keyed by the SHA-256 of each complete certificate. A local pilot can use `proofs/worked-receipts.json` without executing Lean. Receipts cover the unchanged simply supported, distributed-load, and overhanging examples at quarter, midpoint, and three-quarter sections. A changed certificate is labelled **Symbolic result · Lean not checked** unless an explicitly configured compiler checks it. No student model is uploaded to GitHub by this workflow.

On a machine where Lean execution is approved, the service can use a pinned Lean 4.19.0 executable through `EXPLORER_LEAN`. The local pilot does not automatically discover or execute downloaded compilers. Installing a VS Code extension does not establish a successful proof check.

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

- Ideal trusses and guided solutions for compound beams and frames, with force-method explanations.
- A problem catalogue with stable problem versions and instructor-defined tasks.
- Equation-entry checking and section free-body diagrams, including alternative valid solution paths.
- Real-calculus formalisation and wider structural classes for the worked certificates.
- Cohort analysis of first attempts, later corrections, and hint use across problem versions.
