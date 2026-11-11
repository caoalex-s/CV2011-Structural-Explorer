# CV2011 Structural Explorer

[Open the GitHub Pages interface](https://caoalex-s.github.io/CV2011-Structural-Explorer/) · [Build and verification status](https://github.com/caoalex-s/CV2011-Structural-Explorer/actions)

Structural Explorer lets students draw planar beams and frames, place supports and loads, and inspect the response as the model changes. Its sandbox displays reactions, normal force, shear force, bending moment, and displacement. A separate problem workspace checks supported beam calculations and records submitted steps under pseudonymous course IDs.

## Run the local pilot

Use Node.js 24 or later and Python 3.12. KaTeX renders LaTeX equations in the browser. SymPy supplies the exact checker in the local service.

```powershell
python -m venv .venv
.venv/Scripts/python.exe -m pip install -r requirements.txt
pnpm install --frozen-lockfile --ignore-scripts
node scripts/build.mjs
.venv/Scripts/python.exe -m server.app
```

Open <http://127.0.0.1:8765/>. The local service creates a demonstration account named `DEMO-001` and exposes its credentials only in loopback mode. The database and local credentials are saved in `.data/`, which is excluded from Git and the static build. Keep this directory when restarting the pilot to retain the records.

For a fresh checkout on Windows, `start-local.ps1` starts the configured local pilot in a hidden process and opens no extra console window. Its process ID and logs are written under `.data/`. `stop-local.ps1` stops only that recorded process after checking its command line.

## Learn with an interactive unit

Open `learn/` from the workspace navigation. The first unit connects support
restraints, equilibrium, and internal-force diagrams for one simply supported
beam. Students make predictions, vary the load and span, read symbolic formulas
with numerical substitutions, and open a separate practice problem. The course
map follows the Week 1 roadmap and marks the remaining teaching units as planned.

The section activity keeps its controls beside the diagrams and includes a
changing retained free body with explicit equilibrium equations. Diagram scales
remain constant by default, with automatic fitting available for small responses.
Phones show the whole span with readable section values and optional enlargement.

Astro builds the static lesson pages. The existing TypeScript workspace and
solver retain their interfaces. `src/pages/learn/` holds the content, while
`web/lesson-beam.ts` defines the bounded teaching example. Both interfaces use
the course SVG symbols and shared typography. Use pnpm 11.25.0 with the committed
lockfile. A local build uses `/` as its base. GitHub Actions sets
`EXPLORER_BASE=/CV2011-Structural-Explorer/` for Pages. The combined build creates
both the lesson routes and workspace in `dist/`.

Only submitted concept choices and solution reveals enter the record. Versioned
questions in `src/data/questions.json` supply the browser feedback and server
answer key. The authenticated server overrides client grade claims and records
the observed choice category. These are course concept checks, not Lean proofs.
Disconnected submissions remain queued for explicit upload through Learning
insights. Each lesson starting example uses its own model storage key and resumes
saved edits after a refresh. **Restart lesson example** restores that example
through the undo history. The main saved sandbox remains separate.
Print view expands the derivations without recording those automatic
expansions as student reveals.

The lesson links each short derivation to its generic Lean theorem scope. The
library includes section equilibrium, the shear jump, agreement of moment
branches at the load, finite-increment identities, and the attained maximum
moment for the single point-force beam. These statements use integer
representations after clearing decimal denominators. The physical idealisation,
input conversion, real-calculus interpretation, and browser rendering remain
outside the proofs. Live substitutions do not create new instance certificates.
The course source files remain unchanged. Local Lean execution remains disabled.

## Use the drawing workspace

1. Choose **Blank canvas**, then **Open example**.
2. Select **Draw member** and click its start and end positions. A snapped endpoint on an existing member creates a rigid joint. Crossing members remain unconnected unless a joint is explicitly created.
3. Use **Add / edit joint** to insert a joint on a member. Select a joint to choose rigid continuity, a pin, a rotational spring, or member-specific constraints. Node labels follow the tutorial sequence A, B, C, …, Z, AA, … automatically. Inserting a joint places its label between the existing member ends. Model identifiers remain unchanged when the displayed labels update.
4. Place pin, roller, fixed, or guided supports on members. Select each support to edit its position and constraint direction. **Custom** support properties allow separate restraints of global x, global y, and rotation.
5. Place concentrated forces or couples. For a distributed load, click both boundaries on the same member. Select it to edit both intensity values. At a joint, **Attached member** identifies the member side receiving the load or ground restraint.
6. Drag joints, supports, and loads in **Select / move** mode. Use numerical properties for precise values. Undo, redo, pan, zoom, model import, and model export are available.
7. Choose a response layer and move the section slider. The bending-moment display can be placed on the tension or compression side without changing its numerical sign.

The model uses metres, kilonewtons, and kilonewton metres. Global y is positive upwards and rotation is positive counterclockwise. Normal force is positive in tension. Bending moment is positive when the negative local-y side is in tension, with the local x-axis directed from the first member joint to the second.

### Course terminology and conventions

The **Course terminology, definitions, and conventions** panel follows the current Week 2 and Week 4 lectures and Tutorials 2, 5, 8–10, and 12. The plotting selector distinguishes **Tension side** from **Compression side**. Both use the same sagging-positive bending moment. Course references and the reviewed source locations are recorded in `qa/course-alignment-review.json`.

The method of sections uses downward-positive distributed intensity `w`, with `dV/dx = -w` and `dM/dx = V`, as in Tutorial 5. The load editor displays downward-positive start and end intensities. Model files and the numerical solver retain upward-positive global force components, and the editor converts the sign at its boundary. Existing model files and attempt records retain their meaning. Tutorial 9 uses an upward-positive signed load in its load-equation formulation; the course panel explains that contextual difference.

Double integration uses the tutorial's flexural rigidity `EI`, upward-positive elastic curve `v(x)`, and counterclockwise-positive physical slope `theta = dv/dx`. Each interval introduces two constants in `EI*theta` and `EI*v`, numbered `C1, C2, ...`. The moment-area view distinguishes tangent deviation from absolute displacement. The virtual-work view follows Tutorial 12: `m = bar(M)/bar(P)` is the normalised virtual moment with length units, and a downward virtual force selects `Delta = -v`. Reaction symbols follow the drawing's node labels, with `R1`, `R2`, ... identifying unlabelled interior supports.

The stability classification concerns free motion in the small-displacement model. A sufficient reaction count alone does not establish stability. The degree of static indeterminacy follows the planar component count `r - 3n` only for a stable assembly with independent equilibrium equations. Ideal roller contacts are assumed engaged; unilateral contact and buckling are outside the solver.

## Supported analysis

### Checked portal workspace

The **Checked portal** entry opens the same drawing workspace at `portal-checker/`. Select **Enable local checking** to load the compiled checker and activate isolation for this subpath. Activation preserves the model and section selection through one reload, while **Disable local checking** removes only this checker's registration and returns to the main workspace.

The supported model is the original A–B–C–D portal with both bases fixed and one uniform vertical load on BC. Its signed amplitude is upward-positive and is interpreted as the exact binary64 value stored by the editor. After each supported edit, the checker verifies all 12 joint displacement components, six grouped base reactions, and the BC midpoint bending moment and vertical displacement. The panel rounds its displayed values from the accepted exact rationals, which remain available in the certificate. Other diagram values retain their numerical interpretation.

`PortalChecker.lean` implements the rational acceptance predicate. `PortalSoundness.lean` connects its stiffness, loading, constraints, grouped reactions, and loaded midpoint recovery to the actual portal model and proves stability and unique equilibrium. The browser uses the compiled predicate without running the Lean kernel on each edit. Its compiler, runtime, bounded decoder, and current-input binding remain part of the trust boundary.

The ABI accepts 21 rationals with at most 128 decimal digits per integer field. A worker watchdog bounds each check to one second. Unsupported mechanical or section edits, resource limits, worker failures, and stale requests clear the certificate. The dedicated workspace keeps its model separate from the main sandbox and requires no per-edit network request or verifier service.

The `live-portal.yml` workflow audits every named bridge theorem and tests the installed bundle against its source hashes before exercising the actual browser checker. Its explicit `build_wasm` input additionally builds the structural artifact twice through the pinned Lean 4.19/C/Emscripten chain and compares every recorded build layer. The manifest identifies the compilation source commit, proof and ABI hashes, stability witness, and exact asset bytes. Local checks do not execute Lean or WASM.

### Numerical model

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

Applied forces, couples, and distributed loads carry distinct labels beside their magnitudes. Default labels are `P_1`, `M_0`, and `w_1`, with additional indices for further actions. Select an action to edit its **Load label**. Labels persist in saved models and remain separate from physical force components and application points. A varying distributed load identifies both endpoint intensities. Renaming a load updates its notation throughout a published solution without changing the numerical certificate.

Guided checking covers a single horizontal beam drawn left to right, one pin, and one roller with a vertical reaction. Supports may lie inside the span. The checker handles multiple point forces, applied couples, and partial uniform or linearly varying distributed loads. It checks vertical reactions, section normal force, shear force, bending moment, and vertical displacement.

Computed diagrams and reactions are initially hidden in problem mode. Students can submit arithmetic expressions, request hints, reveal derivations, and reveal the computed response. The symbolic checker accepts exact equivalent arithmetic and compatible unit conversions. Rounded numerical submissions use a 0.1% tolerance with a small absolute floor. An unsupported expression is marked unresolved instead of being treated as an incorrect mathematical result.

The verification layers have distinct scopes:

| Layer | Scope |
| --- | --- |
| TypeScript tests | Numerical beam/frame benchmarks, constraints, sign conventions, and geometry changes |
| SymPy | Exact two-support beam reactions, section forces, and integrated displacements, including equilibrium and support conditions |
| Cross-language tests | Forty generated mixed-load beams compared between the independent TypeScript and SymPy formulations |
| Lean general library | Reaction-numerator equilibrium identities after clearing input denominators, and inversion of the plotting side |
| Lean worked certificates | Exact polynomial section equilibrium, N/V/M equations, displacement conditions, and moment-area/unit-load calculations for the certified model and section |

`proofs/StructuralProofs.lean` states the general reaction and plotting identities and the parameterized point-force beam theorems described above. The deployment workflow runs the pinned Lean toolchain, audits the reported axioms, and rejects deliberately incorrect lesson claims before publication. A local build can reuse its committed CI receipt only when the proof-source SHA-256 is unchanged.

### Read the course-method derivation

The derivations retain the load symbols, beam length L, and flexural rigidity EI before substituting current values. Relative support and load positions are expressed as fractions of L, defining the family of geometrically similar beams represented by the drawing. Symbolic displacement and rotation use metres and radians, with conversion to millimetres and milliradians shown in the numerical step. Single-axis force and couple symbols denote magnitudes in their drawn directions. Inclined forces use signed Cartesian components, and distributed intensity remains downward-positive. The parameter list records the meaning and current value of every symbol.

SymPy checks the parametric equilibrium, polynomial differential relations, support conditions, and continuity. Every displayed symbolic expression is also checked against its numerical counterpart after substitution. Lean certificates continue to check the current numerical model and selected section. They do not establish a universally quantified theorem for all load amplitudes, lengths, and stiffnesses. Numerical extrema remain specific to the current parameters because changing load amplitudes can change the governing section.

The worked solution opens with short calculations for maximum bending moment, physical rotation, and vertical displacement. Each calculation shows the symbolic response, selection of the governing point, and explicit numerical substitution with units. Rounded readouts use approximate equality; exact fractions remain in the details. **Values at the selected section** provides the same substitution format for N, V, M, rotation, and displacement. **All point values, signed extrema, and proof details** contains the complete table and range enclosures. **Full course-method derivations** retains the longer explanations and interval calculations.

The workspace shows fixed global axes, local axes that follow the selected member, and the positive cut actions on the right face of the retained start portion. Changing the tension/compression plotting side preserves these axes and signs.

Stationary points follow the course relations: V=0 for bending moment, M=0 for physical slope, and theta=0 for displacement. Endpoints and jumps are compared as well. Exact rational extrema are displayed as fractions. Irrational positions use symbolic roots when short expressions are available and otherwise use rational isolating intervals. Approximate extrema carry explicit rational enclosures.

The generated Lean source adds exact point evaluations, interval-coverage statements, Bernstein polynomial basis conversions, and coefficient inequalities for every covered interval. These bounds are independent of canvas samples and of the completeness of the stationary-root search. The global real-domain interpretation uses the Bernstein convex-hull theorem, which is not yet formalised in Lean here. Isolation of irrational stationary roots also remains symbolic. This distinction is shown in the derivation and proof scope. Existing limits to one horizontal beam with a pin and vertical roller remain in force.

Choose **Show worked solution** beneath the section readouts. The method tabs cover the method of sections, double integration, moment-area theorems, principle of virtual work, and method of superposition. Expressions use the current loads and coordinates, including partial linearly varying loads, concentrated couples, and overhangs. The view gives the full piecewise N/V/M functions, physical slope and elastic curve, boundary and continuity conditions, and values at the selected cut. It refreshes after sandbox edits. Problem mode requires an explicit reveal and records that learning event.

On GitHub Pages, the unchanged **Simply supported beam**, **Distributed load**, and **Overhanging beam** examples include published worked solutions at quarter, midpoint, and three-quarter sections. These derivations and downloadable certificates are checked in GitHub CI before publication and remain available without a verifier connection. The panel offers the checked sections and clears the published result after any model edit. For an edited beam, open the local workspace linked in the panel and transfer the drawing with **Save model** and **Open model**. Checking student answers and recording verified attempts still require the service.

Equations are generated as LaTeX and rendered with a pinned, locally bundled KaTeX renderer and fonts. Fractions, subscripts, integral limits, aligned equations, and units use the same rendering path in all five methods. The renderer also supplies MathML for assistive technology. No external rendering service or CDN is needed.

The sequence follows the course beam-force lectures and Part 2 Lectures 2.2–2.6 and 2.9. These derivations cover a single prismatic horizontal beam with one pin and one vertical roller, up to 12 loads, and no internal joint releases or springs. Frames and other support arrangements retain their numerical sandbox response. Horizontal displacement and shear deformation are outside this worked-solution view.

`proofs/BeamCertificate.lean` defines exact rational polynomial operations. For each supported model, the service constructs a downloadable Lean certificate that independently reconstructs section equilibrium from the encoded point and distributed actions. It checks all polynomial coefficients, the downward-positive load conversion, interval integration constants, force and moment jumps, differential polynomial identities, support conditions, displacement and slope continuity, and the displayed moment-area and unit-load calculations. Virtual work checks the downward displacement against the negative of the upward-positive elastic curve. Superposition certifies the sum of the symbolic per-load contributions. It does not certify each contribution's derivation separately.

The certificate uses ordinary `decide`, and the service requires a successful compiler result for every generated theorem. Its axiom audit permits only Lean's standard propositional-extensionality axiom (`propext`) and rejects unproved claims (`sorryAx`) and compiler-trust axioms. Its scope is exact rational polynomial algebra. The physical idealisation, drawing translation, interpretation of formal polynomial differentiation and integration as real calculus, and floating-point canvas solver remain outside the certificate. A successful build of the general library alone does not mark a current worked solution as checked.

Local Lean execution is disabled by default. GitHub's Linux runner checks public synthetic examples and publishes receipts keyed by the SHA-256 of each complete certificate. A local pilot can use `proofs/worked-receipts.json` without executing Lean. Receipts cover the unchanged simply supported, distributed-load, and overhanging examples at quarter, midpoint, and three-quarter sections. A changed certificate is labelled **Symbolic result · Lean not checked** unless an explicitly configured compiler checks it. No student model is uploaded to GitHub by this workflow.

On a machine where Lean execution is approved, the service can use a pinned Lean 4.19.0 executable through `EXPLORER_LEAN`. The local pilot does not automatically discover or execute downloaded compilers. Installing a VS Code extension does not establish a successful proof check.

Under **Model, signs, and verification scope**, choose **Download VS Code proof project**. Extract the ZIP and open its folder in VS Code with the official Lean 4 extension. The project includes the exact generated source, its SHA-256 and status at export, and a `lean-toolchain` file pinned to 4.19.0. It contains no compiler binaries. Opening the Lean file starts the extension's compiler-backed checking, so use an installation approved for the machine. A later check in VS Code does not automatically update the pilot's recorded verification status.

## Learning records

The pilot records submissions, hints, solution reveals, model snapshots, section positions, units, selected diagram side, server verification results, and server timestamps. Sandbox edits are excluded. Tokens authenticate accounts independently of their pseudonymous course IDs. The instructor view aggregates verified submissions and shows the evidence behind broad answer patterns such as opposite signs or a factor of 1000. These patterns do not establish a unique misconception from a numerical answer alone.

When the verifier is unavailable, events remain in browser storage with unresolved status. **Learning insights → Verify and upload queued attempts for my ID** submits these records after a connection is established. Export is available for both model files and learning records. Published GitHub files contain application code and synthetic test cases; the private database remains local.

Learning insights separates first recorded submissions with no recorded aid,
retries, submissions after recorded aid, and all submissions. Percentages and
error categories use the selected group. Related lesson reveals and prior
prediction feedback remain identifiable after reload from saved events. These
flags describe recorded tool usage and do not establish independent mastery.

The agreed pilot uses a local verification and record service. GitHub Pages hosts the sandbox interface and local record queue. A Pages visitor needs a reachable verifier to receive server-verified grades and contribute to a shared class record. For the local pilot, use the local application URL to access the complete workflow.

## Development and deployment

```powershell
npm install --ignore-scripts
npm run check
npm test
.venv/Scripts/python.exe -m unittest discover -s tests -p 'test_*.py' -v
node scripts/build.mjs
```

If npm is unavailable but Node and Python are installed, `python scripts/install_math_renderer.py` installs only the pinned renderer after checking the npm archive's SHA-512 integrity, without running package scripts. Then run `node scripts/build.mjs`.

To preview the published examples without a service, run `python -m scripts.check_worked_examples` before building. With local Lean execution disabled, this command requires an existing exact-source receipt for every example. CI runs the same command with the pinned compiler and publishes the generated `worked-examples.json` with the static application. Generated files contain only the three maintained synthetic examples and are excluded from source control.

Run `lake build --wfail` inside `proofs/` to check the formal library with the pinned toolchain. GitHub Actions runs the checks before publishing `dist/` to Pages. The build copies browser sources and the bundled renderer, fonts, and licence into `dist/`; server code, account credentials, and student records are excluded.

The optional Dockerfile packages the Python service and browser application for a later hosted pilot. Hosted mode requires `EXPLORER_INSTRUCTOR_TOKEN`, an explicit `EXPLORER_ORIGINS` allowlist, and persistent `EXPLORER_DATA` storage. Issue each course account with `python -m server.app --issue CV2011-0042` and distribute the returned token privately. Place a hosted service behind HTTPS and apply host-level request limits. No hosted student-record service is configured for this pilot.

## Next releases

- Ideal trusses and guided solutions for compound beams and frames, with force-method explanations.
- A problem catalogue with stable problem versions and instructor-defined tasks.
- Equation-entry checking and section free-body diagrams, including alternative valid solution paths.
- Real-calculus formalisation and wider structural classes for the worked certificates.
- Cohort analysis of first attempts, later corrections, and hint use across problem versions.
