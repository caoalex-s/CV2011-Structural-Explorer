# Structural proof coverage and phases

The current application models planar, linear Euler–Bernoulli members with axial deformation. Member properties are constant on each prismatic member and displacements are small. Supports remain engaged and joint springs are linear. Buckling, plasticity, shear deformation, large displacements, truss elements, and unilateral contact are outside this model.

| Family or quantity | Existing checked scope | Remaining obligation |
| --- | --- | --- |
| Endpoint-supported beam with one vertical point force | Generic cleared-denominator equilibrium, section, jump, continuity, and conditional maximum-moment rules | Real elastic derivation and its relation to the displayed formulas |
| Horizontal pin–roller beam with mixed forces, couples, and partial uniform or linear vertical loads | Exact-rational certificates for individual supported model and section snapshots | Generic real fields, calculus, compatibility, method identities, and real-domain extrema |
| Cantilever and other beam supports | Numerical frame response | Generic boundary conditions, compatibility, and certified solutions |
| Frames with rigid, pinned, sliding, member-specific, or spring connections | Numerical frame response | Local member, transformation, connection, assembly, restraint, and recovery theorems |
| Reactions, N, V, M, axial and transverse displacement, rotation, connection actions and slips | Exact beam-instance algebra where stated above | Real frame recovery, equilibrium, and compatibility across all supported families |
| Stability and mechanisms | Floating-point rank and residual checks | Exact or rigorously enclosed stability, uniqueness, mechanism, and conditioning witnesses |

## Phase 1: real member fields

`RealBeamFields.lean` develops arbitrary-degree real polynomial fields and their relationship to real differentiation and integration. The point-force example uses downward-positive force, upward-positive displacement, and counterclockwise-positive slope. Its theorem statements and hypotheses determine its checked scope. The source remains unverified until the complete dependency-pinned Linux workflow passes; pending proofs are not exposed as checked in the application.

A polynomial field theorem does not establish that a drawing was translated correctly, that a system is stable, or that the TypeScript floating-point solver returned the mathematical solution. Assumed idealisation and boundary conditions must remain visible. Every numerical instance certificate remains tied to its exact source snapshot. Load-position changes can change the piecewise interval order and require the appropriate branch and a fresh instance certificate.

## Phase 1 theorem scope and receipt

The point-force solution predicate uses positive span and flexural rigidity with the load coordinate between the supports, including the endpoints. The signed force parameter is downward-positive. Its field obligations include reaction equilibrium, zero distributed intensity between actions, the shear jump, moment and displacement continuity, slope continuity, support conditions, and the Euler–Bernoulli curvature relation. The existence and uniqueness theorems concern these mathematical fields. The separate splice theorem establishes the displacement derivative on each side and at the join.

The cantilever predicate uses positive span and rigidity, a signed downward end force, a counterclockwise end couple, and a downward intensity that varies linearly over the full span. The associated moment, shear, slope, and displacement polynomials are subject to the free-end actions and fixed-end displacement and slope. The existence and uniqueness statements do not yet cover partial-load boundaries or arbitrary multi-member frames. Axial-field lemmas currently connect conditional polynomial balance and constitutive equations to real derivatives; a loaded axial solution is not yet established.

The real-polynomial derivative and interval-integral lemmas link formal polynomial operations to Mathlib's real calculus. The course-method identities and global real-domain extrema for arbitrary piecewise loads remain separate obligations. `RealBeamAudit.lean` enumerates each real-field theorem and CI rejects omitted reports and dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`. No project-specific axiom or admitted proof is permitted.

CI records a separate real-field status only after the proof build, regression fixtures, and axiom audit succeed. Its SHA-256 digest covers all local Lean sources, the Lean toolchain, the Lake configuration, and the dependency lock that pins Mathlib and its transitive imports. The static build clears a checked status when that bundle changes. The workspace applies the status only to the eligible point-force family and identifies it as a generic derivative and continuity result. It does not reuse a numerical instance certificate.

## Local frame segment in development

The local-element branch defines six end movements in the order (u₁, v₁, θ₁, u₂, v₂, θ₂). Its loaded axial and transverse fields include the particular solutions for affine local intensities. The corresponding end-action order is (Fx₁, Fy₁, C₁, Fx₂, Fy₂, C₂). On the retained left segment, (N, V, M) equals (−Fx₁, Fy₁, −C₁) at the left end and (Fx₂, −Fy₂, C₂) at the right end. These statements are not a certificate for an application model.

The current local proof obligations include endpoint kinematics, real-field balance and constitutive equations, consistent distributed-load and stiffness work integrals, stiffness symmetry and positive semidefiniteness, the rigid-motion kernel and rank, and uniqueness for prescribed end movements. Coordinate lemmas assume c²+s²=1. Spring stationarity includes the action applied directly to the selected member side. The free-direction relation is r=p_side, which does not in general imply r=0.

The numerical model stores distributed intensity in the global vertical direction. Its transformation into local components is qx=sq and qy=cq. A separate distributed global-horizontal intensity is not currently supported. Subdivision, action ownership, reference-member choices, arbitrary geometry, global assembly and restraints, stability, and floating-point execution remain separate proof obligations. No local or global frame verified badge is added by this branch. Linux CI must compile and audit the current sources before any theorem in this section is reported as checked.

## Later phases

1. Establish generic local six-degree-of-freedom element stiffness and consistent load relations, including axial and bending fields and endpoint force conventions.
2. Prove coordinate transformations and end-connection laws for rigid, released, and positive-stiffness spring directions. Keep ground restraints distinct from member-end compatibility.
3. Prove finite assembly, constraint handling, global force balance, solution existence and uniqueness, and a nonzero mechanism witness. Duplicate restraints require combined-reaction semantics.
4. Establish field recovery, physical displacement and rotation, and applicable course-method identities and real-domain bounds for the supported families. Distinguish exact extrema from certified enclosures.
5. Connect verified statements to versioned model semantics and strict applicability checks. Address arbitrary orientation, irrational lengths and trigonometric values with real or rigorously enclosed representations. A rational approximation alone cannot certify an arbitrary original drawing. Formal treatment of floating-point implementation and rounding requires its own refinement or error bounds.

The existing general lesson rules and exact worked-beam certificates retain their current scopes throughout these phases. Invalid, unstable, poorly conditioned, or unsupported models must not inherit a verified status. Linux CI uses synthetic models; student records and private models remain local.
