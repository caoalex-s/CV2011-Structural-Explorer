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

## Later phases

1. Establish generic local six-degree-of-freedom element stiffness and consistent load relations, including axial and bending fields and endpoint force conventions.
2. Prove coordinate transformations and end-connection laws for rigid, released, and positive-stiffness spring directions. Keep ground restraints distinct from member-end compatibility.
3. Prove finite assembly, constraint handling, global force balance, solution existence and uniqueness, and a nonzero mechanism witness. Duplicate restraints require combined-reaction semantics.
4. Establish field recovery, physical displacement and rotation, and applicable course-method identities and real-domain bounds for the supported families. Distinguish exact extrema from certified enclosures.
5. Connect verified statements to versioned model semantics and strict applicability checks. Address arbitrary orientation, irrational lengths and trigonometric values with real or rigorously enclosed representations. A rational approximation alone cannot certify an arbitrary original drawing. Formal treatment of floating-point implementation and rounding requires its own refinement or error bounds.

The existing general lesson rules and exact worked-beam certificates retain their current scopes throughout these phases. Invalid, unstable, poorly conditioned, or unsupported models must not inherit a verified status. Linux CI uses synthetic models; student records and private models remain local.
