# Independent review: vertical mapping-path model and restriction

Accepted 2026-10-09 12:17:22 UTC.

## Frozen scope

- `Quillen/Topology/FiberwiseMappingPath/Basic.lean`
- `Quillen/Topology/FiberwiseMappingPath/Restriction.lean`

Author manifest: `logs/fiberwise-mapping-path-model-sources.sha256`.
The two complete sources were read. This review does not alter production sources
or their live artifacts. Subsequent boundary-lifting, locality and local-fiber
HELP sources are outside this review.

## Semantic assessment

`Space q f` is the actual subtype of `E × C(I,F)` consisting of an original
source point and an entire path starting at its image, with every path value
lying over the same displayed base point. Its topology is the induced topology
from the original source and compact-open path space. The source projection,
endpoint evaluation, and constant-path inclusion retain their literal coordinates.

The contraction sends a stored path `γ` to `s ↦ γ((1−t)s)`. It starts at the
identity and ends at the constant-path inclusion composed with the original
source projection. The proof checks joint continuity using the continuous
uncurrying criterion for the actual compact-open mapping space and the compact
interval. It fixes the source coordinate and every point of the constant-path
section throughout, and its path remains in the original displayed base fiber.
The homotopy equivalence uses exactly this section and source projection. The
identity `endpoint ∘ inclusion = f` is literal.

The contraction preserves the displayed base point. Its endpoint in `F` can
move along the stored path; no inverse over that endpoint is asserted or needed.
In later uses, weakness of the original map may follow from the actual displayed
factorization and the separately proved weakness of the endpoint map.

For an arbitrary subset `U` of the base, the restriction homeomorphism repacks
every original path value with its proof of membership over `U`. Verticality
transports membership at the endpoint to every time and to the original source.
The inverse only forgets these membership proofs. Both inverse identities and
continuity are proved on the whole stored paths, rather than path classes or
only the endpoints. The continuous-map endpoint square commutes exactly.
Neither openness, closedness, separation, local compactness of the original
spaces, nor a lifting property is an assumption. All three object universes
remain independent.

## Independent verification

The fresh first-path overlay excludes every target artifact family. Target
sources are rebuilt in order and actual fresh import paths are checked. One
constant traversal selects all **70 target origins (35 + 35)** with a fixed guard and recursively allows
only `propext`, `Classical.choice`, and `Quot.sound`.

All **29 independent consumers passed warning-free**. They retain all 15 author tests and add explicit source
coordinates, homotopy endpoints, original constant-path values, compatibility
of restriction with the literal section and scaling in both directions, the
inverse endpoint equation, and empty/full subset tests. All use independent
source, target and base universes.

Audit: `audits/FiberwiseMappingPathIndependentAudit.lean`.
Replay: `logs/verify-fiberwise-mapping-path-independent.sh`.
Evidence directory: `logs/fiberwise-mapping-path-independent-20261009/`.

All before/after hashes agree: the two frozen sources, **3,321 prerequisite
sources**, **15,542 dependency artifacts**, and toolchain/project pins. Both
fresh target artifacts are regular files and remain byte-identical across
the final fixed70 audit. The actual import log confirms fresh Basic and
Restriction resolution. No consumer repair or production change was needed.

The first all-origin run passed before the exact per-module counts were fixed.
The final guard replay passed with both counts checked, preserving the original
source-build log and checking source/artifact hashes again.

- Final audit log: `logs/fiberwise-mapping-path-independent-20261009/audit-fixed70.log`
- Terminal driver: `logs/fiberwise-mapping-path-independent-terminal-driver.log`
- Fixed replay: `logs/finalize-fiberwise-mapping-path-independent.sh`
- Evidence manifest: `logs/fiberwise-mapping-path-independent-20261009/artifacts.sha256`

This accepted boundary establishes the actual vertical path model, its section
homotopy equivalence and exact restriction homeomorphism. It makes no endpoint
lifting, local-to-global weakness or final Waldhausen fibration assertion.
