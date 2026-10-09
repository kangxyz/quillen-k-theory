# Independent review: finite cubical stage extension

## Frozen scope and current status

The four reviewed sources are exactly
`Topology/CubicalSubdivision/{StagePasting,FaceBoundaryTopology,OuterBoundary,
FaceCover}.lean`. Manifest `logs/cubical-stage-extension-sources.sha256` has
fingerprint `14bff4f49e0449913573d0a92c0fea9fd7332e1cc30bdacf7dbd9706869b11e9`.

**Accepted.** The complete semantic read, four fresh excluded-target source
rebuilds, and the fixed-72 origin audit with all 29 strengthened consumers
passed warning-free at 11:28:52 UTC on 2026-10-09. All source, dependency
and toolchain hashes matched before and after. The later `BoundaryLifting` source and
local or global lifting induction are outside this boundary. Production
sources are unchanged.

## Mathematical inspection

### The original finite-stage quotient

`skeletonBelow n m r` is the actual finite union of face images of dimension
strictly below r. It is compact and closed, empty for r=0, and equals the
previous ordinary skeleton at successor dimensions. A stage face has exactly
dimension r. Its preimage of the lower skeleton is exactly its entire
ordinary parameter boundary, including the empty boundary at r=0.

`StageSource` is the disjoint sum of that lower skeleton and the finite
family of original parameter cubes for the new stage faces. The projection
uses the literal subtype inclusion on the first summand and the original
face maps on the second. The source is compact; the target is the actual
Hausdorff skeleton subtype. Every face of dimension at most r is either
strictly lower or exactly at the new dimension, proving actual surjectivity.
The projection is consequently a genuine quotient map.

For continuous lower-skeleton data and continuous new-face data agreeing on
whole attaching boundaries, the proof checks every pair in a projection
fiber. Lower/lower agreement is literal equality; lower/face agreement uses
the full attaching-preimage identity; same-face agreement uses injectivity;
distinct equal-dimensional faces agree through both full boundaries. Thus
the chosen representative function descends continuously into an arbitrary
topological target. Its values on the entire lower skeleton and every new
face remain exactly the original specified maps. No continuous representative
choice is assumed, and the target needs no separation hypothesis.

The theorem requires already supplied compatible data. It does not assume
or conclude a local filler-existence principle under another name.

### Genuine arbitrary-universe face-boundary HEP

`Active F` is the original finite coordinate subtype. `activeEquivFin` gives
an actual finite equivalence, and `faceCubeHomeomorph` reindexes the original
parameters by its inverse, with the exact coordinate formula checked.
`FaceCube` adds only `ULift`; it lives in any common universe u.

The same bijection identifies the entire ordinary boundary, characterized
by an actual coordinate equal to zero or one. Restricting the two inverse
homeomorphisms gives the boundary homeomorphism. Compactness is obtained
from the accepted canonical compact boundary presentation. No new
compactness or boundary equivalence hypothesis is supplied by the caller.

`faceBoundaryInclusion` is literally subtype inclusion. Its factorization
through the actual cube-boundary inclusion retains the exact original map.
Composition of genuine homeomorphism HEP and the accepted boundary HEP
therefore proves HEP for this inclusion in arbitrary `TopCat.{u}`. The
unlifted boundary companion removes only `ULift`, without changing a
coordinate or its boundary proof. The consumer audit includes arbitrary-u
homotopy targets and equality with the entire prescribed boundary homotopy,
not merely its endpoint restrictions.

### Exact outer-boundary dichotomy

`OnOuterBoundary F` means that an actual fixed coordinate label is zero or
the terminal grid vertex. Such a face lies entirely on the original outer
cube boundary. Conversely an interior parameter point can lie there only
when the whole face has such an outer label: a moving coordinate reaching
an outer endpoint would force a parameter endpoint, contrary to interiority.

The exact checked conclusions are therefore a full preimage equal to the
universe for outer faces, and a preimage contained in the face's own whole
boundary for other faces. No stronger union-of-outer-face-images identity,
closure-under-face-operators theorem, or HEP for arbitrary closed subsets
is inferred. At n=0 there is no outer-face label, consistently with the
empty original outer boundary.

### One actual grid controls every face

`faceSet_subset_cellSet` chooses one full-dimensional grid cell per face,
uniformly over its entire parameter space. Moving coordinates use their
original interval; fixed coordinates use a cell containing the one fixed
grid vertex. Only pointwise preimages are chosen to prove the resulting
subset relation, without any continuous-choice claim.

The previously accepted whole-cell open-cover subordination then supplies
one grid size controlling every whole face in every dimension. The ambient
map and open-cover index set retain their independent universes and original
topologies. There is no incompatible per-dimension grid selection.

## Independent verification contract

The first-path overlay excludes all artifacts for the four reviewed targets.
Each original source is compiled to a fresh regular `.olean`. Import output
must resolve every target through the overlay. The source-only recursive
dependency closure contains 3,338 sources and 15,622 dependency artifacts;
these, the target sources and project/toolchain pins are rehashed around
both the fresh build and the audit. The mutable public umbrella is outside
that frozen prerequisite closure, while the combined `Quillen.Library`
import is present in the consumer audit to check integration collisions.

The fixed-72 audit includes every defining-origin declaration, including
private/generated declarations (StagePasting 27, FaceBoundaryTopology 36,
OuterBoundary 7, FaceCover 2), and recursively permits only `propext`,
`Classical.choice` and `Quot.sound`.

The 29 consumers check the literal sum/sigma stage source, both projection
summands, actual quotient/surjectivity, full attaching-preimage equality,
exact stage boundary map, empty initial skeleton and empty boundaries for
stage-zero faces, zero-stage pasting without a boundary constraint, all
original values of general stage pasting, arbitrary-universe compactness
and full HEP, both coordinate homeomorphisms, actual inclusion factorization,
outer-face and non-outer-face preimages including n=0, and uniform
whole-face cover subordination with independent target/index universes.

Audit: `audits/CubicalStageExtensionIndependentAudit.lean`.
Preparation: `logs/prepare-cubical-stage-extension-independent.py`.
Replay: `logs/verify-cubical-stage-extension-independent.sh`, with `build`
and then `audit` arguments.
Evidence: `logs/cubical-stage-extension-independent-20261009/`.

## Source hashes

- StagePasting: `fe1005ba228b2b64c4aa0f845468f6a2cf4cbd23aa0a523c1cc48aaba8cbba2e`
- FaceBoundaryTopology: `34940e82cbe06209bd249060f000b7263026f2dbeedf2e12502f2c4ff2e91360`
- OuterBoundary: `7c40e0a302fcfdf795ba6905ad6705513ef9ad12350cf662a96348a18b667ddb`
- FaceCover: `23f0c03e612c11275eb120ec37d3204ca0ce32c5f4e467282d73700e26e37160`

The initial consumer driver needed parentheses around a sum type and a
simp-at-hypothesis proof for the dependent empty-stage subtype. These were
consumer-only repairs; all frozen production sources were unchanged.

Terminal drivers: `logs/cubical-stage-extension-independent-build-driver.log`
and `logs/cubical-stage-extension-independent-audit-driver.log`.
Evidence manifest: `logs/cubical-stage-extension-independent-20261009/artifacts.sha256`.
