# Actual finite-stage extension and boundary tests

## Frozen scope

`logs/cubical-stage-extension-sources.sha256` freezes these four sources:

- `CubicalSubdivision/StagePasting`
- `CubicalSubdivision/FaceBoundaryTopology`
- `CubicalSubdivision/OuterBoundary`
- `CubicalSubdivision/FaceCover`

All four final sources compile warning-free. The initial exhaustive
recursive-origin audit passed 72 declarations and 19 exact consumers with
only `propext`, `Classical.choice`, and `Quot.sound`.
`audits/CubicalStageExtensionAudit.lean` fixes that count; the final fixed-72 rerun also passed warning-free.
The clean final log is `logs/cubical-stage-extension-fixed72.log`. The later `BoundaryLifting` and local lifting
induction are outside this boundary.

## Finite-stage continuous extension

The strictly lower skeleton is empty at dimension zero and agrees with the
preceding closed skeleton thereafter. The actual lower skeleton and the
finite disjoint union of newly attached parameter cubes form a compact space.
Its original coordinate map onto the next Hausdorff skeleton is surjective,
hence an actual quotient map.

The preimage of the lower skeleton in each new face is exactly its entire
original boundary. Distinct new faces intersect only on their boundaries.
These facts prove that a given continuous lower-skeleton map and continuous
new-face maps agreeing on whole boundaries descend continuously. The result
retains both the lower-skeleton map and every original new-face map exactly.
No filler or lifting conclusion is assumed by this pasting theorem.

## Honest arbitrary-universe boundary tests

A face's finite active coordinate set is explicitly reindexed by an actual
equivalence with `Fin (faceDimension F)`. Both the parameter cube and its
entire boundary are then universe-lifted into an arbitrary `TopCat.{u}`.
The resulting homeomorphisms retain the literal coordinate formulas and
commute with the original boundary inclusion. The accepted canonical cube
boundary HEP theorem therefore proves HEP of that actual face-boundary
inclusion. Compactness is transported from the genuine compact boundary
presentation. No universe-zero restriction is imposed on future HLP/HELP
targets.

## The precise outer-boundary criterion

A label with a fixed coordinate at an actual outer endpoint gives an entire
face on the original outer cube boundary. Otherwise the preimage of the
outer boundary lies in the face's own whole parameter boundary. The source
states this exact dichotomy; it does not claim an additional union-of-outer-
faces identity or an unstated closure-under-face-operators theorem.

This dichotomy is enough to preserve an originally prescribed outer-boundary
map during the skeleton induction: whole outer faces use that map; on other
faces, every outer-boundary point is already in the prescribed attaching
boundary.

## One cover choice for all dimensions

Every canonical face is proved to lie in one actual full-dimensional grid
cell, uniformly over every parameter point. Thus the previously proved
single grid subordinate to a pulled-back open cover controls all faces in
all skeleton dimensions simultaneously. No separate incompatible grid choice
is made at each stage.

## Remaining scope

These theorems supply explicit geometry and continuous extension of already
compatible data. Local right lifting, weak double-cylinder/cartesian gluing,
and the connected-row global diagonal fiber theorem remain later proofs.
