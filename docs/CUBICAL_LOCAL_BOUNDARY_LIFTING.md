# Genuine locality of actual cube-boundary lifting

## Checked scope

The four sources frozen by `logs/cubical-local-lifting-sources.sha256` are:

1. `Topology/CubicalSubdivision/BoundaryLifting`
2. `Topology/CubicalSubdivision/LocalLifting`
3. `Topology/CubicalSubdivision/FiberBoundaryLifting`
4. `Waldhausen/Fibration/RelativeRows/CubicalLifting`

All four compile warning-free in the ordered final source check
`logs/cubical-local-lifting-check3.log`. The fixed author audit `audits/CubicalLocalLiftingAudit.lean` passed all
15 defining-module origins recursively and all 12 original-map consumers,
including independent universes and degree zero, warning-free. The only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. The terminal log
is `logs/cubical-local-lifting-fixed15.log`; frozen source hashes match.
The earlier audit-only missing namespace was repaired without source changes,
and its initial evidence is retained separately.

## Exact theorem

`CubicalSubdivision.BoundaryLifting p` means strict right lifting against
every literal finite cube-boundary inclusion. A given continuous boundary
map `a` and cube map `b` with `p a = b` on the whole boundary have a continuous
cube extension `c` satisfying both `c|boundary = a` and `p c = b` exactly.
The original source and target may have independent universes.

`BoundaryLifting.of_open_cover` proves this property for the original `p`
from the property for its literal restrictions over an open target cover.
The hypotheses do not include any global filler, homotopy-fiber comparison,
or weak-equivalence conclusion.

## Actual relative face induction

For the specified test map a single finite affine grid is chosen subordinate
to the pulled-back cover, simultaneously for every face dimension. Induction
constructs a continuous exact lift on the strictly lower skeleton, retaining
the originally prescribed outer-boundary values.

At each stage an entire outer face uses the given original boundary map. A
remaining face is filled in its chosen chart. The lower-skeleton map already
lies in that chart on its whole attaching boundary, because its projection is
exactly the original test map. The actual face-boundary RLP gives an exact
filler. Every point of that face on the original outer boundary lies in its
own attaching boundary, so the prescribed values persist. The finite quotient
pasting theorem then gives the continuous next-stage map, retaining all data.

The zero-dimensional lower skeleton is genuinely empty; no nonempty source
is assumed. The argument ends at the actual whole cube. It never asserts HEP
for an arbitrary closed inverse-image subset and never chooses a continuous
family of weak inverses.

## Original fibration and row consumers

The generic adapter applies full compact HELP on all original strict-fiber
maps of two genuine HLP projections to the compact lifted cube and its actual
whole-boundary HEP pair. This proves literal boundary lifting for the actual
mapping-path endpoint. Its normalized strict-square specialization retains
the original full path coordinates.

The relative-row consumer derives every fiber premise from the genuine
nested-weak-equivalence structure `N`. It states cube-boundary lifting for
`MappingPath.endpoint (rowNormalizedComparison N α)`, using the unchanged
original normalized comparison. The category has the honest common universe
`C : Type u`, `Category.{u} C` already required by the row-realization model.

## Remaining global obligation

This is exact local RLP and an actual original-row input. It does not yet
prove weak-cartesian collar gluing or the connected-row global diagonal
homotopy-fiber theorem. In particular local HELP for a chart-restricted map
cannot silently be substituted for RLP of the restriction of its global
mapping-path endpoint: prescribed boundary paths of the latter may leave the
chart. The later collar construction must establish the requisite local
normalized lifts or controlled path transport with those paths retained.
