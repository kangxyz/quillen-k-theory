# Independent review: actual realization double-cylinder model

**Accepted, 2026-10-09 13:25:19 UTC.** Both fresh-source builds and the fixed40/all26-consumer audit passed warning-free on the first run.

## Frozen scope

- `Quillen/Topology/Realization/DoubleCylinder.lean`
- `Quillen/Topology/Realization/DoubleCylinderCompactGraph.lean`

Manifest: `logs/realization-double-cylinder-sources.sha256`.
Both sources and their actual cylinder/endpoint construction dependencies were
read completely. No production source or live artifact is changed. This
boundary is after the immutable 12:10 archive freeze.

## Semantic assessment

The simplicial model is the actual pushout of the two cylinder endpoints
`X ⨿ X → X ⊗ Δ[1]` along the original map `coprod.map f g`.
Its two displayed legs are the original categorical pushout inclusions.
Realization of the binary coproduct is identified with the ordinary topological
sum by the two genuine colimit cocones, with exact inclusion formulas.

The endpoint-pair square is proved separately on both coproduct summands.
It uses the accepted canonical interval-cylinder comparison and its exact zero
and one endpoint identities. The attaching-map square likewise retains the
original realized `f` and `g` on the two summands. Only the interval product
comparison is used, whose homeomorphism was proved using the locally compact
interval; there is no arbitrary-product realization claim.

Realization preserves the actual simplicial pushout. Transporting that
pushout square through the three proved coordinate isomorphisms gives the
literal ordinary topological double-cylinder square. Its canonical comparison
with any supplied displayed pushout is therefore an actual categorical
isomorphism and homeomorphism. The supplied hypothesis is the structural
pushout property, not a comparison equivalence or lifting conclusion.
The comparison's values on the original cylinder leg and both endpoint legs
are proved by the universal property; both whole-leg and pointwise formulas
are retained. No attaching map is required to be injective.

For a compact test into this unchanged displayed double cylinder, precompose
the entire test with the actual inverse homeomorphism. The accepted compact
closed-graph theorem for simplicial realizations then transports back by the
continuous product map and injectivity of that homeomorphism. Compactness
alone suffices for this graph statement; the parameter need not be Hausdorff
or locally compact. Matching against any continuous projection is a closed
preimage of this graph. Local compactness is required explicitly for the
subsequent quotient-product descent. The resulting pullback quotient retains
its original parameter and quotient-map coordinates exactly.

The three simplicial objects and displayed topological pushout have the same
universe `u`. The compact test, quotient source and matching projection source
have independent universes `v`, `z` and `w`; no raw cross-universe realization
isomorphism is asserted.

## Independent checking

The first-path overlay excludes every artifact family of both target modules.
It copies the independently accepted fresh quotient/compact-graph prerequisite
artifacts and verifies their hashes separately. Both sources are rebuilt in
order without any live build. Actual imported paths are checked.

The single defining-module traversal recursively audits fixed
**40 = 37 + 3** declarations, allowing only `propext`, `Classical.choice` and
`Quot.sound`. The **26 consumers** preserve all twelve author consumers and
add the actual simplicial pushout definition/square, both original endpoint
and attaching squares, genuine realized pushout, exact inverse cylinder/end
leg coordinates, attaching formulas at times zero and one, empty and
zero-dimensional compact parameters, every finite cube, a point test, and
continuous descent through the literal quotient pullback.

The frozen source hashes, **3,385 prerequisite sources**, **15,868 dependency artifacts**, toolchain/project pins, and copied accepted fresh quotient/graph artifacts were rechecked before and after the run. Actual fresh target import paths and regular artifact files were verified. No production or audit repairs were required, and no live artifact was changed.

Audit: `audits/RealizationDoubleCylinderIndependentAudit.lean`.
Replay: `logs/verify-realization-double-cylinder-independent.sh`.
Evidence: `logs/realization-double-cylinder-independent-20261009/`.

## Remaining scope

This supplies a genuine simplicial realization model for the displayed double
cylinder and the compact-test closed matching locus. It does not itself prove
compact homotopy lifting, variable-base collar gluing, arbitrary quotient
base-change stability, or the global Waldhausen fibration theorem. Those
constructions must separately retain their original boundary and base maps.
