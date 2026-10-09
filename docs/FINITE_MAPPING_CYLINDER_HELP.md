# Finite-parameter lifting and full vertical HELP for the actual mapping cylinder

Status: all nine implementation sources have compiled warning-free and are
frozen in `logs/compact-mapping-cylinder-lifting-sources.sha256` (manifest
SHA-256 `2344a59b9c96f156feb4547df919eb6893471a113a01259a2fdc359eb248a5bb`).
The final ordered nine-source replay and all-origin audit passed warning-free
at 2026-10-09 14:10:45 UTC: exactly 47 defining-module origins and all 13
original-map consumers, with only `propext`, `Classical.choice`, and `Quot.sound`.
The fixed-47 guard and all 13 consumers replayed warning-free at
2026-10-09 14:17:09 UTC. All nine source hashes and the accepted quotient3,
compact-correction5, and full-over-base3 prerequisite hashes still match.
Independent review is underway; its acceptance is not yet claimed.

## Checked source contract

Let `sq` be the displayed ordinary TopCat pushout of the endpoint-one
inclusion `A → A×I` and an original map `f : A → C`. Let `M` be its actual
pushout object, `r : M → C` its canonical collapse, `j : A → M` the literal
endpoint-zero map, and `base : C → T`. Write `π = r ≫ base`.

The first endpoint constructs `CompactHomotopyLiftingProperty π` from:

- genuine unrestricted `HomotopyLiftingProperty (f ≫ base)`;
- genuine unrestricted `HomotopyLiftingProperty base`;
- closed graphs of the actual compact locally compact test maps into `T`.

A genuine homeomorphism `T ≃ₜ |X|` for an actual simplicial realization
supplies the closed graphs by the separately accepted finite-support theorem.
A homotopy equivalence does not supply this hypothesis.

The output quantifies over compact locally compact parameter spaces in the
common universe. For each original initial map `a : D → M` and original base
homotopy `H : I×D → T`, it constructs a continuous `L : I×D → M` with
`L(0,d)=a(d)` and `π(L(t,d))=H(t,d)` literally. It does not assert unrestricted
HLP of `π` or a continuous lifting function on the entire path-start space.

The second endpoint additionally takes full compact HELP on every original
strict-fiber map of `f`. It proves full vertical HELP for the actual source
end `j`, on a displayed compact HEP pair `i : K → D` with compact locally
compact contracted target `D` and a duration whose zero locus is exactly
`range i`. Both the original boundary map and every intermediate point of
the prescribed boundary homotopy are retained. Its cubical specialization
is `source_endpoint_boundaryLifting_of_realizationModel`, for the literal
`FiberwiseMappingPath.endpoint π j`, including dimension zero.

## Construction

1. The accepted quotient3 boundary proves that a locally compact product of
   the actual pushout sum quotient remains quotient, and that restriction to
   the explicitly closed matching locus remains quotient. Compact maps into
   a realization have closed graphs by finite closed Hausdorff support.
2. `SumSubtype` and `CompactMappingCylinderParameters` give the original
   parameter-matched source/target sum its actual quotient topology.
3. The cylinder piece starts at height `s`. It follows a genuine source
   lift up to time `1−s`, with cylinder height `s+t`, then follows a genuine
   target lift of the shifted original base path. At the seam, the height is
   exactly one and target-lift time is exactly zero. At a glued starting cap,
   this is literally the target-side formula for all times.
4. The set-theoretic pushout relations prove constancy on every quotient
   fiber. Quotient descent after product with the locally compact interval
   constructs the actual continuous lift. The original initial point and
   complete projected homotopy are proved pointwise by quotient surjectivity.
5. The canonical collapse `r` is already an actual homotopy equivalence and
   hence has ordinary full compact HELP. The original `f` obtains its full
   vertical comparison from the accepted contracted-test theorem, using its
   two genuine HLP projections. It is not obtained by a weak-to-HELP assertion.
6. Full-boundary cancellation uses the actual pushout of the side cylinder
   and both caps. Ordinary strict HELP of `r` first lifts that boundary.
   Accepted compact base correction makes the lift base-exact while fixing
   the whole boundary, using duration `d(x)·t·(1−t)`. Its zero locus is proved
   equal to the original cylinder-boundary image, not merely to its endpoints.
7. The original source-end comparison therefore has exactly the prescribed
   side track and endpoint maps. Packing the whole vertical track gives the
   original vertical mapping-path endpoint RLP on every finite cube boundary.

All source/target/base spaces and the HLP parameter universes share the
explicit universe required by the existing genuine-HLP API. No Hausdorffness
of the whole mapping cylinder, no global source-end inverse, no arbitrary
product/pullback preservation, and no weak-equivalence-to-full-HELP conversion
is used. Genuine HLP of the two original projections is used on their possibly
noncompact lifting parameter spaces; only the new mapping-cylinder conclusion
is restricted to compact locally compact tests.

## Remaining scope

This is the finite bridge-end input. It does not by itself prove the open
attachment chart theorem, global weak-cartesian gluing, the two-sided-bar
fiber theorem, Waldhausen fibration, or the final scheme/perfect comparison.
The chart author must preserve the proved finite relative lifting interface
and distinguish actual compact HELP inputs from merely weak equivalences.

## Frozen source order

1. `Quillen/Topology/Maps/SumSubtype.lean`
2. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderParameters.lean`
3. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderTimes.lean`
4. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderLiftFormula.lean`
5. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderLiftDescent.lean`
6. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderLifting.lean`
7. `Quillen/Topology/HELP/CompactVerticalCancellation.lean`
8. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderVerticalHELP.lean`
9. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderBoundary.lean`

The separate quotient3 prerequisite is independently accepted in
`docs/REVIEW_20261009_COMPACT_PARAMETER_QUOTIENT.md`. Compact correction5 is
independently accepted in `docs/REVIEW_20261009_COMPACT_LIFTING_CORRECTIONS.md`.
The new nine-source audit is prepared as
`audits/CompactMappingCylinderLiftingAudit.lean`; it will scan all defining
origins recursively and check the exact original maps, empty/zero-dimensional
tests, full prescribed boundary and literal endpoint lifting.

## Author evidence

- Ordered rebuild and initial successful audit: `logs/compact-mapping-cylinder-lifting-initial-audit.log`.
- Frozen implementation hashes: `logs/compact-mapping-cylinder-lifting-sources.sha256`.
- Guarded recursive audit: `audits/CompactMappingCylinderLiftingAudit.lean` (fixed 47).
- Focused guard replay: `logs/compact-mapping-cylinder-lifting-fixed47.log` (terminal success).
- Evidence manifest: `logs/compact-mapping-cylinder-lifting-evidence.sha256`.
