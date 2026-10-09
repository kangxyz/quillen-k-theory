# Canonical cube-boundary homeomorphism

## Checked scope

`Quillen/Topology/HELP/CubeBoundaryHomeomorph.lean` compiles warning-free and
is frozen. Its fixed-30 recursive declaration-origin audit and all 16 exact
consumers, including the combined public-library import, passed warning-free
at 11:00:06 UTC on 2026-10-09. Source and prerequisite hashes match before
and after the check. The accepted three-source cubical weak-equivalence
boundary is unchanged.

Source SHA256:
`21c514eb74da3f572f0eb837365f743826bc42915ba175b5dd6549d2766a32eb`.

Manifest: `logs/cube-boundary-homeomorph-sources.sha256`, SHA256
`66dc31e01f116b1058526f967d885cd2edc54449ebd74041fae4b94baa946be3`.

## Injectivity from actual pushout relations

`TheoremA.cylinderBoundaryMap_injective` assumes only injectivity of the
original map `i : A ⟶ B`. It concludes injectivity of its actual
`cylinderBoundaryMap i`; it needs neither HEP nor compactness or separation.

The proof uses the actual side/cap pushout's joint surjectivity. For two side
points, equality of their images determines both the time and the original
point by injectivity of `i`. For a side point and a cap point, equality forces
time zero or one and the precise original gluing relation identifies the
points. Equal-cap points agree by their original coordinates; points on
opposite caps cannot have equal images because zero and one are distinct.

Induction starts with the genuinely empty zero-dimensional presentation and
uses the original `stepHomeomorph` at each successor. This proves
`boundaryPresentation_injective` for the already defined canonical
presentation; the existing `BoundaryPresentation` structure is not changed.

## Homeomorphisms and exact original maps

`boundaryPresentationHomeomorph n` has target
`{z : cube n // z.down ∈ Cube.boundary (Fin n)}`. Its underlying forward map
is definitionally the original presentation map, restricted to the boundary.
Surjectivity is exactly the previously proved full-boundary coverage.
The source is compact, and the target is a subtype of a Hausdorff cube;
therefore this continuous bijection has continuous inverse.

The source need not be assumed Hausdorff. In fact
`boundaryPresentation_isClosedEmbedding` proves that the original map is a
closed embedding directly from its compactness, continuity and injectivity.

`boundaryPresentationHomeomorph_comp` is the exact factorization of the
original presentation map through the actual subtype inclusion.
`boundaryPresentationHomeomorph_inv_comp` gives the inverse factorization.
Composing the existing presentation HEP with that genuine inverse
homeomorphism proves `boundaryInclusion_hep` for the actual inclusion.

`boundaryULiftHomeomorph` removes only the universe lift, and
`boundaryPresentationUnliftedHomeomorph` identifies the same canonical source
with the literal boundary of `Fin n → unitInterval`. Its forward-coordinate
formula is definitionally the original map followed by `ULift.down`.
`unliftedBoundaryInclusion_hep` proves HEP of the literal small-universe
subtype inclusion. The lifted theorem works in every arbitrary common
universe, with arbitrary targets in that universe; the unlifted categorical
HEP theorem is in `TopCat.{0}`. The unlifted homeomorphism itself allows an
arbitrary universe for the canonical presentation source.

## Verification and limits

The audit `audits/CubeBoundaryHomeomorphAudit.lean` imports the public library
alongside this module, scans every declaration defined by this source,
including private/generated declarations, and recursively allows only
`propext`, `Classical.choice` and `Quot.sound`. Its consumers check both
original map factorizations, the raw coordinate formulas, genuine emptiness
of the zero boundary, arbitrary presentation-map descent through the actual
homeomorphism, and the entire prescribed boundary homotopy for both lifted
and unlifted inclusions.

Checks run with one Lean thread under slot1, with acquisition times recorded.
Evidence is under `logs/cube-boundary-homeomorph-20261009/`. Reproducible
scripts are `logs/check-cube-boundary-homeomorph.sh` and
`logs/audit-cube-boundary-homeomorph.sh`.

This supplies the actual whole-cube boundary inclusion needed for arbitrary
prescribed boundary data. It asserts no HEP for arbitrary closed subsets,
no finite cubical-wall gluing theorem, and no global weak-cartesian result.
Independent review is separate from this author's checks.
