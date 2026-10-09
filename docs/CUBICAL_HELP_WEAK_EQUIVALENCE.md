# Cubical lifting and the original complete weak-equivalence property

## Checked source boundary

All three sources compile warning-free and are frozen. Ordered final source
rechecks and the recursive-origin audit passed all 65 declarations with only
`propext`, `Classical.choice` and `Quot.sound`; all 21 exact consumers passed
warning-free. The final fixed-65 rerun, including the combined `Quillen.Library`
import, completed successfully at 10:45:16 UTC on 2026-10-09. Independent
excluded-target source rebuilds and a fixed-65 audit with 24 strengthened
consumers also passed warning-free, with source and prerequisite hashes
unchanged. The boundary is:

- `Quillen/Topology/HELP/CubeBoundary.lean`
- `Quillen/Topology/HELP/CubicalLifting.lean`
- `Quillen/Topology/HELP/FiberwiseWeakEquivalence.lean`

The frozen manifest is `logs/cubical-help-sources.sha256`, fingerprint
`490e4357237238a0907983d5d5569c020e8e6aa466fc324f70fbd8fc4ffaf02b`.
Initial checks shared slot1; after its explicit release, final author checks
use slot2 with one Lean thread, preserving the global two-process cap. Frozen
prerequisites are unchanged. The one-pass recursive-origin and 21 exact
consumer audit is `audits/CubicalHELPAudit.lean`; evidence is recorded under
`logs/cubical-help-20261009/`.

## Genuine cube boundaries

`CubicalTests.cube n` is the actual finite product cube, universe-lifted by
`ULift` so it can be used in the common-universe HLP/HELP APIs. Its contraction
is coordinatewise multiplication by `1-t`. `stepHomeomorph` adds the first
coordinate by the actual `Fin.cons` map, with `Fin.tail` and coordinate zero
as inverse.

`BoundaryPresentation n` contains a compact space and an actual HEP map to
that cube, together with proofs that its image lies in and covers the entire
ordinary `Cube.boundary (Fin n)`. The zero-dimensional source is genuinely
empty. The successor presentation is the actual topological pushout
`CylinderBoundary`, postcomposed with `stepHomeomorph`. Its side cylinder
covers old boundary coordinates, and its two caps cover the new coordinate's
two endpoint faces. Compactness and HEP come from the accepted genuine
cylinder-boundary construction. The theorem `boundaryPresentation_range`
states the full image equality. No embedding or boundary-homeomorphism
assumption is substituted for this construction.

## Actual GenLoop quotients

`ContractedStrictHELP f` packages strict HELP on compact HEP pairs with an
explicit contraction of the test target. It is a lifting property, not a
homotopy-set conclusion. Full compact HELP implies this restricted property.

Surjectivity of the original `homotopyGroupMap` lifts each original target
`GenLoop (Fin n)` using constant source-boundary data. Coverage of the full
cube boundary makes the lifted map a source `GenLoop` at the original
basepoint. The obtained relative homotopy, precomposed with `ULift.up`, gives
the exact equality of the original quotient classes.

Injectivity starts with the actual relative homotopy between the images of
two original loop representatives. Its boundary data are the first loop on
one cap, the second on the other, and the constant basepoint on the side.
These glue by the genuine cylinder-boundary pushout universal property. A
strict lift on the compact contracted cylinder has the exact two endpoint
loops and constant value on every original boundary point. It therefore
supplies the required relative homotopy between the original source loops.
Only pointwise coverage of the boundary is used to check that assertion;
no continuous choice of boundary preimages is assumed.

Both arguments use the actual quotients in every finite degree, including
zero, and use no group operation in dimension zero. A separate empty-boundary
point test proves actual component surjectivity. Thus an empty source cannot
satisfy the resulting weak property with a nonempty target.

## Original total-map endpoint

`isWeakHomotopyEquivalence_of_fiberHELP` applies the previously accepted
contracted-test lifting theorem to maps `p : E → B`, `q : F → B`, `f : E → F`
with `q ∘ f = p`, genuine HLP for both projections, and full compact HELP for
every original strict-fiber map. The result is the complete weak-equivalence
property of the original continuous map `f`: component surjectivity and
bijectivity on every original finite homotopy-set map, including zero.

Neither total space is required to be a simplicial realization or to have a
CW model. All spaces use one arbitrary common universe; the actual homotopy
sets retain their original small `Fin n` cube parameters. The audit includes
the chosen-fiber application via individual joined base paths and the
accepted strict-fiber HELP transport.

This does not prove compact HELP from weak equivalence, nor does it establish
a weak-cartesian pushout/gluing theorem. Those statements have additional
proof obligations. The implementation uses no global continuous inverse
family over a path-space pullback.

## Frozen source hashes

- CubeBoundary: `6ec9c2f08de5082c0fa117abbf5d645f2d757653af0d5d03b79688f4c3b327de`
- CubicalLifting: `ed695771e38c28ecb4806edeaadb3640d23fa74ee7c038b59e168d455375b147`
- FiberwiseWeakEquivalence: `d6a27e597c6df89a7a23e12cd6009c5b4cb9d48c89383d409efd2077f905148f`

The declaration-origin counts are CubeBoundary 56, CubicalLifting 7, FiberwiseWeakEquivalence 2.
Every private/generated declaration in those origins is included. The audit
also tests literal successor pushout maps, contraction coordinates, the
whole boundary-image equality, every original finite homotopy-set map,
explicit degree zero, component surjectivity, empty-source consequences, and
the original chosen-fiber application through actual joined-path transport.

Scripts: `logs/check-cubical-help.sh`, `logs/check-cubical-help-slot2.sh`,
and `logs/audit-cubical-help.sh`.
