# DVR localization and unit-pair generation

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.GTheory.DVR.SplitResidue` | Original generic finite-module G map injective in all degrees for a DVR whose actual residue map has a ring section |

## DVR tame kernel and split residue

The provided Aglib `MilnorK.K2.Residue` and `MilnorK.K2.DVR.Basic` supply
the actual DVR tame map with ordered convention `∂{u,π}=ū` and
`∂{π,u}=ū⁻¹`; Aglib also supplies the compatible uniform residue.
The additional candidate
[`DVR.TameKernel`](../../Aglib/KTheory/MilnorK/K2/DVR/TameKernel.lean) proves
`ker_tame_eq_unitSymbolSpan` for every actual DVR `R` and fraction field `K`:
the Milnor tame kernel is the integer span of symbols of two units of `R`.
Its uniform-residue kernel is the comap of this span along the supplied
`MilnorK.twoEquiv`.
This is an algebraic Milnor theorem; Quillen products and unit generation
require their own comparisons.

[`MilnorDvrBoundary`](../../KTheory/LowDegreeScalarAction/MilnorDvrBoundary.lean)
supplies those comparisons for the actual localization of a Dedekind domain at
a height-one prime. Its lower Milnor map is the original upper map followed
by canonical same-category universe lowering. The original local boundary,
canonical residue promotion, and original field determinant equal Aglib's tame
map on every Milnor class. Both the canonical and any supplied fraction field
are covered, with no residue-section hypothesis. The resulting ordered values
are `∂{u,π}=ū` and `∂{π,u}=ū⁻¹`.

[`GTheory.DVR.SplitResidue`](SplitResidue.lean)
proves `localizationKMap_injective_of_residueSection` for the original
generic finite-module G map in every degree when the actual residue map
has a ring section. The native test realizes this for `PowerSeries ℚ`.

[`UnitPairGeneration`](UnitPairGeneration.lean)
proves `unitPairSpan_eq_top_of_residueSection` for the original lower G2 of the
actual local ring. The premise is a genuine ring section of its original
residue map; generic injectivity is derived from that section. No Matsumoto
injectivity or generic-G1 premise is required. The separate client constructs
the coefficient section at the affine-line origin over every field, with
Q/F2/F3 specializations. Projective K2 transport uses a separate actual K/G
comparison; nonsplit-DVR generation is not asserted.

[`SpecUnitPairs`](../../KTheory/LowDegreeScalarAction/SpecUnitPairs.lean)
constructs genuine scalar/positive-cube unit pairs in original scheme K2.
Their KToG/affine images are the same lower DVR products. For the actual
Dedekind localization with a residue ring section, native
`Scheme.KToGPIDEquiv` reflects generation to `Scheme.K (Spec A) 2`.
The proof uses the literal rank-one tilde sheaf and its positive automorphism
cube, rather than defining pairs by an arbitrary inverse equivalence.

[`SpecUnitPairNaturality`](../../KTheory/LowDegreeScalarAction/SpecUnitPairNaturality.lean)
computes the original generic and closed K-pullbacks of these pairs. Under
target-only KToG/affine transport, their values are the lower Milnor symbols
of the mapped ordered units; for field targets, the actual scheme pairs also
agree. The residue case uses exact vector-bundle K-pullback and an ordinary
sections/tensor isomorphism, with no nonflat coherent G-pullback.

## Current normalization and generation boundary

`UnitPairGeneration` and the original scheme `SpecUnitPairs` comparison give
lower G2 and original `Scheme.K (Spec A) 2` unit-pair generation for the actual
Dedekind localization **with a ring section of its original residue map**.
The section supplies generic injectivity; no generic-G1 arithmetic premise is
substituted. This does not assert nonsplit-DVR generation.

The [scalar-action normalization](../../KTheory/LowDegreeScalarAction/README.md#same-negative-inverse-and-dvr-boundaries)
now applies the same negative inverse to every original characteristic-zero
fraction-field class. Raw determinant is `tame(-N)` and inverse raw determinant
is `tame(N)`, with no residue section or residue-characteristic-zero premise.
Original generic/closed scheme K-pullbacks and target-only K-to-lower-G transport
have negative mapped-symbol values; applying `N` to the closed residue field
requires its explicit characteristic-zero hypothesis. These statements preserve
the original maps and do not identify an arbitrary DVR Milnor presentation.
