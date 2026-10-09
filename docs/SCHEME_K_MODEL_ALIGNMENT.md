# Public scheme K and the actual vector-bundle / perfect-complex models

## Checked universes

For `X : AlgebraicGeometry.Scheme.{u}`:

- `SchemeSheaf.FiniteLocallyFree X : Type (u+1)` has `Category.{u}`.
- `PerfectComplexes.StrictPerfect X : Type (u+1)` has `Category.{u}`.
- `PerfectComplexes.Perfect X : Type (u+1)` has `Category.{u}`.
- `SchemeSheaf.SmallVectorBundle X : Type (u+1)` has `Category.{u+1}`.
- Both `(vectorBundleExactStructure X).QCategory` and
  `(smallVectorBundleExactStructure X).QCategory` have `Category.{u+1}`.
- Both corresponding KSpaces are `TopCat.{u+1}`.
- Public `Scheme.K X n`, actual vector-bundle exact S-K, `StrictK X n`,
  and `PerfectK X n` are all in `Type (u+1)`.

These assignments were verified by Lean, not inferred from documentation.
The raw Q morphism universe already contains `u+1` because its span
representatives contain an apex object. Consequently the small and original
Q-models have the same realization universe despite their original hom
universe difference.

## Proven bridge

Import `Quillen.Scheme.Comparison.SmallVectorBundleK`.

```
Quillen.SchemeSheaf.smallVectorBundleKEquiv
  (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
  Quillen.Scheme.K X n ≃*
    (Quillen.SchemeSheaf.vectorBundleExactStructure X).K n
```

The forward homomorphism is exactly `smallVectorBundleKMap X n`, as recorded
by `smallVectorBundleKEquiv_toMonoidHom`.

The exact functor is the existing
`ExactStructure.smallModelToOriginal.{u+1}`. Its induced Q-functor is already
proved to be a categorical equivalence. The new bridge zero-normalizes that
actual Q-functor, realizes its categorical equivalence, and applies the
existing based homotopy-group equivalence theorem. It uses no assumed Q/S,
Gillet–Waldhausen, or perfect-complex comparison equivalence.

## Generic support

`Quillen.KTheory.Map.CommonAmbient` works with
`C D : Type (max v₁ v₂)`, `Category.{v₁} C`, and `Category.{v₂} D`.
Their Q-categories have a common object/hom universe. It defines
`ExactFunctor.commonAmbientNormalizedQ`, `commonAmbientKMap`, and
`commonAmbientKEquiv` (the last under the genuine categorical hypothesis
`F.mapQ.IsEquivalence`). The common-universe map agrees definitionally with
the established `ExactFunctor.KMap` on the overlap of their parameter ranges;
this is checked by an independent consumer example in the audit.

No original public definition was changed. No identification of different-
universe realizations is asserted. A new Waldhausen small-model equivalence
is unnecessary for this alignment.

## How it fits the remaining comparison

A proved raw exact-category Q/S equivalence can be inverted and composed with
`smallVectorBundleKEquiv`, landing in the existing source of
`PerfectComplexes.vectorBundleSComparison` and
`PerfectComplexes.vectorBundleToPerfectSMap`. Those existing S-maps already
have source/target realization universe `u+1`.

This resolves the size/model mismatch. It does not by itself prove Q/S or
Gillet–Waldhausen, nor that the strict-to-local-perfect map is an equivalence.
No conditional substitute for those missing theorems is introduced here.

## Verification

The two new implementation modules compiled with Lean 4.34.0 without
warnings or errors, and have matching oleans. Source manifest:
`logs/small-vector-bundle-k-sources.sha256`.

`audits/SmallVectorBundleKModelAudit.lean` recursively audits every declaration
originating in both modules, including generated ones. All 34 declarations
passed, and the audit permits only
`propext`, `Classical.choice`, and `Quot.sound`. It also checks the exact
public endpoint, arbitrary-universe category/realization assignments, and
agreement of the new map with the established map where both apply.
The dedicated universe probe is `audits/probes/SchemeKUniverseProbe.lean`.

Logs: `logs/common-ambient-k-map.log`, `logs/small-vector-bundle-k.log`,
`logs/small-vector-bundle-k-audit.log`, and `logs/scheme-k-universe-probe.log`.
All checks use the shared slot-2 compiler lock. All 13 previously frozen
realization-source hashes were rechecked and remain unchanged.
