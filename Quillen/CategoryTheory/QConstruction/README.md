# The original Q-construction

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |

## Exact structure and the Q-category

Let `C : Type u` have `[Category.{v} C]`, `[Preadditive C]`, and
`[HasFiniteBiproducts C]`. An `E : CategoryTheory.ExactCategory.ExactStructure C` contains a predicate
`E.conflation` on `ShortComplex C`. Every selected short complex has the
actual kernel and cokernel universal properties. The other fields give
isomorphism closure, identity and composition for admissible maps, pushouts
along inflations, and pullbacks along deflations, with the corresponding
stability properties. The object and morphism universes may differ.

`E.inflation` and `E.deflation` select the first and second maps of these
conflations. `mono_of_inflation` and `epi_of_deflation` prove their ordinary
categorical mono and epi properties. Mixed base-change properties needed
below are derived from the exact axioms. An ambient abelian category or
existence of arbitrary pullbacks is not part of this input.

The restricted-span construction in
[`QConstruction.Basic`](Basic.lean)
represents an arrow from `X` to `Y` by a span `X ← M → Y`: the left leg is a
deflation and the right leg an inflation. `Quillen.Q` quotients such spans
by isomorphisms of the apex commuting with both legs.
`Q.mkHom_eq_iff_apexIso` records exactly this equality criterion.

Composition uses the genuine pullback of the right leg of the first span
and the left leg of the second. `Q.mkHom_comp` and `Q.comp_apex` retain that
representative and its apex. For an exact structure the required restricted
pullback instances are supplied by its axioms and their consequences;
arbitrary pairs of morphism properties do not automatically define an exact
category. The specialization is `E.QCategory`.

## Q-span naturality

[`SpanIsoNaturality`](SpanIsoNaturality.lean) exposes
`CategoryTheory.ExactCategory.ExactStructure.qSpan_iso_naturality`.
