# Library guide

## Imports

Prefer individual modules when only one interface is needed. Selected public
entrypoints and generated whole-topic imports are also available.

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | K-groups, exact-functor maps, equivalences, and small models |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |
| `Quillen.Scheme` | Public geometric K/G interfaces |
| `Quillen.Resolution` | Admissible finite-resolution comparisons |
| `Quillen.PerfectComplexes.Basic` | Strict and locally-perfect connective models |
| `Quillen.Waldhausen.QuillenComparison.Equivalence` | The exact-category Q/S comparison |
| `Quillen.Library` | Selected public K/G interfaces |
| `Quillen` | Complete library |

Generated subject imports include `Quillen.Algebra`, `Quillen.CategoryTheory`,
`Quillen.Topology`, `Quillen.KTheory`, `Quillen.Devissage`, `Quillen.Localization`,
`Quillen.GTheory`, `Quillen.PerfectComplexes`, and `Quillen.Waldhausen`.

## Exact categories and K-groups

For an exact structure `E`, the main objects are:

- `E.QCategory`: the restricted-span Q-category.
- `E.KSpace` and `E.kBasepoint`: its classifying space and distinguished point.
- `E.K n`: its connective K-group in degree `n`.
- `E.SmallK n`: K-theory using the chosen small-model interface.

An exact functor `F : ExactFunctor E E'` induces `F.mapQ`, `F.KMap n`, and
`F.smallKMap n`. The API includes identity, composition, and natural-isomorphism
laws. For a composable functor `G`, `ExactFunctor.KMap_comp_apply` identifies
the composite pointwise:

```lean
(F.comp G).KMap n x = G.KMap n (F.KMap n x)
```

`SmallExactCategory.ofExactStructure E` bundles the input, and
`SmallExactCategory.KFunctor n` gives the corresponding group-valued functor.
These interfaces reuse the same K-groups and canonical maps.

## Localization and dévissage

`Quillen.Devissage` provides the finite-filtration hypothesis and the induced
K-equivalence for the stated abelian setting. The Serre localization namespace
provides `quotientKMap`, `connectingHom`, and `localizationSequence`, with
individual exactness statements and the connective K₀ tail.

These are maps of the specified inclusions and quotient functors. The exact
premises remain part of each theorem; consult [Scope.md](Scope.md) before using
them outside their stated categorical setting.

## Scheme interfaces and universes

For `X : AlgebraicGeometry.Scheme.{u}`, `Quillen.Scheme.K X n` uses finite
locally free sheaves, while `Quillen.Scheme.G X n` uses coherent sheaves under
the stated local noetherian hypotheses. These public types lie in `Type (u + 1)`.
The separately named affine interface `Quillen.Scheme.Affine.G R n` lies in
`Type u`; it should not be treated as a definitional alias of global scheme G.

`Quillen.Scheme.restrictK` and `restrictG` are induced by open restriction.
`Quillen.Scheme.KToG` is the canonical inclusion map. Relevant modules include:

- `Quillen.Scheme.OpenImmersionFunctor`: restriction functoriality and naturality.
- `Quillen.Scheme.Localization`: noetherian open localization.
- `Quillen.Scheme.ClosedGTheory`: closed-subscheme dévissage and pushforward.
- `Quillen.Scheme.Regular`: regular K→G comparison with explicit hypotheses.

The regular affine equivalence has no finite Krull-dimension bound. The
nonaffine equivalence retains quasi-compactness and the resolution property.
No arbitrary-scheme pullback functor is implied by the open-restriction API.

## Perfect complexes

`Quillen.PerfectComplexes.PerfectK X n` is the locally-perfect connective
S-theory interface. Restriction, support, strict-to-local, and vector-bundle
comparison maps are defined using the stated models and quasi-isomorphisms.

The comparison of split and ambient-monomorphism cofibrations is distinct from
Gillet–Waldhausen and the strict-to-local equivalence. The latter comparisons
remain open; the existence of their canonical maps does not assert equivalence.

## Examples and references

The [downstream package](../examples/downstream) contains client proofs for
exact-functor laws, localization, dévissage, regular comparisons, scheme
restriction, and Waldhausen interfaces. It uses a local path dependency with
its own manifest and build directory.

Mathematical references:

- [Quillen, Higher Algebraic K-theory I](https://link.springer.com/chapter/10.1007/BFb0067053).
- [Bühler, Exact Categories](https://arxiv.org/abs/0811.1480).
