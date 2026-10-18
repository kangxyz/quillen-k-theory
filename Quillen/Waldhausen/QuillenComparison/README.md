# QuillenComparison interfaces

## Migration to 0.5.0

| Previous import | Current owner |
| --- | --- |
| `Quillen.Waldhausen.QuillenComparison.SpanNaturality` | `Quillen.CategoryTheory.QConstruction.SpanIsoNaturality` |

## Comparison with exact-category Q

For `E : Quillen.ExactStructure C`,
[`ofExactCategory E`](../ExactCategory.lean) uses inflations
and isomorphisms as its cofibrations and weak equivalences. Its axioms follow
from the exact structure. A `F : Quillen.ExactFunctor E E'` has `F.waldhausenExact`,
with pushout preservation derived from additive exactness.

[`QuillenComparison.Equivalence`](Equivalence.lean)
constructs `deloopingHomotopyEquiv E` to `E.KSpace`. Its based zigzag gives
`comparisonKEquiv E n : (ofExactCategory E).K n ≃* E.K n`, with the original
`comparisonK E n` forward, for every `n` and without an equivalence premise.
`comparisonKEquiv_exactFunctor_naturality` commutes with Waldhausen
`KMap F.waldhausenExact n` and exact-category `F.KMap n` in their common universes.
See [exact-category guide](../../../docs/topics/ExactCategories.md).
