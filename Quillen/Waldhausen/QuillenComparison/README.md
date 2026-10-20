# QuillenComparison interfaces


## Comparison with exact-category Q

For `E : CategoryTheory.ExactCategory.ExactStructure C`,
[`ofExactCategory E`](../ExactCategory.lean) uses inflations
and isomorphisms as its cofibrations and weak equivalences. Its axioms follow
from the exact structure. A `F : CategoryTheory.ExactCategory.ExactFunctor E E'` has `F.waldhausenExact`,
with pushout preservation derived from additive exactness.

[`QuillenComparison.Equivalence`](Equivalence.lean)
constructs `deloopingHomotopyEquiv E` to `E.KSpace`. Its based zigzag gives
`comparisonKEquiv E n : (ofExactCategory E).K n ≃* E.K n`, with the original
`comparisonK E n` forward, for every `n` and without an equivalence premise.
`comparisonKEquiv_exactFunctor_naturality` commutes with Waldhausen
`KMap F.waldhausenExact n` and exact-category `F.KMap n` in their common universes.
See [exact-category guide](../../KTheory/README.md).
