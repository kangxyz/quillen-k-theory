# Finite-filtration dévissage

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |

## Abelian finite-filtration dévissage

Let `C` be small and abelian, and let `P : ObjectProperty C` contain zero and
be closed under subobjects, quotients, and finite products. Its full
subcategory has the inherited abelian exact structure
`Devissage.subcategoryExactStructure P`; `Devissage.exactInclusion P` is the
actual exact inclusion into `C`.

`Devissage.FiltrationHypothesis P` says that every object has an actual finite
admissible filtration starting at a zero object, with each successive quotient
in `P`. The inductive
[`ExactStructure.Filtration`](Filtration.lean) records the
short exact sequences and factors. There is no common length bound and no
extension-closure assumption on `P`.

Under this hypothesis, `Devissage.classifyingHomotopyEquiv P h` has the
realized Q-inclusion as its forward map. The proof identifies the inclusion
comma categories with layer posets, contracts them by intersections and
finite-filtration induction, and applies Theorem A. Contractibility and a
homotopy inverse are conclusions of this route, rather than filtration inputs.

Canonical zero-object rebasing gives `Devissage.KEquiv P h n` in every
nonnegative degree. Its coercion is exactly `Devissage.KMap P n`, as recorded
by `KEquiv_coe`; it is not an unspecified isomorphism between the same groups.
[`Consumer.Devissage`](../../examples/downstream/Consumer/Devissage.lean) uses
both the equivalence and this forward-map identity.
