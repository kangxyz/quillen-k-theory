# Finite admissible resolutions

## Resolving subcategories and actual finite resolutions

Let `C` be small, preadditive, and have finite biproducts, with exact structure
`E`. The resolution theorem takes a full subcategory defined by `P`, with
zero, isomorphism, finite-product, extension, and admissible-kernel closure.
The kernel condition `E.IsKernelClosed P` applies to a conflation
`A → B → D` when **both** `B` and `D` lie in `P`; it is weaker than closure
under every admissible subobject of a `P`-object. The exact structure is
`ExactSubcategory.exactStructure E P`.

[`ExactStructure.FiniteResolution`](Finite.lean) is an
actual finite tower. An object already in `P` gives a length-zero resolution.
A successor step resolves the terminal object of a conflation using a middle
object in `P` and a previously resolved kernel. Consequently
`E.ResolutionHypothesis P` is precisely
`∀ X, Nonempty (E.FiniteResolution P X)`. Length may depend on `X`; a
numerical projective-dimension assertion must first produce this tower.

`Resolution.classifyingHomotopyEquiv E P h` proves a homotopy equivalence with
the original Q-inclusion as forward map. The proof starts with length-one
comma contractions, proves resolving closure of the finite-length strata, and
uses their genuine filtered Q-nerve colimit. The canonically normalized
inclusion induces `Resolution.KEquiv E P h n`, whose forward homomorphism is
`Resolution.inclusionKMap E P n`.

The shorter interfaces retain the same closure assumptions and canonical map:

| Available resolution data | Comparison |
| --- | --- |
| `∀ X, E.ResolutionLength P 1 X` | `KEquivOfLengthOne E P h n` |
| A common `N : ℕ` and `∀ X, E.ResolutionLength P N X` | `KEquivOfBounded E P N h n` |
| Objectwise finite towers, without a common bound | `KEquiv E P h n` |

There is also a cover formulation in `Resolution.LengthOne`: actual
admissible epimorphisms from `P`-objects suffice under the stronger
`E.IsAdmissibleSubobjectClosed P` condition. It does not replace that condition
by the weaker kernel condition.
[`Consumer.Resolution`](../../examples/downstream/Consumer/Resolution.lean)
uses length-one and objectwise finite resolutions and checks the original
forward maps. For the geometric source of finite vector-bundle resolutions,
see [regular K-to-G comparison](../AlgebraicGeometry/Scheme/Regular/README.md#regular-k-to-g-comparison).
