# General finite-module support and quotient interfaces

`PrincipalClosedSupport` retains the actual restriction of scalars along
`R → R/(f)` and its equivalence onto the finite modules killed by `f`; its
abelian/exact constructions retain the noetherian hypothesis where used.
`IdealPowerFiltration` uses a commutative noetherian ring and the actual
submodule `I M` and quotient `M/I M`; an annihilating ideal power gives a finite
exact filtration by `I`-annihilated factors.

`SmallModelLocalization` retains the actual finite-module localization functor,
its chosen small-model transport, Serre kernel and quotient theorem, including
the uniform annihilator criterion for one represented finite module.
`PrincipalSupportSmallModel` supplies the actual principal support category,
scalar operator, killed predicate and its finite filtration.

`ClosedSupportSmallModel` retains the exact quotient-ring/support-subcategory
comparison on the same chosen small models. `ScalarRepresentation` retains the
annihilation/scalar correspondence through the stated fully faithful additive
finite-module representation. Original objects, namespaces, maps, hypotheses
and universe bounds are preserved. G/K groups and localization/devissage
K-equivalences remain downstream.

`PrimaryDecomposition` works over a commutative Dedekind domain. It identifies
the actual finite torsion-module category with the canonical finite-support
family of primary-module categories by an exact equivalence. Annihilator
factors bound support; the reconstruction uses actual primary-submodule
inclusions and summation. The self-coordinate inclusion is naturally the
identity and distinct-prime coordinates are naturally zero.

`PrimarySmallModel` restricts the original `equivSmallModel` to exactly the
native `smallTorsion R⁰` category. Its primary exact functor and primary
inclusions are single composites between matching small endpoints, retaining
the original represented-module squares. Explicit alternative SmallModel
equivalences refer to the same original categories; they do not identify
different-universe K-groups. Native K-assembly and residue dévissage remain
in `Quillen.GTheory.Dedekind`.

`ScalarMatrices` sends linear automorphisms to actual finite-module
isomorphisms. Its commutative-ring matrix action is the original ordinary
`g.val.mulVec`, used by the field matrix-transport comparison.

`PrincipalRankOne` retains the literal `Fin 1 → R` multiplication-to-principal-quotient
sequence and its categorical cokernel, together with the actual localization
comparison and scalar GL(Fin 1) action at the original localized coefficient.
These module and map comparisons hold for commutative rings; regularity supplies
monicity, while noetherianity gives the standard short-exact and conflation
statements. It uses the existing quotient restriction and finite-module
localization functors.

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalRankOne` | Literal principal rank-one quotient/cokernel and actual localization/scalar-GL comparisons; regularity gives monicity, Noetherianity gives short exactness and conflations |
