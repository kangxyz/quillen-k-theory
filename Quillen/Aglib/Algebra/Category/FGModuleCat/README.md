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
identity and distinct-prime coordinates are naturally zero. Chosen small-model
transport and residue-field dévissage remain separate downstream steps.
