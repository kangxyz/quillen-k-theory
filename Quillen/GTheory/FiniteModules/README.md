# Finite-module G-theory and localization

## Imports

| Import | Interface |
| --- | --- |
| `Aglib.Algebra.Category.ModuleCat.Finite` | Native finite-module category |
| `Quillen.GTheory.FiniteModules.PrincipalObjectBoundary` | Positive original Serre self-conflation boundary and literal principal rank-one quotient calibration over Noetherian commutative rings at regular elements, including zero cokernels and units |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |


## Finite-module G-localization and closed support

Let `R : Type u` be commutative and noetherian and `S : Submonoid R`.
`FiniteModuleLocalization.G R n` is
`(CoherentScheme.finiteModuleExactStructure.{u,u} R).SmallK n`, in `Type u`.
`SupportedG S n` uses the genuine Serre kernel on the small model: represented
finite modules whose scalar localization is zero. The localization functor,
its Serre-localization property, and its small-model transport are proved.

`localizationKMap S n` is exactly the original scalar-localization
`smallKMap`. `smallAbelianKEquiv` and `smallKMap_comparison` identify it with
the abelian small-model Serre map, including zero normalization.
`localization_longExact S` therefore gives the preceding connective sequence
with `SupportedG S`, `G R`, and `G (Localization S)` and the terminal G₀
surjection. The hypotheses allow arbitrary `S`, including localization at zero.

For `S = Submonoid.powers f`, `smallTorsion_powers_iff_uniform` identifies
support with annihilation by one power of `f` on the whole represented finite
module. Restriction of scalars from `R/(f)` identifies modules killed by `f`;
the finite power filtration then gives `closedSupportGEquiv f n`.
Its forward map is `closedSupportedKMap f n`, and
`closedSupportGEquiv_pushforward` retains the actual closed restriction-of-scalars
map `closedPushforwardKMap`. `principalClosedLocalization_longExact` has closed
term `G (R/(f))` and open term `G (R[f⁻¹])`, with the transported boundary and
the same G₀ endpoint.

[`IdealClosedSupport`](https://github.com/kangxyz/aglib/blob/16aa08a90198d76be0bec47dd640b5c992acd9d7/Aglib/Algebra/Category/FGModuleCat/IdealClosedSupport.lean)
also constructs the actual equivalence between finite `R/I`-modules and
modules killed by `I`.
[`idealPowerFiltration`](../../Aglib/Algebra/Category/FGModuleCat/IdealPowerFiltration.lean)
produces a finite filtration when a stated power of `I` annihilates the module.
The general geometric closed/open sequence, including a potentially nonaffine
open complement, is described in
[scheme localization](../../AlgebraicGeometry/Scheme/Coherent/README.md#coherent-open-and-closed-localization).
