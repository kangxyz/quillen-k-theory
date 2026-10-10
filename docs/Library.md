# Library guide

Use an individual module when you need one interface. Whole-topic facades are
convenient for broader developments; `import Quillen` imports the complete
library. The [scope guide](Scope.md) records hypotheses and open boundaries.

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | Exact-category K-groups, exact-functor maps, equivalences, and small models |
| `Quillen.Waldhausen.Basic` | Waldhausen structures, cofibrations, and weak equivalences |
| `Quillen.Waldhausen.KTheory` | Connective S-construction groups |
| `Quillen.Waldhausen.Approximation.Basic` | Generic approximation property |
| `Quillen.Waldhausen.FunctorialFactorization.Basic` | Generic functorial cofibration factorization |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |
| `Quillen.Resolution` | Admissible finite-resolution comparisons |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |
| `Quillen.AlgebraicGeometry.Scheme` | Selected geometric K/G interfaces |
| `Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization` | Perfect localization for quasi-compact opens of qcqs schemes |
| `Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris` | Connective two-open sequence and matching K₀-class gluing |
| `Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups` | Scheme Bass groups from perfect K₀ |
| `Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality` | Iterated S-spectrum, stable K-group comparison, and arbitrary exact-functor laws |
| `Quillen.Topology.Prespectrum.StableLocalization` | Coherent-homotopy quotient and categorical stable localization |

Whole-topic imports include `Quillen.Algebra`, `Quillen.CategoryTheory`,
`Quillen.Topology`, `Quillen.KTheory`, `Quillen.Devissage`, `Quillen.Resolution`,
`Quillen.Localization`, `Quillen.GTheory`, `Quillen.AlgebraicGeometry`, and
`Quillen.Waldhausen`. `Quillen.AlgebraicGeometry.PerfectComplexes` is a generated
nested facade; its individual modules give much smaller dependency closures.

## Module paths and namespaces

Geometric source is under `Quillen.AlgebraicGeometry.Scheme` and
`Quillen.AlgebraicGeometry.PerfectComplexes`. For example, import
`Quillen.AlgebraicGeometry.Scheme.Pullback` and
`Quillen.AlgebraicGeometry.PerfectComplexes.Basic` for these interfaces.
Their principal declaration namespaces are `Quillen.Scheme` and
`Quillen.PerfectComplexes`. Use the canonical interfaces described below.

Generic topological foundations are under `Quillen.Topology`; categorical
Theorem B interfaces remain under `Quillen.CategoryTheory.TheoremB`.
Approximation and functorial factorization have generic interfaces separate
from `Quillen.Waldhausen.SplitComplexes`. Paths describe ownership rather than
requiring a matching declaration namespace.

The generic constructions use these declaration namespaces:

| Construction | Namespace |
| --- | --- |
| Compact mapping-cylinder lifting | `Quillen.MappingCylinder.Compact` |
| Source and target mapping-cylinder collars | `Quillen.MappingCylinder.SourceCollar`, `Quillen.MappingCylinder.TargetCollar` |
| Fiberwise bridge charts and collars | `Quillen.FiberwiseBridge.SourceCharts`, `Quillen.FiberwiseBridge.TargetCollar` |
| Sequential Cartesian realization | `Quillen.CartesianRealization.Sequential` |
| Skeletal Cartesian realization | `Quillen.CartesianRealization.Skeletal` |

Composition and coercion lemmas follow their canonical simplification direction.
Equivalence coercions use `_coe`; their underlying monoid homomorphisms can be
normalized with `MulEquiv.toMonoidHom_eq_coe` before rewriting.

## Exact categories and canonical maps

For an exact structure `E`, `E.QCategory` is the restricted-span category,
`E.KSpace` its classifying space, `E.kBasepoint` its chosen point, and `E.K n`
its connective K-group. `E.SmallK n` is the chosen small-model interface.

An exact functor `F : ExactFunctor E E'` induces `F.mapQ`, `F.KMap n`, and
`F.smallKMap n`. The API includes identity, composition, and natural-isomorphism
laws. For a composable `G`, the pointwise composition law is

```lean
(F.comp G).KMap n x = G.KMap n (F.KMap n x)
```

`SmallExactCategory.ofExactStructure E` bundles the input;
`SmallExactCategory.KFunctor n` supplies the group-valued functor using the same
canonical maps. See the [exact-functor client](../examples/downstream/Consumer/ExactFunctor.lean).

## Waldhausen interfaces

For `W : Quillen.Waldhausen.Structure C`, cofibrations, weak equivalences, and
zero are explicit data. `W.Delooping` realizes the diagonal S-construction
nerve, `W.kBasepoint` is its point, and `W.K n` gives its connective groups.
The exact-category Q/S comparison is in
`Quillen.Waldhausen.QuillenComparison.Equivalence`.

`Quillen.Waldhausen.Fibration.GeneralComparison` supplies the canonical fiber
comparison with nested weak equivalences, coarse two-out-of-three and extension,
joint-cylinder data, and the second-endpoint section identity.
`Quillen.Waldhausen.Fibration.LongExactSequence` supplies its canonical maps and
exactness statements. Object and morphism universes may differ.

`Quillen.Waldhausen.GilletWaldhausen.GeneralComparison` compares bounded-term
complexes with the stated abelian term category. Its term property must contain
zero and be closed under isomorphisms, extensions, and admissible kernels.
`Quillen.Waldhausen.Cofinality.GeneralDense` keeps dense-cofiber closure and
joint-cylinder data explicit; positive equivalences and degree-zero tails have
separate statements.

The Serre localization API provides `quotientKMap`, `connectingHom`, and
`localizationSequence`, with the connective K₀ tail. The independent algebraic
Waldhausen group is `Quillen.Waldhausen.AlgebraicGrothendieck.Group W`;
identification with homotopical `W.K 0` remains open.

## Scheme and perfect-complex interfaces

For `X : AlgebraicGeometry.Scheme.{u}`, `Quillen.Scheme.K X n` uses vector
bundles, and `Quillen.Scheme.G X n` uses coherent sheaves under the local
noetherian hypotheses. These groups lie in `Type (u + 1)`.
`Quillen.Scheme.Affine.G R n` lies in `Type u` and has its own affine interface.

`Quillen.CoherentScheme.AffineFiniteType R` is the full category of affine
quasicoherent sheaves with finite global-sections module, over any ring.
`Quillen.CoherentScheme.affineLocallyFiniteType X` tests quasicoherence and finite
type on every affine open chart; `FiniteTypeSheaves X` is its full subcategory,
over any scheme. The Serre, abelian, exact-category, and G-theory results retain
their stated noetherian or locally noetherian hypotheses.

`restrictK`, `restrictG`, and `KToG` are the canonical restriction and inclusion
maps. `pullbackK` and `KFunctor` accept all scheme morphisms; `pullbackG` requires
flat maps between locally noetherian schemes. The regular affine K→G comparison
has no finite Krull-dimension bound; the nonaffine result retains
quasi-compactness and the resolution property. These declarations remain in
`Quillen.Scheme`, with source under `Quillen.AlgebraicGeometry.Scheme`.

In `Quillen.PerfectComplexes`, `StrictPerfect X` consists of globally bounded
finite locally free complexes. `Perfect X` consists of complexes locally
isomorphic in quasi-isomorphism localization to strict perfect complexes.
`StrictK X n` and `PerfectK X n` are connective S-construction groups in
`Type (u + 1)`.

`vectorBundleToStrictKEquiv` holds on every scheme, and affine strict/local
comparisons include every nonnegative degree. `strictKPullback` accepts every
scheme map. `perfectKPullback` and `PerfectKFunctor` accept arbitrary maps
between quasi-compact schemes and agree with the existing restriction maps.
The relative/support comparison, qcqs positive endpoint, K₀ image, support
excision, and ordinary/supported Mayer–Vietoris APIs are described in
[ThomasonTrobaugh.md](ThomasonTrobaugh.md).

`Quillen.Scheme.ProjectiveLine.twoChartLine R` glues two affine polynomial
charts along the Laurent overlap. Its projection is flat, the scheme is qcqs,
and `globalSectionsIso R` identifies its global sections with `R`.
See [ProjectiveLine/Charts.lean](../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/Charts.lean)
and [ProjectiveLine/GlobalSections.lean](../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/GlobalSections.lean).
Proj identification, twisting sheaves, higher cohomology, perfect pushforward,
and the projective-bundle formula remain separate work. The finite-coefficient
retract criterion in `Quillen.Algebra.Module.FiniteCoefficientRetract` is
conditional on its projectivity/splitting and uniform finite-window hypotheses;
no production application supplies the missing pushforward theorem.

## Connective spectra

`Quillen.LoopPrespectrum` has actual based spaces and continuous maps
`Eₙ → ΩEₙ₊₁`. `Quillen.Waldhausen.IteratedS.originalPrespectrum W` uses the
iterated S-construction and its original cylinder loop maps;
`originalPrespectrum_isOmega` proves the Ω condition.

For an integer `d`, `Quillen.LoopPrespectrum.stableHomotopyGroup E d` is the
additive colimit of the groups

```text
π_(d.toNat + n + 2)(E_((-d).toNat + n + 2)),  n : ℕ.
```

Transitions use the actual structure maps and loop degree shift. For an
Ω-spectrum, `stableHomotopyStageZeroIso` in
`Quillen.Topology.Prespectrum.StableOmega` inverts the first stable-system
inclusion. That stage is a positive spectrum level determined by `d`.

In `Quillen.Waldhausen.IteratedS`, `originalKStableEquiv W n` is an additive
equivalence from `Additive (W.K n)` to the integer-degree stable group for every
`n : ℕ`, including K₀ and its group law. The earlier `originalZeroSpaceEquiv`
has a set-equivalence type. The negative stable groups of this connective
spectrum vanish; see `originalStableHomotopyGroup_neg_subsingleton`.

`exactOriginalPrespectrumMap` and `exactOriginalOmegaSpectrumMap` normalize
arbitrary exact functors at zero while preserving public `KMap`. Weak natural
transformations give whole based homotopies compatible with the structure maps;
normalized identity and binary composition have such homotopies.
`exactStableKMap` has named identity, composition, and weak-transformation laws.
`originalKStableEquiv_exact_naturality` retains original K-maps in every
nonnegative degree without a chosen-zero equality premise.

## Stable fibers and localization

In `Quillen.LoopPrespectrum`, `parameterLooping` transposes the loop and
structure coordinates. Its integer stable shift `parameterStableHomotopyIso`
uses the stage sign correction `(-1)^n` and `parameterStableOffset d`, equal to
one for `d < 0` and zero otherwise. This construction has its own structure
maps; use its API directly rather than identifying it with `looping` or the
older square-cone construction.

`homotopyFiber f` is an actual path-space prespectrum. If both inputs are
Ω-spectra, its Ω theorem includes component conditions. For every prespectrum
map, `stableFiberLongExactSequence` gives the integer-degree segment

```text
π^st_(d+1)(E) → π^st_(d+1)(F) → π^st_d(Fib f) → π^st_d(E) → π^st_d(F).
```

The boundary uses the inverse signed parameter-loop shift and literal
loop-to-fiber inclusion. A whole coherent based-square homotopy defines an
actual fiber map and boundary naturality. Vanishing of all integer stable fiber
groups detects stable equivalence. A fiber of connective inputs is connective
under the degree-zero surjectivity hypothesis.

The structural Waldhausen theorem in
`Quillen.Waldhausen.Fibration.SpectrumComparison` provides
`canonicalFiberPrespectrumMap_isStableEquivalence_general` with coarse
two-out-of-three, extension, joint data, and the second-endpoint section. It
retains the canonical path-space comparison and supplies the required K₀
surjectivity; this is a connective fibration comparison.

`CoherentHomotopyCategory` quotients by whole coherent based homotopies, and
`StableLocalization` then inverts maps inducing isomorphisms in every integer
stable degree. `localizedStableHomotopyFunctor` descends stable groups through
this category, with a universal lift. A stable model structure, triangulation,
and cofiber exactness are not part of this construction.

In `Quillen.Waldhausen.IteratedS`, `localizedSpectrumMap` has literal identity
and composition equalities and weak-transformation invariance.
`localizedSpectrumMapIso` requires bijectivity of every original K-map, including
K₀. Strict arbitrary-exact functoriality is supplied after stable localization;
raw normalized prespectrum maps retain the homotopy laws above.

`Quillen.PerfectComplexes.PerfectLocalizedSpectrumFunctor` is contravariant for
arbitrary maps between quasi-compact schemes. It inverts the bounded-flat
inclusion in the localized category, preserves the original perfect K-maps, and
agrees with flat pullback. `BoundedFlatLocalizedSpectrumFunctor` accepts all
schemes. See [Spectrum/DerivedPullback.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean).
The localized inverse does not assert a strict continuous inverse.

## Bass groups and the affine transition

`Quillen.PerfectComplexes.Bass.negativeKFunctor n` is contravariant on
quasi-compact schemes; `n : ℕ` denotes degree `-n`. The seed is homotopical
`PerfectK X 0` in additive form. Each successor is the actual cokernel of the
two polynomial-to-Laurent maps, with quotient, exactness, and descent APIs.
`Bass.supportedNegativeKFunctor` uses supported perfect K₀ on pairs with a
quasi-compact ambient scheme and an arbitrary vanishing open.

The affine ring interface is `Quillen.Bass.negativeKFunctor`.
`Quillen.Bass.affineSchemeNegativeKIso` compares the ring and scheme-product
recursions naturally in every nonpositive degree; its degree-zero component is
the literal original K₀ identity. These groups have not been identified with
algebraic Grothendieck K₀ or negative stable groups of a Bass spectrum.

`Quillen.PerfectComplexes.affineBassTransition` uses the actual Laurent unit
`T¹` with inverse `T⁻¹`, its scalar automorphism, and the structure-compatible
homotopy to construct one affine Bass step. Functorial spectral iteration,
comparison with the cokernel groups, and the fundamental theorem remain open.
See [Affine/BassStep.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassStep.lean)
and [Affine/BassSchemeComparison.lean](../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassSchemeComparison.lean).

## Client examples

The [downstream package](../examples/downstream) exercises public interfaces
through a local path dependency with its own configuration, manifest, and build
directory. The maintained [tests](../Tests) cover additional constructions and
regressions. Neither directory is a dependency of library source.
