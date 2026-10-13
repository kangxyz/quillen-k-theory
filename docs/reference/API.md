# API reference

Use a focused module for one interface; `import Quillen` imports the complete
library. This reference records selected import paths, public objects, canonical
maps, and size conventions. The [topic guides](../README.md#mathematical-topics)
develop the mathematical comparisons, their hypotheses, and their remaining
obligations; [scope](Scope.md) gives the cross-topic boundary.

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | Exact-category K-groups, canonical maps, equivalences, and small models |
| `Quillen.KTheory.Plus` | Selected ring plus/Q comparison and component interfaces |
| `Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | Scalar-extension unit and additive Hom universal property |
| `Quillen.Algebra.Category.ModuleCat.Finite` | Finite-module Serre and exact-category interfaces on mathlib's finitely generated module category |
| `Quillen.Algebra.Homology.FiniteProjectiveResolution` | Actual finite-projective resolutions and finite-free PID resolutions |
| `Quillen.KTheory.GrothendieckComparison.Equivalence` | Classical exact-category K₀ comparison |
| `Quillen.Waldhausen.Basic` | Cofibrations, weak equivalences, and chosen zero |
| `Quillen.Waldhausen.KTheory` | Connective S-construction groups |
| `Quillen.Waldhausen.GrothendieckComparison.SmallModel` | Classical Waldhausen K₀ with independent object and morphism universes |
| `Quillen.Waldhausen.GrothendieckComparison.ImageQuotientExact` | Coarse image-quotient K₀ exactness under exactness and target factorization |
| `Quillen.Waldhausen.Approximation.Basic` | Generic approximation property |
| `Quillen.Waldhausen.FunctorialFactorization.Basic` | Generic functorial cofibration factorization |
| `Quillen.Devissage.Homotopical` | Finite-filtration dévissage |
| `Quillen.Resolution` | Admissible finite-resolution comparisons |
| `Quillen.Localization.Serre.LocalizationTheorem` | Connective Serre localization |
| `Quillen.GTheory.FiniteModules.LocalizationSequence` | Finite-module G-localization |
| `Quillen.Topology.DeformationRetract.Basic` | Cylinder deformation retracts and pushout transport |
| `Quillen.Topology.MappingCylinder.Basic` | Interval maps, cylinder projections, and retracts |
| `Quillen.Topology.HELP.Basic` | Homotopy extension and continuous cylinder coordinates |
| `Quillen.Topology.UnitInterval` | Shared interval multiplication continuity |
| `Quillen.Topology.Realization.Constant` | The literal realization of a constant simplicial map |
| `Quillen.Topology.Realization.Skeleton` | The bottom simplicial skeleton |
| `Quillen.Topology.Pushout.HomotopyEquivalence` | Homotopy gluing and specified component maps |
| `Quillen.Topology.Realization.SubfamilyHEP` | Homotopy extension for realized simplicial subfamilies |
| `Quillen.AlgebraicGeometry.Scheme` | Selected geometric K/G interfaces |
| `Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization` | Perfect localization for quasi-compact opens of qcqs schemes |
| `Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris` | Connective two-open sequence and matching K₀-class gluing |
| `Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups` | Scheme Bass groups from perfect K₀ |
| `Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality` | Iterated S-spectrum, additive K-comparison, and exact-functor laws |
| `Quillen.Topology.Prespectrum.StableLocalization` | Coherent-homotopy quotient and categorical stable localization |

Whole-topic imports include `Quillen.Algebra`, `Quillen.CategoryTheory`,
`Quillen.Topology`, `Quillen.KTheory`, `Quillen.Devissage`, `Quillen.Resolution`,
`Quillen.Localization`, `Quillen.GTheory`, `Quillen.AlgebraicGeometry`, and
`Quillen.Waldhausen`. `Quillen.AlgebraicGeometry.PerfectComplexes` is a generated
nested facade; individual modules have smaller dependency closures.

## Migration to 0.5.0

The 0.5.0 refactor places generic foundations below their applications and
uses one implementation of shared constructions. Obsolete module paths and
duplicate declarations are removed; update imports and references directly.

| Previous import | Current owner |
| --- | --- |
| `Quillen.GTheory.FiniteModules.Basic` | `Quillen.Algebra.Category.ModuleCat.Finite` |
| `Quillen.AlgebraicGeometry.Scheme.Regular.FiniteProjectiveResolution` | `Quillen.Algebra.Homology.FiniteProjectiveResolution` |
| `Quillen.AlgebraicGeometry.Scheme.Regular.LocalPrincipalDomain` | `Quillen.Algebra.RegularLocal.PrincipalDomain` |
| `Quillen.Waldhausen.QuillenComparison.SpanNaturality` | `Quillen.CategoryTheory.QConstruction.SpanIsoNaturality` |

Use `Quillen.ExactStructure.qSpan_iso_naturality` for the shared Q-span law and
`Quillen.HomologicalAlgebra.mappingCone_acyclic_of_quasiIso` for cone acyclicity.
The localization functor and representative-map law are
`Quillen.GroupCompletion.Localization.actedMapFunctor` and
`actedMapFunctor_mkHom`. The realization constant-map law is
`Quillen.realization_const_apply`; the universal homotopy vertex-track law is
`Quillen.classifyingSpaceUniversalHomotopy_vertex_track`.
Projective-line applications use the single `polynomialChart` family in
`Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts`, with `true` selecting
the plus chart and `false` selecting the minus chart.

Mathematical hypotheses, original maps, and comparison boundaries are retained.

## Module paths and namespaces

Geometric source lies under `Quillen.AlgebraicGeometry.Scheme` and
`Quillen.AlgebraicGeometry.PerfectComplexes`; principal declaration namespaces
are `Quillen.Scheme`, `Quillen.SchemeSheaf`, and `Quillen.PerfectComplexes`.
Paths describe mathematical ownership and need not match declaration namespaces.
For example, import `Quillen.AlgebraicGeometry.Scheme.Pullback` and
`Quillen.AlgebraicGeometry.PerfectComplexes.Basic` for those canonical interfaces.
Topological foundations lie under `Quillen.Topology`, while categorical
Theorem B interfaces remain under `Quillen.CategoryTheory.TheoremB`.
Approximation and functorial factorization have generic interfaces separate
from `Quillen.Waldhausen.SplitComplexes`.

| Construction | Declaration namespace |
| --- | --- |
| Cylinder deformation retracts | `Quillen.CylinderStrongDeformationRetract` |
| Primitive mapping-cylinder maps | `Quillen.MappingCylinder` |
| Homotopy extension and general cancellation | `Quillen` |
| Pushout homotopies and gluing | `Quillen.Pushout` |
| Realization coproducts and subfamilies | `Quillen.Realization` |
| Cylinder boundary data | `Quillen.CylinderBoundary` |
| Compact mapping-cylinder lifting | `Quillen.MappingCylinder.Compact` |
| Source and target mapping-cylinder collars | `Quillen.MappingCylinder.SourceCollar`, `Quillen.MappingCylinder.TargetCollar` |
| Fiberwise bridge projection, charts, and collars | `Quillen.FiberwiseBridge`, `Quillen.FiberwiseBridge.SourceCharts`, `Quillen.FiberwiseBridge.TargetCollar` |
| Sequential and skeletal Cartesian realization | `Quillen.CartesianRealization.Sequential`, `Quillen.CartesianRealization.Skeletal` |

The cylinder, retraction, and homotopy-extension owners have generic topology
dependencies; Theorem A and B consume their public interfaces. Composition and
coercion lemmas follow their canonical simplification direction. Equivalence
coercions use `_coe`; normalize underlying homomorphisms with
`MulEquiv.toMonoidHom_eq_coe` before rewriting.

## Canonical objects and maps

Namespaces record the constructions; module paths record their mathematical
owners. The following notation assumes the input structure and hypotheses
specified by the declaration and its linked topic guide.

| Input | Objects and canonical maps | Guide |
| --- | --- | --- |
| Exact structure `E` | `E.QCategory`, `E.KSpace`, `E.kBasepoint`, `E.K n`, `E.SmallK n` | [Exact categories](../topics/ExactCategories.md) |
| Exact functor `F` | `F.mapQ`, `F.KMap n`, `F.smallKMap n` | [Exact functors](../topics/ExactCategories.md#exact-functors-and-their-canonical-maps) |
| Bundled small exact category | `Quillen.SmallExactCategory.ofExactStructure`, `KFunctor n` | [Size conventions](../topics/ExactCategories.md#equivalences-and-universe-boundaries) |
| Waldhausen structure `W` | `W.Delooping`, `W.kBasepoint`, `W.K n` | [Waldhausen theory](../topics/Waldhausen.md) |
| Bundled small Waldhausen category | `Quillen.Waldhausen.SmallWaldhausenCategory.KFunctor n` | [Chosen zero and functoriality](../topics/Waldhausen.md#exact-functors-and-the-chosen-zero) |
| Scheme `X` | `Quillen.Scheme.K X n`, `G X n`, `restrictK`, `restrictG`, `KToG` | [Scheme K/G-theory](../topics/SchemeKTheory.md) |
| Strict/local perfect complexes | `Quillen.PerfectComplexes.StrictPerfect`, `Perfect`, `StrictK`, `PerfectK` | [Perfect complexes](../topics/PerfectComplexes.md#complexes-and-support) |
| Based prespectrum | `Quillen.LoopPrespectrum`, signed stable groups, actual fibers and telescopes | [Spectra](../topics/SpectraAndBass.md) |
| Ring-indexed Bass recursion | `Quillen.Bass.negativeKFunctor i` on `CommRingCat` | [Bass groups](../topics/SpectraAndBass.md#bass-cokernels-and-the-original-laurent-seed) |
| Projective completion | `Quillen.FiniteProjectiveModule.StableCompletion.Completion`, `ZeroComponent`, `stableZeroMap` | [Ring plus model](../topics/PlusConstruction.md) |

For composable exact functors, the pointwise map law is
`(F.comp G).KMap n x = G.KMap n (F.KMap n x)`.
`Quillen.ExactFunctor.KMap_id_apply` and `KMap_comp_apply` are public helpers in
`Quillen.KTheory.API`. Natural-isomorphism and small-model comparisons use the
same canonical maps; their explicit universe and comparison inputs remain in
the individual interfaces.

Scheme `K X n`, `G X n`, `StrictK X n`, and `PerfectK X n` lie in
`Type (u + 1)` for `X : Scheme.{u}`. The affine finite-module G interface is in
`Type u`. Bundling an essentially small category requires its actual selected
small model; a universe change is not a new arbitrary identification.

## Degree-zero presentation interfaces

| Import after `Quillen.` | Canonical comparison |
| --- | --- |
| `KTheory.GrothendieckComparison.Equivalence` | `ExactStructure.grothendieckKZeroEquiv`, with `grothendieckToKZero` and `kZeroToGrothendieck` |
| `KTheory.GrothendieckComparison.Functor` | `SmallExactCategory.grothendieckFunctor`, `grothendieckKZeroIso` |
| `Waldhausen.GrothendieckComparison.Equivalence` | `Waldhausen.AlgebraicGrothendieck.grothendieckKZeroEquiv` |
| `Waldhausen.GrothendieckComparison.SmallModel` | `Waldhausen.AlgebraicGrothendieck.grothendieckKZeroEquivOfSmallModel` |
| `AlgebraicGeometry.PerfectComplexes.GrothendieckComparison` | `PerfectComplexes.perfectGrothendieckKZeroEquiv` |

These comparisons retain the original object classes and K-maps. Exact-category
presentations use conflation relations; Waldhausen presentations use weak-arrow
and cofibration-pushout relations. Their separate size and naturality interfaces
are described in the [exact](../topics/ExactCategories.md#the-object-and-conflation-presentation-of-k₀)
and [Waldhausen](../topics/Waldhausen.md#classical-k₀-and-small-model-transport)
guides. The perfect specialization does not supply a triangulated-derived
presentation.

## Geometric maps and localization endpoints

| Import after `Quillen.AlgebraicGeometry.` | Selected public maps |
| --- | --- |
| `Scheme.Pullback`, `Scheme.FlatPullback` | `Quillen.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| `Scheme.FinitePushforward`, `Scheme.FiniteFlatPushforward` | `Quillen.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| `Scheme.Regular` | `Quillen.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
| `PerfectComplexes.Basic`, `PerfectComplexes.Local` | `Quillen.PerfectComplexes.StrictK`, `PerfectK` |
| `PerfectComplexes.OpenFunctor` | `perfectOpenKMap`, `perfectOpenKRestrict`, `perfectKRestrict` |
| `PerfectComplexes.OpenLongExactSequence` | `perfectOpenConnectingHom`, `perfectOpen_positiveLongExactSequence` |
| `PerfectComplexes.GlobalLocalization` | Actual open endpoint, positive comparison and degree-zero image |
| `PerfectComplexes.MayerVietoris` | Two-open connective sequence and matching K₀-class gluing |

In the perfect rows, unqualified names belong to `Quillen.PerfectComplexes`.
[Scheme K/G-theory](../topics/SchemeKTheory.md) records all-map bundle pullback,
flat/noetherian coherent pullback, regularity/resolution conditions, finite
direct image, and the generic derived sheaf maps. The
[perfect-complex guide](../topics/PerfectComplexes.md) records the support,
qcqs/open, degree-zero, and auxiliary-cover conditions of localization.
The relative group `PerfectOpenK j n` and actual `PerfectK U n` are different
endpoints until the corresponding comparison is applied.

## Spectral and Bass entrypoints

| Import after `Quillen.` | Interface |
| --- | --- |
| `Waldhausen.SConstruction.Iterated.StableHomotopy` | Original additive `originalKStableEquiv` and connective spectrum |
| `Waldhausen.SConstruction.Iterated.StableFunctoriality` | Normalized exact-functor spectrum maps and K-map naturality |
| `Waldhausen.SConstruction.Iterated.LocalizedFunctoriality` | `localizedSpectrumMap` and its strict laws |
| `Topology.Prespectrum.FiberSequence` | Signed stable long exact sequence of actual path-space fibers |
| `Topology.Prespectrum.StableLocalization` | Coherent-homotopy quotient and categorical stable localization |
| `Topology.Prespectrum.ConeLinearExcision` | Specified cone-fiber comparison under growth and point HEP |
| `Topology.Prespectrum.TelescopeStableColimit` | T1 telescope stable-colimit comparison |
| `Topology.Prespectrum.LoopTailReplacementFiberEquivalence` | Ω replacement and fiber comparison |
| `KTheory.Bass.StrictRingDiagram` | Strict spectral Bass endofunctor and supplied-seed transitions |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassNegativeMap` | Finite-stage bottom comparison and natural negative-class maps |

The [spectrum guide](../topics/SpectraAndBass.md) distinguishes original
connective groups, recursive Bass cokernels, finite-stage bottom groups, and
telescope maps. The [perfect guide](../topics/PerfectComplexes.md) records the
geometric seed and support/localization comparisons. A generic diagram
interface, finite-stage isomorphism, or stable self-comparison does not supply
an additional rectification or telescope-identification theorem.

## Finite Čech models and full-open graded diagrams

| Import after `Quillen.` | Principal interface |
| --- | --- |
| `Algebra.Module.FiniteParametrix` | `Quillen.Module.finite_projective_parametrixKernel` and the split finite-defect replacement |
| `Algebra.ModuleComplex.LaurentModuleCech` | Finite-projective homotopy model of the literal module Čech differential |
| `AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleCech` | Actual finite-projective chart-section Čech model for every finite locally free sheaf |
| `AlgebraicGeometry.Scheme.ProjectiveLine.DerivedCechCone` | Original derived projection image and signed sheaf Čech cone comparison |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.DerivedPushforwardVectorBundle` | `Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedPushforward_vectorBundle` |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BoundedDerivedPushforward` | `Quillen.PerfectComplexes.ProjectiveLine.perfect_derivedPushforward_of_bounded_vectorBundle_terms` |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison` | Actual full-open section K and perfect-K comparison |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModel` | Original strict chosen-zero restriction Model map |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContractionNaturality` | Whole Laurent self-track contraction and coefficient naturality |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedDiagramNull` | Constructed natural nullhomotopy of the original graded Bass seed |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTelescope` | All-integer transition-zero and actual graded telescope stable-group vanishing |

The [scheme guide](../topics/SchemeKTheory.md) records chart module data and the
new finite-defect proof of projection perfection. The
[perfect-complex guide](../topics/PerfectComplexes.md) records the actual
relative/full-open models and original-map transfer boundary. The
[spectrum guide](../topics/SpectraAndBass.md) gives generic natural-null and
cone/telescope-descent interfaces and the graded telescope proof.

The graded telescope is the specified `Under R` diagram for open
`j : U ⟶ Spec R` with `CompactSpace U`. Its vanishing does not identify it
with the original ungraded Bass telescope or with classical negative K-theory.
The proved fine-to-graded seed square retains its original maps; the missing
restriction/localization-null/cone-descent transfer is a separate construction.

## Ring plus and scalar extension

The selected public facade is `Quillen.KTheory.Plus`. Names below are relative
to `Quillen.FiniteProjectiveModule`.

| Import after `Quillen.` | Public names |
| --- | --- |
| `KTheory.Plus.StableGeneralLinearPlus` | `StableCompletion.stableZeroMap_isPlusConstruction` |
| `KTheory.Plus.ProjectiveCompletionZeroLoops` | `StableCompletion.zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence` |
| `KTheory.Plus.ProjectiveCompletionPositiveKNaturality` | `StableCompletion.zeroCompletionPositiveKEquiv_baseChange` |
| `KTheory.Plus.ProjectiveCompletionZerothHomotopy` | `completionZerothHomotopyKZeroEquiv` and actual object-class naturality |
| `KTheory.Plus.ProjectiveTelescopeKZero` | `StableFreeRight.telescopeZerothHomotopyKZeroEquiv` and original stage classes |
| `KTheory.Map.RightBaseChange` | Original `rightBaseChangeExact.KMap` identity/composition laws |
| `Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | `rightBaseChangeUnit`, `rightBaseChangeHomEquiv`, `rightBaseChangeLift`, `rightBaseChange_existsUnique` |

The raw finite-free and idempotent-image scalar owners are
`Quillen.Algebra.Matrix.RightScalarExtension` and
`Quillen.Algebra.Category.ModuleCat.MatrixImageScalarExtension`. The
[plus guide](../topics/PlusConstruction.md) retains the coefficient and ring
universes, basepoint corrections, component formulas, and literal Hom-unit
property. General CW uniqueness, whole-space splitting, and a separate
balanced-tensor carrier comparison remain outside those interfaces.

## Client examples

The [downstream package](../../examples/downstream) has its own configuration,
manifest, and build outputs. Its proofs use the library as a local path
dependency. Selected clients exercise canonical maps and exact comparison
interfaces:

| Topic | Client |
| --- | --- |
| Exact functors and K₀ | [ExactFunctor](../../examples/downstream/Consumer/ExactFunctor.lean), [GrothendieckComparison](../../examples/downstream/Consumer/GrothendieckComparison.lean) |
| Waldhausen comparisons | [WaldhausenAdditivity](../../examples/downstream/Consumer/WaldhausenAdditivity.lean), [WaldhausenFibration](../../examples/downstream/Consumer/WaldhausenFibration.lean), [GilletWaldhausenReduction](../../examples/downstream/Consumer/GilletWaldhausenReduction.lean) |
| Dévissage, resolution, localization | [Devissage](../../examples/downstream/Consumer/Devissage.lean), [Resolution](../../examples/downstream/Consumer/Resolution.lean), [Localization](../../examples/downstream/Consumer/Localization.lean) |
| Scheme maps and regular comparison | [Scheme](../../examples/downstream/Consumer/Scheme.lean), [Regular](../../examples/downstream/Consumer/Regular.lean), [FinitePushforward](../../examples/downstream/Consumer/FinitePushforward.lean) |
| Perfect complexes and derived geometry | [PerfectFoundations](../../examples/downstream/Consumer/PerfectFoundations.lean), [DerivedPushforwardComparison](../../examples/downstream/Consumer/DerivedPushforwardComparison.lean) |
| Finite homotopy scope | [FiniteHELP](../../examples/downstream/Consumer/FiniteHELP.lean) |
| Ring plus and scalar extension | [RingPlusNaturality](../../examples/downstream/Consumer/RingPlusNaturality.lean), [RingScalarExtension](../../examples/downstream/Consumer/RingScalarExtension.lean) |
| Full-open graded stable concentration | [FullOpenGradedSectionStable](../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean) |

The maintained [tests](../../QuillenTest) cover further constructions and regressions.
Neither tests nor clients are dependencies of library source.
[Scope](Scope.md#verification) and
[architecture](../development/Architecture.md#trust-checks) describe the build
and foundation-audit boundary.
