# API reference

Use a focused module for one interface; `import Quillen` imports the complete
library. This reference records selected import paths, public objects, canonical
maps, and size conventions. The [topic guides](../README.md#mathematical-topics)
develop the mathematical comparisons, their hypotheses, and their remaining
obligations; [scope](Scope.md) gives the cross-topic boundary.

## Local Aglib candidates in 0.9.0

General algebraic geometry and its algebraic, categorical and homological
prerequisites awaiting upstream admission live below `Quillen.Aglib`. Import
their precise mathematical leaves from the [candidate tree](../../Quillen/Aglib/README.md).
Existing public declaration namespaces and chosen comparison maps are preserved;
this change reorganizes implementation ownership and splits mixed sources.

The source modules for moved general implementations use the new candidate
paths. Application modules keep their existing paths and import their lower
candidate prerequisites. No duplicate implementation or default forwarding
module is retained for a moved source. Q/K/G/S, Waldhausen, spectra and the
specialized projective-line applications remain in their mathematical owners.

The pinned Aglib 5895002 supplies the original affine injective resolution, derived flat
pullback composition and commuting-square comparison. Their copied definitions are retired;
Quillen keeps its additional Ext, inverse-unit and ordered unit-square theorems. The square
comparison uses native arguments `(c, a, b, j, h.symm)` for the former `(a, j, c, b, h)`
interface, preserving its direction and actual map. The native quasicoherent extension
instance and `unitMul_zero` also supply the shared interfaces directly.

`ModuleCat.scalarBaseChangeNatTrans` and `scalarBaseChangeNatTrans_unit` retain the
candidate's whole natural transformation and unit equation. These explicit names distinguish
them from Aglib's per-module `scalarBaseChangeMap`; no component comparison is asserted.
The independent `Consumer.PublicLibraries` imports both complete public roots together.

## Imports

| Import | Interface |
| --- | --- |
| `Aglib.CategoryTheory.ExactCategory.Basic` | Exact structures and conflations |
| `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Shift` | Original derived flat base-change mate and its actual shift compatibility |
| `Quillen.Aglib.CategoryTheory.Abelian.SerreClass.Annihilation` | Annihilated objects and the canonical quotient by a Serre class |
| `Quillen.CategoryTheory.QConstruction.Basic` | Quillen's Q-construction |
| `Quillen.KTheory.API` | Exact-category K-groups, canonical maps, equivalences, and small models |
| `Quillen.Algebra.Group.StableFieldDeterminant` | Actual stable determinant, field elementary kernel, and quotient determinant equivalence |
| `Quillen.KTheory.Field.ProjectiveDeterminant` | Original projective-Q K1 determinant and actual base-change square |
| `Quillen.KTheory.Field.ModuleDeterminant` | Upper finite-module K1 determinant with literal tensor-extension naturality |
| `Quillen.KTheory.Field.MatrixCubeComparison` | `moduleDetEquiv_matrix_cube` on the literal upper-small positive matrix cube, every field and rank including zero |
| `Quillen.KTheory.Field.MatrixTransport` | Original free-module coordinate isomorphism to the standard action of the same matrix |
| `Quillen.KTheory.FiniteSupport.Decomposition` | Positive finite-support K-equivalence by original evaluations and finite sums of original inclusions |
| `Quillen.GTheory.Dedekind.ResidueFieldAssembly` | Native positive-degree residue-field G-assembly into actual torsion support, with original pushforwards |
| `Quillen.GTheory.Dedekind.Localization` | Original native residue-coordinate kernel intersections and finite-family lifting under explicit generic-G1 injectivity |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.FinitePointAssembly` | Public field-scheme G assembly into actual upper coherent support, every positive degree; Noetherian scheme, injective closed-point family and specified field closed immersions |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.UniverseComparison` | `publicSpecGRingEquiv` in all degrees over Noetherian rings and original public scheme residue-pushforward comparison |
| `Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.LocalizationNaturality` | Literal public `Scheme.pullbackG` equals native localization for every Noetherian ring and submonoid, in all degrees |
| `Quillen.GTheory.Dedekind.LocalDvrBoundaryNaturality` | Original local-DVR boundary after actual generic extension equals global residue coordinates for G(n+2) → G(n+1); kernel intersections and finite-family lifting under original generic-G1 injectivity |
| `Quillen.GTheory.DVR.SplitResidue` | Original generic finite-module G map injective in all degrees for a DVR whose actual residue map has a ring section |
| `Quillen.KTheory.MilnorK2.DVR.TameKernel` | Actual-DVR Milnor tame kernel equals the integer span of field symbols of two ring units, with ordered tame signs |
| `Quillen.KTheory.MilnorK2.FiniteField` | Original Milnor tensor quotient and integral finite-field vanishing; actual Quillen-G2 comparison remains separate |
| `Quillen.KTheory.Plus` | Standard ring plus/Q homotopy equivalences, original K₀–plus product and component interfaces |
| `Quillen.Topology.PlusConstruction.ClassicalCWUniqueness` | Automatic comparison and ordinary uniqueness for original plus maps on actual same-universe Hausdorff CW spaces |
| `Quillen.Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift` | Mixed-universe comparison and ordinary uniqueness on the original actual CW spaces |
| `Quillen.Topology.CWComplex.SimplyConnectedCover` | Constructed same-universe simply connected surjective cover of an actual connected Hausdorff CW subtype |
| `Quillen.Topology.CWComplex.UniverseTransport` | Actual intrinsic CW subtype and literal ULift geometry |
| `Quillen.Topology.HomotopyGroups.Loop.Reversal` | Actual inner-loop reflection and degree-shift formulas |
| `Quillen.Aglib.Algebra.Module.RightScalarExtension` | Literal noncommutative balanced right tensor and its universal properties |
| `Quillen.Aglib.Algebra.Category.ModuleCat.RightScalarExtension` | Tensor functor, identity/composition equivalences and literal-carrier triple coherence |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor` | Comparison with original scalar extension and explicit target lifts |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveTensorCoherence` | Agreement with original identity/composition comparisons |
| `Quillen.KTheory.Map.RightBaseChangeTensor` | Original zero-normalized K-map equality in every degree |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | Scalar-extension unit and additive Hom universal property |
| `Aglib.Algebra.Category.ModuleCat.Finite` | Finite-module Serre and exact-category interfaces on mathlib's finitely generated module category |
| `Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution` | Actual finite-projective resolutions and finite-free PID resolutions |
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

## Direct Aglib interfaces

General exact-category, commutative-algebra, module-sheaf and cohomology interfaces
are provided by [Aglib](https://github.com/kangxyz/aglib). Import precise `Aglib`
leaves and use their native mathematical namespaces. The transferred general
`Quillen` modules and aliases are removed; application imports remain in Quillen.

`ExactStructure` and `ExactFunctor`, including their Quillen K-map extensions,
use `CategoryTheory.ExactCategory`. Bundled `SmallExactCategory` and the actual
Q/K/G constructions remain Quillen-owned. Module ownership and declaration
namespace are distinct.

Derived flat base-change shift compatibility uses the native Aglib owner above.
The copied `Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.Shift`
implementation is retired; its consumers import the native leaf directly. The
original functor shift data and dependent compatibility proposition are retained.

For finite direct-image data on arbitrary schemes, use
`AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePushforward` and
`finiteTypePushforwardSpec`. The coherent specializations have locally Noetherian
source and target. General finite-type pullback retains its locally Noetherian
target and arbitrary source; the coherent specialization assumes both schemes
locally Noetherian. Use the lower interface whenever the original statement has
those weaker conditions.

## Migration to 0.5.0

The 0.5.0 refactor places generic foundations below their applications and
uses one implementation of shared constructions. Obsolete module paths and
duplicate declarations are removed; update imports and references directly.

| Previous import | Current owner |
| --- | --- |
| `Quillen.GTheory.FiniteModules.Basic` | `Aglib.Algebra.Category.ModuleCat.Finite` |
| `Quillen.AlgebraicGeometry.Scheme.Regular.FiniteProjectiveResolution` | `Quillen.Aglib.Algebra.Homology.ModuleCat.FiniteProjectiveResolution` |
| `Quillen.AlgebraicGeometry.Scheme.Regular.LocalPrincipalDomain` | `Quillen.Aglib.RingTheory.RegularLocalRing.PrincipalDomain` |
| `Quillen.Waldhausen.QuillenComparison.SpanNaturality` | `Quillen.CategoryTheory.QConstruction.SpanIsoNaturality` |

Use `CategoryTheory.ExactCategory.ExactStructure.qSpan_iso_naturality` for the shared Q-span law and
`CochainComplex.mappingCone_acyclic_of_quasiIso` for cone acyclicity.
The localization functor and representative-map law are
`Quillen.GroupCompletion.Localization.actedMapFunctor` and
`actedMapFunctor_mkHom`. The realization constant-map law is
`Quillen.realization_const_apply`; the universal homotopy vertex-track law is
`Quillen.classifyingSpaceUniversalHomotopy_vertex_track`.
Projective-line applications use the single `polynomialChart` family in
`Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts`, with `true` selecting
the plus chart and `false` selecting the minus chart.

Mathematical hypotheses, original maps, and comparison boundaries are retained.

## Standard comparison normalization

The 0.7.0 source integration directly refactors the public plus/Q comparison
to the standard `[P] - [R^n]` sign. The Q-construction, K-groups, canonical
K-maps and generic loop/fiber inverse retain their definitions. The standard
comparison inserts exactly one inner-loop reversal, with the outer direction
of its prescribed basepoint track retained. See
[standard comparison normalization](StandardSignMigration.md) for the exact
map equations, labels and client changes. The 0.5.0 owner migration above is
preserved.

The generic `Quillen.loopReversalHomeomorph` belongs to
`Quillen.Topology.HomotopyGroups.Loop.LeftComponentTranslation`, with an
explicit basepoint. `Quillen.Topology.HomotopyGroups.Loop.Reversal` reuses that
owner.

## Version 0.7.0 source integration

The imported sources include path-class endpoints and simply connected covers,
actual CW lifting and Whitehead recognition, automatic same-universe and
mixed-universe comparison and ordinary uniqueness for original plus maps, and
explicit coefficient-universe transport. The
[classical CW guide](../topics/ClassicalCWPlus.md) and
[homotopy foundations](../topics/HomotopyFoundations.md) record their exact
conditions. This is source integration; the package version does not identify
a published tag. Current merged checking is recorded only at
[verification](Scope.md#verification).

## Module paths and namespaces

Geometric source lies under `Quillen.AlgebraicGeometry.Scheme` and
`Quillen.AlgebraicGeometry.PerfectComplexes`; principal declaration namespaces
are `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Modules`, and `Quillen.PerfectComplexes`.
General module and coherent data come from Aglib; Q/K/G application declarations
remain defined by Quillen modules even when extending a native namespace.
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
| Scheme `X` | `AlgebraicGeometry.Scheme.K X n`, `G X n`, `restrictK`, `restrictG`, `KToG` | [Scheme K/G-theory](../topics/SchemeKTheory.md) |
| Strict/local perfect complexes | `Quillen.PerfectComplexes.StrictPerfect`, `Perfect`, `StrictK`, `PerfectK` | [Perfect complexes](../topics/PerfectComplexes.md#complexes-and-support) |
| Commuting path square | `Path.Homotopy.squareProjectionReturnMap`, `squareProjectionReturnTrack` | [Original path returns](../../Quillen/Topology/Path/SquareProjectionReturn.lean) |
| Based prespectrum | `Quillen.LoopPrespectrum`, signed stable groups, actual fibers and telescopes | [Spectra](../topics/SpectraAndBass.md) |
| Ring-indexed Bass recursion | `Quillen.Bass.negativeKFunctor i` on `CommRingCat` | [Bass groups](../topics/SpectraAndBass.md#bass-cokernels-and-the-original-laurent-seed) |
| Projective completion | `Quillen.FiniteProjectiveModule.StableCompletion.Completion`, `ZeroComponent`, `stableZeroMap` | [Ring plus model](../topics/PlusConstruction.md) |

The historical underscore spellings of the path-return constructors remain
transparent deprecated aliases of these canonical names.

For composable exact functors, the pointwise map law is
`(F.comp G).KMap n x = G.KMap n (F.KMap n x)`.
`CategoryTheory.ExactCategory.ExactFunctor.KMap_id_apply` and `KMap_comp_apply` are public helpers in
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
| `Scheme.Pullback`, `Scheme.FlatPullback` | `AlgebraicGeometry.Scheme.pullbackK`, `KFunctor`, `pullbackG`, `GFlatFunctor`, `KToG_pullback` |
| `Scheme.FinitePushforward`, `Scheme.FiniteFlatPushforward` | `AlgebraicGeometry.Scheme.GFinitePushforwardFunctor`, `KFiniteFlatPushforwardFunctor` |
| `Scheme.Regular` | `AlgebraicGeometry.Scheme.KToGRegularAffineEquiv`, `KToGRegularEquiv` |
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
| `KTheory.Bass.TwoChartAdditive` | Additive two-chart contraction and preservation of split exact sequences |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassActualSeedComparison` | Constructed whole seed square on the original two-chart pushout |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedIteration` | Objectwise first-to-second Bass map with literal inclusion, cylinder and loop-coordinate formulas |
| `Topology.Prespectrum.PushoutConeFamily`, `Topology.Prespectrum.PushoutConeFamilyRecovery` | Locally compact parameter descent through the original pushout and reduced cone, strict restriction/looping and recovery of entire chosen families |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeCube`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCubeConsumers` | Actual six-face original identity cube and whole comparison/cone/step identities |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingNative` | Native evaluation of the selected six-face polynomial three-cube with original inputs and independent structure time |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentNativeCell`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeCells`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeAttachments` | Full-target Laurent/polynomial cells and both entire native height-zero attachments through original source chart maps |
| `KTheory.Bass.StrictLaurentSeedStable` | Transparent `Track.SeedStableFactorization` and `SeedStableFormula` for an actual track and supplied seed |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeedStable` | Original supported and ambient seed factorizations through the actual cone inclusion |
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
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.QuasicoherentRepresentative` | `Quillen.PerfectComplexes.ProjectiveLine.exists_quasicoherent_model_of_perfect_plus` |
| `AlgebraicGeometry.PerfectComplexes.ProjectiveLine.IntrinsicPerfectPushforward` | `Quillen.PerfectComplexes.ProjectiveLine.exists_strict_model_of_perfect_plus`, `perfect_derivedProjection_of_perfect` |
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
The fine-to-graded seed square retains its original maps. The section-completion
owners below construct the original forward seeds, whole localization nulls
and transition equations, and literal finite-stage and telescope restriction
and cone maps.

### Constructed section completions

| Import after `Quillen.AlgebraicGeometry.PerfectComplexes.` | Principal interface |
| --- | --- |
| `Affine.FullOpenSectionBassRestrictionTower`, `Affine.FullOpenSectionBassRestrictionCofiber` | Original coarse-to-fine finite restriction and cofiber comparison |
| `Affine.FullOpenSectionBassLocalization` | Actual supported full-open telescope fiber and original signed boundary |
| `BoundedFlat.CoefficientOpenBassTower`, `BoundedFlat.CoefficientOpenBassTelescope` | Native finite and telescope restriction with the original transitions |
| `BoundedFlat.CoefficientFullOpenBassLocalization` | Global native supported full-open telescope fiber and signed boundary |
| `BoundedFlat.CoefficientSupportedOpenBassTower`, `BoundedFlat.CoefficientSupportedOpenBassTelescope` | Auxiliary-supported native finite and telescope restriction |
| `BoundedFlat.CoefficientSupportedFiberBassTelescope`, `BoundedFlat.CoefficientSupportedFullOpenBassLocalization` | Original auxiliary-supported fiber, fine completion comparison and signed boundary |

For open `j : U ⟶ Spec R` with compact `U`, the original coarse-to-fine section
completion restriction is stable in every integer degree. The supported
telescope maps to the actual full-open homotopy fiber through the same whole
localization null, preserving the original signed connecting map.

For a native open map `f : P ⟶ Q` in `Over (Spec R)`, final fine stability uses
qcqs `Q.left` and compact `P.left`; auxiliary support by `T : Q.left.Opens`
also requires compact `T`. These owners supply the corresponding constructed
coarse-to-fine restriction, supported fiber and signed boundary. The graded
Model definitions retain their own compactness conditions on `P.left` and
`Q.left`. No coefficient flatness or noetherian assumption is added.

The fine ambient completion for qcqs `P.left` has its original transition and
stage inclusion invertible in degree `d ≥ -i`:

| Import after `Quillen.AlgebraicGeometry.PerfectComplexes.` | Principal interface |
| --- | --- |
| `BoundedFlat.CoefficientBassFineRangeInvertibility` | `boundedFlatCoefficientAmbientBassTransition_isIso_of_le` |
| `BoundedFlat.CoefficientBassFineTelescopeComparison` | Original inclusion range and `boundedFlatCoefficientAmbientNegativeKTelescopeComparison` |
| `BoundedFlat.CoefficientBassConnectiveTelescopeComparison` | `boundedFlatCoefficientAmbientKTelescopeComparison` through original stage-zero evaluation/inclusion |
| `BoundedFlat.CoefficientSupportedNegativeBottomComparison`, `BoundedFlat.CoefficientSupportedNegativeForgetComparison` | Finite-bottom supported comparison and original forget square with only compact ambient scheme |
| `BoundedFlat.CoefficientSupportedFineRangeInvertibility`, `BoundedFlat.CoefficientSupportedFineTelescopeComparison`, `BoundedFlat.CoefficientSupportedConnectiveTelescopeComparison` | Supported range and original negative/connective fine-telescope isomorphisms; open immersion, compact removed open and qcqs ambient |
| `BoundedFlat.CoefficientSupportedNegativeTelescopeForget` | Original forget-support square and Laurent quotient through the actual inclusions |
| `BoundedFlat.CoefficientFullOpenBassRestriction` | Definitional full-open row/action/seed/telescope and cylinder-wise equality with original restriction |
| `Bass.SupportedLocalizationExactness`, `Bass.SupportedLocalizationBoundary` | Original nonpositive open-pair localization sequence and fixed fine connecting map; geometric positive boundary joins by exactness at literal K₀ |

These comparison maps retain the original recursive quotient and the actual
stage inclusions; the connective and negative supported maps at zero coincide.
The nonpositive localization sequence assumes compact removed open and qcqs
ambient. It does not identify the fine connecting map with the geometric
K₁-to-K₀ map, prove arbitrary-pair pullback naturality of that transported
boundary, or identify the original raw classical model.

The raw all-iterate and telescope comparisons and identification with classical
nonconnective K-theory remain open; completed geometric evaluation is separate. The
[perfect-complex guide](../topics/PerfectComplexes.md) and
[spectrum guide](../topics/SpectraAndBass.md) record these distinct endpoints.

## Ring plus and scalar extension

The selected public facade is `Quillen.KTheory.Plus`. Names below are relative
to `Quillen.FiniteProjectiveModule`.

| Import after `Quillen.` | Public names |
| --- | --- |
| `KTheory.Plus.StableGeneralLinearPlus` | `StableCompletion.stableZeroMap_isPlusConstruction` |
| `KTheory.Plus.ProjectiveCompletionZeroLoops` | `StableCompletion.zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence` |
| `KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv` | `completionToOriginalQLoopsHomotopyEquiv`, `originalQComparisonHomotopyEquiv`, `StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv` |
| `KTheory.Plus.ProjectiveCompletionLoopLabels` | Actual standard component and stage labels |
| `KTheory.Plus.ProjectiveCompletionLoopNaturality`, `KTheory.Plus.ProjectiveCompletionZeroLoopNaturality` | Actual ordinary naturality homotopies for the full and zero-component standard maps |
| `KTheory.Plus.ProjectiveOriginalPlusProduct` | `OriginalKZeroPlusProduct`, `originalPlusProductToQLoopsHomotopyEquiv`, `originalQLoopsPlusProductHomotopyEquiv` |
| `KTheory.Plus.ProjectiveOriginalPlusProductNaturality` | `originalPlusProductBaseChangeMap`, `originalPlusProductToQLoopsHomotopyEquiv_naturality` |
| `KTheory.Plus.ProjectiveCompletionPositiveKNaturality` | `StableCompletion.zeroCompletionPositiveKEquiv_baseChange` |
| `KTheory.Plus.ProjectiveCompletionZerothHomotopy` | `completionZerothHomotopyKZeroEquiv` and actual object-class naturality |
| `KTheory.Plus.ProjectiveTelescopeKZero` | `StableFreeRight.telescopeZerothHomotopyKZeroEquiv` and original stage classes |
| `KTheory.Map.RightBaseChange` | Original `rightBaseChangeExact.KMap` identity/composition laws |
| `Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | `rightBaseChangeUnit`, `rightBaseChangeHomEquiv`, `rightBaseChangeLift`, `rightBaseChange_existsUnique` |

The public standard comparison is one inner-loop reversal after the original
generic loop/fiber inverse. Its prescribed track reflects the inner loop
coordinate and retains the outer path direction. The actual comparison's
component label is `grade(input) - grade(basepoint)`; the zero-stage label is
`[P] - [rankOnePower n]`. Positive comparisons use the original loop-degree
shift and mapped-track transport, with no dimension-parity factor. See
[standard comparison normalization](StandardSignMigration.md).

The comparison homotopy equivalences retain those exact standard forward maps and the
original track. The product uses discrete original K₀ and the particular
`StableCompletion.ZeroComponent` certified by `stableZeroMap_isPlusConstruction`.
Its neutral slice, original classifier and standard labels are retained.
Ring change of the product-to-loop map is by ordinary homotopy with the
original K₀ and zero-completion maps. No natural chosen inverse, strictly
pointed naturality, H-space, A∞ or infinite-loop splitting is asserted.

The raw finite-free and idempotent-image scalar owners are
`Quillen.Aglib.LinearAlgebra.Matrix.RightScalarExtension` and
`Quillen.Aglib.Algebra.Category.ModuleCat.MatrixImageScalarExtension`. The literal
balanced tensor comparison, original unit/composition agreement, exactness
and all-degree K-map equality are proved in the focused tensor imports above.
Raw module and ring universes are independent; the original finite-projective
source remains `Category.{u, u}`, and mixed-ring-universe comparisons lift the
target explicitly. The original K-map and topological ring-change interfaces
retain their common-ring-universe bounds. The [plus guide](../topics/PlusConstruction.md)
records these scopes and the plus certificate's coefficient universe `u + 1`.
Automatic comparison and ordinary uniqueness on actual Hausdorff CW spaces for original
`IsPlusConstruction.{u,u,u}` certificates are now included. Common-universe
chain/certificate transport, CW subtype/ULift geometry and the mixed-universe
original-space assembly are also included. These results do not supply
arbitrary CW-homotopy-type transport or prescribed-track coherence.

## Classical CW plus comparisons and universe transport

| Import after `Quillen.` | Public interface |
| --- | --- |
| `Topology.PlusConstruction.ClassicalCWUniqueness` | `Quillen.IsPlusConstruction.exists_classicalCWComparison`, `classicalCWHomotopyCancel`, `homotopic_classicalCWComparisons`, `classicalCWPlusUnique` |
| `Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift` | `Quillen.IsPlusConstruction.exists_classicalCWComparison_commonUniverse`, `classicalCWHomotopyCancelCommonUniverse`, `homotopic_classicalCWComparisons_commonUniverse`, `classicalCWPlusUnique_commonUniverse`, `classicalCWPlusUnique_successor` |
| `Topology.PlusConstruction.UnivSubtype` | `Quillen.PlusConstruction.UnivSubtype.isPlusConstruction`, `liftPath_apply`, `kernel_lift`, `forward_down` |
| `Topology.PlusConstruction.ClassicalCWComparison`, `Topology.PlusConstruction.ClassicalCWComparisonUniqueness` | Chosen-cover existence and ordinary uniqueness, retaining the covers, points, surjectivity and pushout inputs |
| `Topology.CWComplex.Whitehead` | `Quillen.ClassicalCW.homotopyEquivOfWeakHomotopyEquivalence` with the exact original forward map |
| `Topology.CWComplex.SimplyConnectedCover` | `Quillen.ClassicalCW.exists_simplyConnected_cover` |
| `Topology.LocalCoefficients.CommonUniverseChains` | `Quillen.LocalCoefficients.CommonUniverseChains.liftMap`, `original_chainMap_retract_square`, `all_localCoefficients_liftMap` |
| `Topology.PlusConstruction.CommonUniverse` | `Quillen.PlusConstruction.CommonUniverse.isPlusConstruction`, `basedPiOneMap_square`, `kernel_lift`, `liftPath_down`, `forward_down` |
| `Topology.CWComplex.Subtype`, `Topology.CWComplex.ULift`, `Topology.CWComplex.UniverseTransport` | `Quillen.ClassicalCW.subtypeCWComplex`, `uliftCWComplex`, `uliftSubtypeCWComplex` and original-chart equations |

The automatic theorem takes actual Hausdorff CW subtypes in `Type u`, original
maps, points, tracks and subgroup, and original `IsPlusConstruction.{u,u,u}`
certificates. It constructs a comparison homotopy equivalence under the source
and proves ordinary homotopy uniqueness, with no supplied cover, lift, pushout
or desired equivalence. No finite-dimensional, countable or locally finite
restriction is added. The [classical CW guide](../topics/ClassicalCWPlus.md)
records the exact contract and distinct chosen-cover branch.

Common-universe transport needs the original coefficient quantifier already
in `U = max u v w`; it does not resize smaller coefficients into larger ones.
The included mixed-space assembly uses `U = max u v w z` for original ambient
universes `u`, `v`, `w`, and returns a comparison on the original `B`, `C`.
`classicalCWPlusUnique_successor` consumes literal original
`IsPlusConstruction.{u,u+1,u+1}` certificates. Its ordinary under-source
homotopy and ordinary uniqueness do not assert prescribed-track coherence;
actual Hausdorff CW hypotheses remain explicit.

## Homological and metric homotopy foundations

| Import after `Quillen.` | Interface |
| --- | --- |
| `Topology.HomotopyGroups.SphericalHomotopyAddition` | Genuine signed spherical addition in degree m+2 |
| `Topology.Realization.RelativeSphericalStraightening` | Full finite relative straightening with its specified fixed family |
| `Topology.LocalCoefficients.FirstObstruction` | Absolute first obstruction from lower homotopy and degree-n homology vanishing |
| `Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected` | Original integral homology isomorphisms imply complete weak equivalence for simply connected same-universe spaces |
| `Topology.MetricOrderComplex.RealizationHomotopyEquiv` | Vertex-fixed weak/metric realization and based-loop homotopy equivalences |
| `Topology.MetricOrderComplex.Equiconnection`, `Topology.MetricOrderComplex.LoopEquiconnection` | Actual metric connector and compact-open loop convex geometry |
| `Topology.Realization.OrderedNerveRealizationMap` | Actual nerve return map using nondegenerate interpolation and canonical-epi weight aggregation |
| `Topology.Realization.POUNerveClassifier` | Original partition-of-unity classifier into the weak realization |
| `Topology.Realization.NumerableRealizationDomination`, `Topology.Realization.MetricRealizationDomination` | Constructed realization domination from the displayed cover/connector data |
| `Topology.ClassifyingSpace.LoopDomination` | `RankedChainOrder.universalLoopDominationData` for original loops with independent categorical universes |
| `Topology.LocalCoefficients.TwistedWhiteheadSuppliedCovers` | Original base-map weak equivalence with supplied simply connected covers and commuting lift |
| `Topology.Covering.PathClassPrebundle`, `Topology.Covering.LocalConnectorHypotheses` | Actual surjective path-class cover from original local geometry |
| `Topology.Covering.PathClassEndpoint`, `Topology.Covering.PathClassSimplyConnected` | Exact path-class endpoint equation and genuinely simply connected chart-topologized total |
| `Topology.Covering.HomotopyPullbackTransfer`, `Topology.Covering.LocalConnectorTransfer` | Actual pullback cover transfer under the displayed homotopy equivalence |
| `Topology.ClassifyingSpace.SimplyConnectedCover` | Constructed simply connected cover of an original path-connected categorical realization |
| `Topology.Realization.Whitehead` | Exact-forward homotopy equivalence for weak equivalences between actual simplicial realizations |

The [foundations guide](../topics/HomotopyFoundations.md) keeps the degree
ranges, coefficients, spaces and maps explicit. Raw ordered interpolation
has face/mono coherence; degeneracies are handled by summing repeated weights
through the canonical epimorphism before interpolation in the actual return
map. The constructed domination supplies the original-Q comparison bridge,
without an additional assumed inverse.

Supplied-cover twisted Whitehead retains all four spaces and coefficient
systems in universe `u`, actual simply connected total spaces, a commuting
lift and a fundamental-group isomorphism. The included path-class
endpoint/universality theorem now proves simple connectedness of its actual
prebundle total under path connectedness, local path connectedness and the
displayed ambient-thin neighborhoods. Actual connected Hausdorff CW geometry
supplies these inputs. Separate supplied-cover interfaces keep their explicit
hypotheses. The original-Q homotopy equivalence and product retain the actual standard maps.

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
| Homological and metric foundations | [HomologicalWhiteheadSimplyConnected](../../examples/downstream/Consumer/HomologicalWhiteheadSimplyConnected.lean), [MetricOrderLoops](../../examples/downstream/Consumer/MetricOrderLoops.lean), [NumerableDomination](../../examples/downstream/Consumer/NumerableDomination.lean) |
| Supplied covers and path-class covering | [TwistedWhiteheadSuppliedCovers](../../examples/downstream/Consumer/TwistedWhiteheadSuppliedCovers.lean), [PathClassCovering](../../examples/downstream/Consumer/PathClassCovering.lean), [PathClassUniversality](../../examples/downstream/Consumer/PathClassUniversality.lean) |
| Actual CW plus comparisons | [ClassicalCWPlusAutomatic](../../examples/downstream/Consumer/ClassicalCWPlusAutomatic.lean), [ClassicalCWPlus](../../examples/downstream/Consumer/ClassicalCWPlus.lean), [ClassicalCWPlusMixedUniverse](../../examples/downstream/Consumer/ClassicalCWPlusMixedUniverse.lean) |
| Actual CW covers and universe transport | [CWSimplyConnectedCover](../../examples/downstream/Consumer/CWSimplyConnectedCover.lean), [CommonUniversePlus](../../examples/downstream/Consumer/CommonUniversePlus.lean), [CWUniverseTransport](../../examples/downstream/Consumer/CWUniverseTransport.lean) |
| Standard-sign and original plus product | [StandardSignMigration](../../examples/downstream/Consumer/StandardSignMigration.lean), [OriginalQLoopHomotopyEquiv](../../examples/downstream/Consumer/OriginalQLoopHomotopyEquiv.lean), [OriginalPlusProduct](../../examples/downstream/Consumer/OriginalPlusProduct.lean) |
| Full-open graded stable concentration | [FullOpenGradedSectionStable](../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean) |

The maintained [tests](../../QuillenTest) cover further constructions and regressions.
Neither tests nor clients are dependencies of library source.
[Scope](Scope.md#verification) and
[architecture](../development/Architecture.md#trust-checks) describe the build
and foundation-audit boundary.
