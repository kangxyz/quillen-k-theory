# Perfect-complex K-theory

Strict-perfect and locally perfect complexes have different models and comparison hypotheses. The guides below keep their actual maps, degree-zero image statements, and completion boundaries. Mathematical exposition and APIs live beside their source families.

## Family guides

- [Localization and model comparison](Localization.md)
- [Auxiliary support and Mayer–Vietoris](SupportedOpen/README.md)
- [Projective-line K-equivalences](ProjectiveLine/README.md)
- [Affine and graded objects](Affine/README.md)
- [Bounded-flat sections, finite groups and localization](BoundedFlat/BassComparison.md)
- [Original raw Bass evaluation and coherence](BoundedFlat/RawEvaluation.md)
- [Original classes and geometric connecting maps](BoundedFlat/GeometricBoundary.md)
- [Scheme Bass groups](Bass/README.md)
- [Classical comparison boundaries](Development.md)

## Objects and conventions

The library provides connective K-theory of strict and locally perfect
complexes, vector-bundle comparisons, derived pullback, localization, support
excision, and Mayer–Vietoris. The original restriction maps and relative
homotopy-fiber boundaries remain the public maps. Localization has an exact
image endpoint in degree zero. Separate functorial Bass groups are defined by
cokernel recursion. For a quasi-compact open of a qcqs scheme, the original
nonpositive groups have a recurring localization sequence from the same-null
fine completion. Their independently defined current and normalized-row
classes preserve that original negative boundary. In nonnegative target
degrees the stable boundary on the unchanged perfect classes is the negative
of the original geometric connecting map, including K₁ to supported K₀.
The [connecting-map guide](BoundedFlat/GeometricBoundary.md) keeps the exact
class maps, degree casts and auxiliary-support hypotheses.

This guide owns the perfect objects, supported/relative models, and their
connective geometric localization comparisons. The generic spectrum and
Bass-recursion interfaces are in [spectral and Bass interfaces](../../KTheory/Bass/README.md);
scheme K/G and generic sheaf geometry are in [scheme K/G guide](../Scheme/README.md).
The original current-stage full-open lift has an all-integer stable localization theorem in the [bounded-flat comparison guide](BoundedFlat/BassComparison.md#native-current-stage-full-open-localization). Identification with classical
Thomason–Trobaugh localization retains the boundary in
[classical comparison boundaries](Development.md).
The K-theory declarations below belong to `Quillen.PerfectComplexes` unless another
namespace is specified. Their source is under
`Quillen.AlgebraicGeometry.PerfectComplexes`. The general sheaf-complex interfaces
come from Aglib's `AlgebraicGeometry.Scheme.Modules.Complex` namespace.

## Complexes and support

For `X : AlgebraicGeometry.Scheme.{u}`, the ambient category is
`CochainComplex X.Modules ℤ`. In the Aglib namespace, `strictPerfect X` requires
globally bounded terms, each finite locally free. `StrictPerfect X` is the
corresponding full category.

The standard native `DerivedCategory X.Modules` localizes complexes at
quasi-isomorphisms. `locallyPerfect X` requires an isomorphism in that localization,
near each point, to a strict perfect complex on the neighborhood. `Perfect X` is
the full category of cochain complexes and chain maps satisfying this property.
These complexes need not be termwise quasi-coherent or globally bounded.
See Aglib's [Strict.lean](https://github.com/kangxyz/aglib/blob/40af743ab794d607f566cec0c5417d8e4d02a735/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean) and
[Local.lean](https://github.com/kangxyz/aglib/blob/40af743ab794d607f566cec0c5417d8e4d02a735/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Local.lean).

`StrictK X n` and `PerfectK X n`, for `n : ℕ`, are the connective S-construction
groups in `Type (u + 1)`. Their ambient-monomorphism cofibrations have quotients
in the specified class. `splitStrictKEquiv` and `splitPerfectKEquiv` compare
these with degreewise split cofibrations, retaining quasi-isomorphisms as weak
equivalences.

For an open immersion `j : U ⟶ X`, a supported perfect complex is acyclic after
restriction to `U`. `PerfectSupportedK j n` is its K-group, and
`perfectSupportedKMap j n` forgets support.
See [PerfectSupport.lean](PerfectSupport.lean).

## Remaining obligations

The following comparison targets remain separate from the constructed
strict/fine/current/normalized interfaces.

- Identify the specified classical raw spectrum, forward Laurent cup/boundary
  transitions and whole localization null diagram through all required
  ambient, open and auxiliary-supported stages. The current-stage and
  normalized-row lifts already have internal same-null localization,
  original negative-class comparisons and signed positive geometric formulas.
  Their full classical correspondence is the additional target.
- Complete the raw cone/step composition cube and higher compatibility of
  the chosen input-null, identity and composition data. Whole one-step
  evaluation naturality, the initial mixed seed relative comparison, raw map
  identity, prescribed transition-identity square and polynomial-span
  composition are constructed. The supported raw first stage has its actual
  objectwise rows and seeds; raw row maps and the full localization-null
  comparison remain separate. The coefficient overlap-cell and coherent
  all-stage producer retain their own attachment obligations.
- Compute the original Laurent `[T]` terminal operation and the actual
  O/O(-1) zero-locus class under the same native Phi inverse. A natural section
  must retain its proved sign. Keep possible Nil terms; classical Laurent
  splitting, homotopy invariance and nonconnective descent are separate.
- Identify the separate projected-diagonal endpoints and establish the general
  projective-bundle formula, Proj identification and full twisting-sheaf
  family. Both native qcqs inverse laws, geometric G identification and the
  compact-open supported Phi bijection retain their original maps. Intrinsic
  projection perfection and original open K-map naturality hold over
  quasi-compact bases; arbitrary-base-map naturality remains separate. The
  older finite-coefficient retract criterion keeps its uniform-window input.
- Extend perfect preservation to the claimed general-source/unbounded
  direct-image scope and general bounded-below flat-base-change invertibility
  beyond the available QC-single and open specializations.
- Extend strict/local equivalence to arbitrary nonaffine schemes and perfect
  pullback to arbitrary non-quasi-compact schemes; compare Waldhausen and
  triangulated-derived Grothendieck presentations.
- Supply any separately required general stable cofiber excision, replacement
  cofiber preservation and higher raw-spectrum coherence. The categorical
  stable localization has no asserted standard stable model structure or
  triangulation.

[Classical comparison boundaries](Development.md) fixes the target and its
source locators. The [cross-family scope summary](../../../docs/SCOPE.md)
links the other source owners.

## Source interfaces

| Source / interface | Description |
| --- | --- |
| `Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization` | Perfect localization for quasi-compact opens of qcqs schemes |
| `Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris` | Connective two-open sequence and matching K₀-class gluing |
| `Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups` | Scheme Bass groups from perfect K₀ |
| `AlgebraicGeometry.PerfectComplexes.GrothendieckComparison` | `PerfectComplexes.perfectGrothendieckKZeroEquiv` |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassActualSeedComparison` | Constructed whole seed square on the original two-chart pushout |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedIteration` | Objectwise first-to-second Bass map with literal inclusion, cylinder and loop-coordinate formulas |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeCube`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCubeConsumers` | Actual six-face original identity cube and whole comparison/cone/step identities |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingNative` | Native evaluation of the selected six-face polynomial three-cube with original inputs and independent structure time |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentNativeCell`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeCells`, `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeAttachments` | Full-target Laurent/polynomial cells and both entire native height-zero attachments through original source chart maps |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeedStable` | Original supported and ambient seed factorizations through the actual cone inclusion |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison` | Actual full-open section K and perfect-K comparison |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModel` | Original strict chosen-zero restriction Model map |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionChangeIndex`, `GlobalSectionChangeIndexLaws`, `GlobalSectionUnit`, `GlobalSectionLaurentAction` | Actual all-scheme `globalModel`, coefficient restriction, literal evaluation and original forward units |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedModels`, `GlobalOpenModels`, `GlobalFullOpenModels` | Actual supported/coarse/fine global rows, same zero and exact restriction squares |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEmptySupportedModels`, `GlobalEmptySupportedParameterModels` | Empty-open support forgetting is a Model isomorphism preserving the section, zero, products, pair pullbacks, forward unit and tracks |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope`, `GlobalSupportedTelescope`, `GlobalOpenTelescope` | Stable finite/telescope restriction preserving actual `B^i(seed)` transitions and cylinder faces |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionCoarseFiber`, `GlobalSectionFullOpenFiber` | Actual same-null coarse/full-open `fiberMap`, its restriction equation and all-integer stability |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull`, `ParameterFullFiberComparison`, `ParameterIteratedTwistedFiber` | Original full-open null and `currentLift`, `normalizedLift`, `twistedLift`; same-null stability equivalences |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullFiber`, `ParameterCurrentFullFiber` | `Quillen.PerfectComplexes.ParameterFullCurrentNull.iteratedLift_spec_isStableEquivalence`, `currentLift_integer_isStableEquivalence` and `currentLift_integer_signed_isIso` |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIdentityModels` | Original projection Model isomorphisms at the integer parameter, with support-forgetting and full-restriction squares |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps`, `ParameterAuxiliaryCurrentFiber`, `ParameterAuxiliaryCurrentLocalization` | Actual union/auxiliary/inverse-open rows, original maps and whole null; all-signed current lift under compact P,Q,T and quasi-separated Q |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowLocalization`, `ParameterNormalizedBasicLocalization` | Independent normalized-row path-space lifts, maps, nulls and stable localization with their original compact-open hypotheses |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFinePerfectConnecting`, `CoefficientAuxiliaryFinePerfectConnecting` | Single-minus geometric boundary formulas on every original perfect class, including K₁ to supported K₀ |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicOriginalBoundary`, `ParameterAuxiliaryNormalizedRowBoundary` | Original negative groups and degree casts in intrinsic normalized-row boundary squares |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNaturality`, `GlobalRawBassInputIdentitySeedSquare` | Whole raw one-step evaluation naturality and the prescribed transition-identity square |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedNaturality` | Relative comparison of the two original mixed input/evaluation/seed routes, with complete carrier faces and joins |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionSpan` | Whole polynomial-span composition with original terminal chart pauses; no cone/step composition law inferred |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawGeometry`, `GlobalSupportedRawRows`, `GlobalSupportedRawStep` | Actual qc-ambient open-pair charts and objectwise parameter-looped cones/seeds; the complete three-row wrappers require compact source and ambient, without compact auxiliary open or quasi-separatedness |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputWeakZero`, `GlobalBassEvaluationInputWeakZeroProduct` | Original directed weak-zero localization null and target-isomorphism postcomposition, with whole native recovery |

## The originally chosen supported binary surface

[GlobalSupportedRawInputBinarySurface](BoundedFlat/GlobalSupportedRawInputBinarySurface.lean)
identifies the finite normalization simplex with the exact originally selected
`compositionComparison` at every level, both independent scalar times and every
original input. `InputBinary.relative_native_value` uses the generic
`surfaceValue` interface, whose `surfaceValue_eq_level` theorem recovers the
original level evaluation. Its first and last comparison faces are the original
normalized-composite and split-composition tracks. This binary identification
does not supply the remaining higher overlap or coherent iteration fillers.

The [actual source-projection endpoint attachment](BoundedFlat/ProjectionEndpoints.md)
identifies both complete chosen corrected chart squares with the corresponding
global overlap scalar endpoints, preserving their original interiors and clocks.
