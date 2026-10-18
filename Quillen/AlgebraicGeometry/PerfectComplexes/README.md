# Perfect-complex K-theory

Strict-perfect and locally perfect complexes have different models and comparison hypotheses. The guides below keep their actual maps, degree-zero image statements, and completion boundaries. Mathematical exposition and APIs live beside their source families.

## Family guides

- [Localization and model comparison](Localization.md)
- [Auxiliary support and Mayer–Vietoris](SupportedOpen/README.md)
- [Projective-line K-equivalences](ProjectiveLine/README.md)
- [Affine and graded objects](Affine/README.md)
- [Bounded-flat section comparisons](BoundedFlat/BassComparison.md)
- [Scheme Bass groups](Bass/README.md)
- [Classical comparison boundaries](Development.md)

## Objects and conventions

The library provides connective K-theory of strict and locally perfect
complexes, vector-bundle comparisons, derived pullback, localization, support
excision, and Mayer–Vietoris. The original restriction maps and relative
homotopy-fiber boundaries remain the public maps. Localization has an exact
image endpoint in degree zero. Separate functorial Bass groups are defined by
cokernel recursion. For a quasi-compact open of a qcqs scheme, these original
nonpositive groups now have a recurring localization sequence transported
from the same-null fine completion; its maps and boundary are described below.

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

- Complete the Laurent-unit connecting-map and zero-section class formulas and retain possible Nil contributions; the normalized forward scalar K₁ comparison is proved.

- Extend the proved fine ambient/supported range and original-group identifications through the remaining auxiliary-support tower comparisons. Existing support-enlargement maps must be identified with the actual T, T∪U and T∩U section towers and their exact localization maps.

- Identify the native current-stage telescope objects and selected null diagram with the intended classical nonconnective theory. The actual iterated-seed/current-stage zigzag, geometric action equivariance, whole geometric chi factorization and fixed-word seed squares are supplied; equality of the two different transition definitions is not used by that route.

- Complete any separately required comparison with the older raw geometric cell tower and identify the classical groups and signed localization boundary. The raw overlap O four-cube belongs to that separate route and is not a premise of the native current-stage theorem. The original nonpositive groups already have the same-null fine localization sequence above. Its equality with the geometric boundary, arbitrary-pair boundary naturality, the Laurent [T] terminal formula and O/O(-1) sign, classical Laurent splitting and nonconnective descent remain open; retain possible Nil terms.

- Identify the separate natural projected-diagonal endpoint comparisons and establish the general projective-bundle formula, Proj identification, and full twisting-sheaf family. Both actual native qcqs inverse laws and geometric G identification are proved, and the compact-open supported Phi bijection retains its original forward map. Intrinsic-perfect native projection perfection, original open K-map naturality and exact coefficient/support preservation hold on every quasi-compact base. Arbitrary-base-map naturality remains separate. The older finite-coefficient retract criterion retains its own uniform-window premises.

- Extend perfect preservation to the claimed general-source/unbounded direct-image scope, and establish general bounded-below flat-base-change invertibility beyond the available QC-single and open specializations.

- Extend strict/local equivalence to arbitrary nonaffine schemes and perfect pullback to arbitrary non-quasi-compact schemes; compare the Waldhausen and triangulated-derived Grothendieck presentations.

- Supply any needed general stable cofiber excision, replacement cofiber preservation, and higher raw-spectrum/telescope coherence. The categorical stable localization has no asserted standard stable model structure or triangulation.

The broader comparison boundaries are in [scope summary](../../../docs/SCOPE.md).

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
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope`, `GlobalSupportedTelescope`, `GlobalOpenTelescope` | Stable finite/telescope restriction preserving actual `B^i(seed)` transitions and cylinder faces |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionCoarseFiber`, `GlobalSectionFullOpenFiber` | Actual same-null coarse/full-open `fiberMap`, its restriction equation and all-integer stability |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull`, `ParameterFullFiberComparison`, `ParameterIteratedTwistedFiber` | Original full-open null and `currentLift`, `normalizedLift`, `twistedLift`; same-null stability equivalences |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullFiber`, `ParameterCurrentFullFiber` | `Quillen.PerfectComplexes.ParameterFullCurrentNull.iteratedLift_spec_isStableEquivalence`, `currentLift_integer_isStableEquivalence` and `currentLift_integer_signed_isIso` |
| `AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIdentityModels` | Original projection Model isomorphisms at the integer parameter, with support-forgetting and full-restriction squares |
