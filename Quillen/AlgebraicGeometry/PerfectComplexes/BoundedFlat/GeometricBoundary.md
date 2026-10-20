# Original classes and geometric connecting maps

The section, current-stage and normalized-row constructions have their own
maps, whole nulls and intrinsic stable boundaries. This guide records how
their original perfect and negative classes compare. In nonnegative target
degrees the fixed original class maps give an explicit minus sign between
the stable boundary and the geometric Waldhausen boundary. The original
negative-class squares use their separately defined localization boundary.
These conclusions retain their conventions; they do not constitute a
single all-integer comparison with the separately prescribed raw spectrum.
The [tensor-generated realization](TensorBassConstruction.md) directly proves
original TT 7.4 using the actual support maps and whole acyclicity null.
That theorem does not require equality with an independently prescribed
boundary presentation. The extra class and boundary comparisons below keep
their stated maps, signs and domains.

## Degrees, classes and the original null

Write `H_d(E)` for `stableHomotopyGroup E d`, with `d : ℤ`. Original
Waldhausen K-groups use `n : ℕ` and multiplicative notation; their stable
class maps pass through `Additive.ofMul`. A boundary from degree `n+1` to
degree `n` retains the cast

```text
κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1.
```

The cast is part of the square, including when `n = 0`.
[LevelOneConnectingComparison](../../../Waldhausen/Fibration/LevelOneConnectingComparison.lean)
and [StableConnectingComparison](../../../Waldhausen/Fibration/StableConnectingComparison.lean)
keep the original canonical fiber map and complete acyclic null.
`originalKStableEquiv_connecting_sign` compares
`changeWeakConnectingHom` with `stableFiberConnecting` with one minus sign.
`originalKStableEquiv_liftConnecting_sign` gives the same convention for
`stableFiberLiftConnecting` of the actual arrows and specified null. The
comparison assumes weakness of the original canonical fiber map. The
minus comes from the original level-one stabilization and loop transpose,
without changing either boundary or inserting a degree-dependent class twist.

## Canonical weak-zero and homotopy null comparison

The auxiliary localization null is the reversal of the actual objectwise
weak transformation `ParameterAuxiliarySupport.zeroToFull`. The construction
requires objectwise weakness; it assumes no isomorphism from zero to the
composite.
[GlobalBassEvaluationInputWeakZero](GlobalBassEvaluationInputWeakZero.lean)
keeps this directed edge separate from the full isomorphism-reference
nodes. For an open immersion, arbitrary auxiliary open and scheme
parameter, `InputWeakZero.null_native` and `family_null` recover the entire
original `fullNull`, including its clock and level-zero loop coordinate.
The old finite normalization simplex survives as a whole face. The
specified affine cone is based and structure-compatible with independent
height and normalization coordinates. Its null-slice coefficient and
Laurent equations do not assert whole-family naturality for independently
chosen normalization nodes.

[GlobalBassEvaluationInputWeakZeroProduct](GlobalBassEvaluationInputWeakZeroProduct.lean)
postcomposes that original null with a supplied independently varying
target isomorphism-reference family. `InputWeakZeroProduct.native` uses
the actual realization-grid parameter, preserving both native parameters
and the separate structure time. The weak first coordinate is monotone;
only the isomorphism second coordinate can reset along the grid. The
construction never inverts the weak transformation. It supplies neither
a weak-by-weak product nor arbitrary source-normalization precomposition,
and it does not identify the realization-product interior with the
separately selected affine cone.

For homotopy-commuting diagrams, the generic
[FiberLiftHomotopyNaturality](../../../Topology/Prespectrum/FiberLiftHomotopyNaturality.lean)
retains explicit nulls `N : f ≫ r ~ 0` and `N' : f' ≫ r' ~ 0` for
`f : S ⟶ A`, `r : A ⟶ O` and their primed counterparts. With comparisons
`s : S ⟶ S'`, `a : A ⟶ A'`, `o : O ⟶ O'`, its arrow homotopies are
`Hf : f ≫ a ~ s ≫ f'` and `Hr : a ≫ r' ~ r ≫ o`.
It additionally takes a whole null square `Q`: the prescribed second-arrow
track followed by the postcomposed `N` is compared with the precomposed
`N'`, along `Hf` followed by `r'` and the constant zero edge.

`homotopyFiberLiftNaturalityHomotopy` has exactly `Hf` as its first
coordinate and `Q` as its fiber-path coordinate. The four complete edge
equations, joint continuity, basedness and structure compatibility are
part of `Q`; comparison, null-path and structure times remain independent.
Three stable comparisons transport stability of the specified lifts.
`stableFiberLiftConnecting_homotopySquare` gives their original signed
boundary equation in degree `d : ℤ`, assuming the two actual lifts are
invertible in that degree. Writing `δ_d, δ'_d` for those boundaries, it is
`δ_d ≫ H_d(s) = H_(d+1)(o) ≫ δ'_d`, with `H_d` also denoting the induced
map on stable groups. The construction neither chooses replacement inverse
tracks nor constructs an application-specific null square.

The finite weak-zero recipes recover the canonical localization null at
their Model interface. A comparison with the supported raw cones and
seeds still requires the actual whole row-null square, including any
finite-stage and telescope-cylinder equations. Equality of induced stable
maps, scalar carrier extension or the objectwise Bass `sourceNull` does
not supply that square.

## Basic positive geometric boundary

Fix `R : CommRingCat.{u}`, `P,Q : Over (Spec R)` and `f : P ⟶ Q` with
`[IsOpenImmersion f.left]`. The actual support-to-acyclic, ambient and coarse
evaluation Model arrows in
[CoefficientSupportEvaluationNull](CoefficientSupportEvaluationNull.lean)
preserve the chosen zeros, both localization arrows and every null time.
`CoefficientEvaluationKStable` and `CoefficientSupportEvaluationClasses`
retain the original K-equivalences and their stable class maps.

`CoefficientInitialEvaluationConnecting` transports the intrinsic initial
boundary through that actual evaluation square.
[CoefficientInitialConnectingSign](CoefficientInitialConnectingSign.lean)
then gives its negative geometric sign in every nonnegative target degree.
`CoefficientSupportAcyclicKComparison`,
`CoefficientInitialSupportedConnecting` and
`CoefficientInitialPerfectConnecting` pass through the genuine supported
evaluation and original bounded-flat inclusion. The comparisons retain
`perfectAcyclicSupportedKEquiv` and the original relative-to-full-open
equation `qcqsPerfectConnectingHom_comp_relative`.
`CoefficientInitialTelescopeConnecting` preserves the whole original null
under stage-zero inclusion and coarse-to-full-open restriction.

Assume also compact `P.left`, compact `Q.left` and quasi-separated `Q.left`.
For every `a : Under R`, `n : ℕ`, and
`x : PerfectK (space (op P, a)) (n+1)`,
[CoefficientFinePerfectConnecting](CoefficientFinePerfectConnecting.lean)
proves `boundedFlatCoefficientFineConnecting_perfectClass_sign`. If
`c_open` and `c_support` denote its original perfect evaluation followed
by stage-zero inclusion, the equation is

```text
δ_fine,n (cast_κ (c_open,n+1 x))
  = - c_support,n (qcqsPerfectConnectingHom (schemeMap f a) n x).
```

Both class maps are the original ones in the theorem. The source class is
formed before its degree cast. Positive cofinality of actual restriction
supplies representatives for every open perfect class, including the
K₁-to-supported-K₀ case. The theorem does not assume this signed equality
as an endpoint comparison.

[ParameterNormalizedBasicPositiveBoundary](ParameterNormalizedBasicPositiveBoundary.lean)
transports this formula through the actual normalized-to-fine boundary
square. Its `basicConnecting_originalPerfectClass_sign` specializes to
`U.ι` for compact `U : Q.Opens` and compact quasi-separated `Q`, retaining
both original `identityPairIso` perfect pullbacks. The normalized Model-class
formula and vanishing on actual ambient restriction use the same convention.

## Auxiliary support and positive geometric boundary

For the same `f` and `T : Q.left.Opens`, the auxiliary three objects are
supported complexes acyclic on the union open, on `T`, and on its inverse
image in `P`, respectively. Their maps are original support enlargement and
restriction. The geometric connecting map starts at
`PerfectSupportedK (f.left ⁻¹ᵁ T).ι (n+1)` and ends at the union-supported
K-group in degree `n`. This fixes the meaning of support before comparison.

`CoefficientAuxiliaryEvaluationNull` exposes the actual acyclic conversion
and AsSmall maps with both arrows and all null times.
`CoefficientSupportedNativeFibration` proves the native canonical fiber map
weak from the original supported joint data and exact evaluation.
`CoefficientAuxiliaryInitialConnecting` and
`CoefficientAuxiliaryInitialConnectingSign` give the intrinsic square and
its single minus on each native K-class. These initial interfaces need no
compactness. Their telescope comparison in
`CoefficientAuxiliaryInitialTelescopeConnecting` requires compact `P.left`,
`Q.left`, `T`, and quasi-separated `Q.left`.

The selected zero of the native AsSmall comparison is retained.
`Waldhausen.SmallModel.Connecting`,
`CoefficientAuxiliaryAcyclicEvaluation` and
`CoefficientAuxiliaryConnectingEvaluation` compare the independent geometric
zero by actual exact evaluation and the genuine small-model K-equivalence.
They identify the native connecting map with
`boundedFlatPerfectSupportedOpenConnectingHom` using original forward and
inverse section K-equivalences, without a new zero-equality premise.

`CoefficientAuxiliaryNativeClasses`,
`CoefficientAuxiliaryInitialSupportedConnecting` and
`CoefficientAuxiliaryInitialPerfectConnecting` retain the actual fiber map,
perfect inclusion and positive cofinality. The initial supported comparison
needs no compactness; its perfect comparison needs compact `Q.left`.
[CoefficientAuxiliaryFinePerfectConnecting](CoefficientAuxiliaryFinePerfectConnecting.lean)
gives the fine endpoint when `P.left`, `Q.left`, `T` are compact and `Q.left`
is quasi-separated. Its `perfectClass_sign` equation is

```text
δ_aux,n (cast_κ (c_open,n+1 x))
  = - c_union,n (qcqsPerfectSupportedConnectingHom
      (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) _ n x).
```

The original source is supported on the inverse-image vanishing open and
the target on the union vanishing open. Both stage-zero classes and `κ`
are explicit, also for K₁ to union-supported K₀.

`CoefficientAuxiliaryPerfectBoundaryProjection` proves naturality of this
geometric boundary under the actual coefficient-projection support pairs,
using `schemeMap_projection`, `supportedPairTargetSquare` and
`supportedPairUnionSquare`.
[ParameterAuxiliaryNormalizedRowOriginalPositiveBoundary](ParameterAuxiliaryNormalizedRowOriginalPositiveBoundary.lean)
therefore retains arbitrary original Over/f endpoints and both original
projection pullbacks. Its identity specialization uses a scheme `X`,
compact opens `U,T`, compact quasi-separated `X`, and the original
`qcqsPerfectSupportedConnectingHom U.ι T _ n`. The explicit minus and every
nonnegative target degree remain in the conclusion.

## Original negative classes and boundaries

The original negative groups are the existing Bass recursion from perfect
K₀; their index `i : ℕ` denotes degree `-i`. Each fine class is the unchanged
finite-bottom comparison followed by the original stage-`i` inclusion.
The current class is independently defined from its actual finite stage.
The [finite sign comparison](../../../KTheory/Bass/SignComparisons.md#original-ambient-and-supported-negative-classes)
shows their correction is identity in every index: the geometric word and
loop reversal each contribute `(-1)^(i.choose 2)`.

[ParameterCurrentNegativeBoundaryCorrection](ParameterCurrentNegativeBoundaryCorrection.lean)
retains the current intrinsic boundary and its integer-degree transport.
[ParameterCurrentNegativeBoundarySign](ParameterCurrentNegativeBoundarySign.lean)
cancels both actual corrections to obtain
`currentNegativeConnecting_eq_original`, with the original restriction and
support-forget maps in its exactness statements. The hypotheses are the
open immersion, compact source and target, and quasi-separated target.
[ParameterCurrentFirstBoundary](ParameterCurrentFirstBoundary.lean)
separately retains the K₀-to-first-negative case through its original
degree-zero class and degree cast.

`ParameterAuxiliaryNegativeClasses` uses the original finite comparisons,
actual auxiliary finite maps and fine inclusions for all three rows.
`ParameterAuxiliaryNegativeSign` proves their current-to-fine class squares
in every index. `ParameterAuxiliaryNegativeBoundarySign` then compares the
independent intrinsic and fine boundary composites, with both class maps
and `negativeLocalizationDegreeIso`. The full boundary comparison requires
compact source, target and auxiliary open and quasi-separated target.

## Independent normalized classes and the basic row

`SchemeModelRowNormalizedClasses.normalizedStageInclusion` is defined from
the actual row comparison and telescope inclusion. Its finite inclusion
equation precedes its `normalizedModelClass`; the latter keeps every
nonnegative degree, including zero.
`ParameterSupportedNormalizedRowClasses.normalizedRowNegativeClass` likewise
uses the unchanged negative finite comparison and independent normalized
inclusion, without defining a class through a telescope inverse.

`ParameterAuxiliaryNormalizedRowConnecting` forms
`normalizedPresentationConnecting` from the normalized row's own
restriction, enlargement and whole null.
`ParameterAuxiliaryNormalizedRowBoundaryComparison` compares that intrinsic
boundary with the fine one in every integer degree.
`ParameterAuxiliaryNormalizedRowClasses` and
[ParameterAuxiliaryNormalizedRowBoundary](ParameterAuxiliaryNormalizedRowBoundary.lean)
retain the independent negative classes and their original integer cast.
`ParameterAuxiliaryNormalizedRowPerfectClasses` supplies stage-zero perfect
class equations: the fiber and ambient equations need only compact target,
and the open equation only compact source. The full auxiliary boundary
keeps compact source, target and auxiliary open and quasi-separated target.

For an empty open source, every ordinary cochain complex on that source
is acyclic. [GlobalEmptySupportedModels](GlobalEmptySupportedModels.lean)
therefore makes the original support-forgetful map a Model isomorphism with
a section-preserving exact inverse and the same zero.
`GlobalEmptySupportedParameterModels` retains the actual product/pair
pullbacks, forward unit and whole tracks in both directions.
`ParameterNormalizedRowForget` transports this actual map to the normalized
row. `ParameterNormalizedRowNegativeForget` keeps
`supportedNegativeKForgetNat` on the independent finite classes with only
compactness of the target; ambient class invertibility additionally uses
the qcqs hypothesis.

`ParameterAuxiliaryBasicNull` identifies the original basic composite with
ambient product pullback and proves equality of the selected nulls at
every unchanged time. `ParameterNormalizedBasicDiagram` then defines its
support-forget and restriction arrows and `basicNull`, with an explicit
union-open object cast.
`ParameterNormalizedBasicLocalization` constructs `basicLift` and
`basicConnecting` from those maps. At the integer parameter the lift is
stable for compact quasi-separated `Q` and compact `U : Q.Opens`.
`ParameterNormalizedBasicCurrentBoundary` and
`ParameterNormalizedBasicFineComparison` preserve the original whole null
and identify their independently defined boundaries.

[ParameterNormalizedBasicOriginalBoundary](ParameterNormalizedBasicOriginalBoundary.lean)
exports `basicConnecting_original_negative_square`. It retains
`identityOpenGroupIso`, `identitySupportGroupIso`, the independent
normalized finite classes and `negativeLocalizationDegreeIso`, and uses the
existing absolute `supportedNegativeLocalizationConnecting` in every index.
Its assumptions are precisely compact quasi-separated `Q` and compact `U`.
The positive geometric formula above and this original negative square have
different stated domains and conventions; joining their ranges does not
construct the additional comparison with the prescribed raw spectrum,
transitions and whole null. That comparison is separate from the direct
TT 7.4 localization theorem.

Source and validation identities belong to the
[evidence registry](../../../../docs/evidence/README.md#tt-source-and-validation-records).
