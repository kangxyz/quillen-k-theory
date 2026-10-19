# Original raw Bass evaluation

Evaluation of cocartesian bounded-flat sections compares a strict section
diagram with the original geometric pullback construction. The comparison
retains the chosen zeros, geometric composition tracks, source nulls and
forward Laurent units. This guide distinguishes the coefficient construction
over `Spec R` from the integer-base construction on arbitrary schemes. The
[section-completion guide](BassComparison.md) owns the strict towers and their
stable localization; [classical comparison boundaries](../Development.md)
owns the remaining correspondence with the specified classical theory.

## Coefficient one-step evaluation

Fix `R : CommRingCat.{u}`, `P : Over (Spec R)` and `a : Under R`. The
bounded-flat fiber has morphisms in universe `u`; its cocartesian section
category has morphisms in `u + 1`. Evaluation and its common-universe lift
keep their actual forward functors. Exact categorical equivalence alone is
insufficient to replace their geometric naturality tracks by equalities.

[CoefficientSectionEvaluationComposition](CoefficientSectionEvaluationComposition.lean)
compares the original evaluation maps, section reindexing, geometric pullback
and normalized composition. With `S_f` denoting section reindexing, `P_f`
geometric pullback, `κ_f` the evaluation isomorphism, and `β(f,g)` the original
normalized composition, its component equation has the form

```text
κ_(f≫g)(x); β(f,g)(E x)
  = transportS(x); κ_g(S_f x); P_g(κ_f(x)).
```

Here `E` is the relevant evaluation and `transportS` is the actual strict
section-composition equality. The theorem keeps the Spec transports,
associators and original normalization. It proves both chart faces and the
moving cylinder, with no openness, compactness, flatness or supplied coherence
premise.

[CoefficientSectionEvaluationSourceLeg](CoefficientSectionEvaluationSourceLeg.lean)
keeps the source-leg movement and the two-time raw-cone interchange.
[CoefficientSectionEvaluationTopology](CoefficientSectionEvaluationTopology.lean)
supplies the levelwise evaluation equivalences and the span/cone/loop HEP and
T1 properties. The original source-null pasting and whole seed comparison are
in [CoefficientSectionEvaluationSeedComparison](CoefficientSectionEvaluationSeedComparison.lean).
In the affine specialization,
[SectionBassEvaluation](../Affine/SectionBassEvaluation.lean) constructs the span, cone
and looped-step maps, and
[SectionBassEvaluationEquivalence](../Affine/SectionBassEvaluationEquivalence.lean)
proves complete weakness at every level, including zero, and stability in
every integer degree. Their target is the original raw bounded-flat step.

## Coefficient identity, composition and the second seed

The polynomial-span identity uses the original two inclusion tracks and
their exact clocks. [CoefficientPolynomialUnit](CoefficientPolynomialUnit.lean),
`CoefficientPolynomialSpanUnit`, the normalized-unit owners and
[CoefficientBassUnitCharts](CoefficientBassUnitCharts.lean) produce its chart
faces. [CoefficientBassUnitNativeCube](CoefficientBassUnitNativeCube.lean)
constructs the six-face identity cube.
[CoefficientBassUnitCubeConsumers](CoefficientBassUnitCubeConsumers.lean)
then gives the whole comparison square, cone identity and parameter-looped
step identity. These constructions retain the original inputs, basepoints
and independent times; the caller supplies no identity filler.

The composition proof realizes the original normalized geometric faces in
a common simplex before extending their scalar boundary.
[SplitTripleSimplex](SplitTripleSimplex.lean) and
[TripleNativeEvaluation](TripleNativeEvaluation.lean) identify the full
triple comparison, including the degree-zero loop coordinate.
[DoubleSquareMergedSimplex](DoubleSquareMergedSimplex.lean),
`DoubleSquareRectangleNative`, `DoubleSquareOriginalRectangle` and
`DoubleSquareRectangleFaces` give the common rectangle, original route faces
and continuous three-side collapse. [MWholeNativeCube](MWholeNativeCube.lean)
constructs the six original composition faces with all twelve whole shared
edges; `MWholeScalarFaces` retains their scalar face formulas. [MWholeCubeConsumers](MWholeCubeConsumers.lean) descends them to the
original comparison, cone and step composition, retaining the literal
Laurent inclusion track and independent structure time.

The positive and negative mixed comparisons used by the coefficient seed
are constructed in
[CoefficientBassPositiveActualMixedFiller](CoefficientBassPositiveActualMixedFiller.lean)
and [CoefficientBassNegativeActualMixedFiller](CoefficientBassNegativeActualMixedFiller.lean).
Their carrier surfaces keep both tips, concatenation clocks and native values
in every level. [CoefficientBassSeedPushoutComparison](CoefficientBassSeedPushoutComparison.lean)
descends these fillers to the original two-chart pushout, and
[CoefficientBassActualSeedComparison](CoefficientBassActualSeedComparison.lean)
exports the whole seed square. Its objectwise cone map and parameter-looped
first-to-second map are in
[CoefficientBassSeedIteration](CoefficientBassSeedIteration.lean). The
inclusion, entire cylinder and output-loop formulas do not assert a strict
functorial second coefficient stage.

## Coefficient source cells and quotient descent

[PushoutConeFamily](../../../Topology/Prespectrum/PushoutConeFamily.lean)
accepts four families: Laurent, positive and negative polynomial cylinders,
and overlap cylinder. With their full quotient attachments, based values
and independent structure laws, it descends them through the original
pushout and reduced cone for any locally compact external parameter.
Restriction along a continuous parameter map commutes strictly with descent
and then with independent parameter looping.
`PushoutConeFamilyRecovery.ofFamily_desc` recovers an entire supplied family;
`CoefficientBassCompositionCellDescent` applies this to the original
composition cone and step.

The Laurent families and polynomial three-cube already have their complete
selected faces. The relevant owners are
[CoefficientBassRaw1LaurentFamily](CoefficientBassRaw1LaurentFamily.lean),
`CoefficientBassRaw1PolynomialCommonPasting`, its `Sides`, `LaurentFace`,
`Top` and `Native` leaves, and
[CoefficientBassRaw1LaurentNativeCell](CoefficientBassRaw1LaurentNativeCell.lean).
[CoefficientBassRaw1PolynomialNativeCells](CoefficientBassRaw1PolynomialNativeCells.lean)
places both polynomial cells in the full original target cone;
[CoefficientBassRaw1PolynomialNativeAttachments](CoefficientBassRaw1PolynomialNativeAttachments.lean)
identifies each entire height-zero face with the Laurent family after the
actual source chart map. Height one is the original cone point. The genuine
polynomial input, original Laurent bottom, unreduced tip, based values and
structure time are retained.

The separate overlap family still needs its prescribed comparison, route,
cone-height and overlap coordinates, all eight three-faces and their whole
intersections, including the original half-height midpoint. The required
attachments must give the actual `PlusPasting` and `MinusPasting` of
[CoefficientBassSecondCoefficientProjection](CoefficientBassSecondCoefficientProjection.lean).
An assembled `PushoutConeFamily (I × I)` must recover both complete cone
routes before looping. The chosen-carrier and chosen-chart augmentation
interfaces preserve supplied earlier fillers;
`CoefficientBassSeedChosenSquareRange` preserves a supplied range condition
and does not prove the concrete chosen-boundary range.

`BassMergedBoundarySimplex`, `BassMergedScalarBoundary` and `BassH0Native`
give scalar lifts for the complete chart pauses, shared Laurent bottom and
prescribed H0 surface. These are useful boundary faces, not a recursive
producer for every raw cell tree. Likewise,
[NativeParameterEvaluation](../../../Topology/Prespectrum/NativeParameterEvaluation.lean)
preserves supplied whole-value path and homotopy lifts under an arbitrary
evaluator; it neither constructs a geometric lift nor identifies unevaluated
carrier nodes from equality of their values. Contractibility does not replace
a missing prescribed attachment or a previously chosen filler.

## Integer-base raw objects on arbitrary schemes

[GlobalRawBassSquare](GlobalRawBassSquare.lean) fixes an objectwise convention
for every `X : Scheme.{u}`. Its spectra are the original bounded-flat spectra
on the actual integer-base polynomial and Laurent products, with
`GlobalIndex`'s universe lift. The arrows are the original projections and
positive/inverse chart maps. The overlap concatenates the inverse positive
split-composition track with the inverse-chart split-composition track.

[GlobalRawBassStep](GlobalRawBassStep.lean) takes the literal cone and
parameter loops. Its `sourceNull` is the positive split-composition track
followed by the positive-leg cone null; `transition` uses the original forward
Laurent unit and this specified null. This fixes the raw object and seed
before any comparison with strict sections. No equality with the separately
implemented coefficient raw first stage is implicit in this convention.

[GlobalBassEvaluationComposition](GlobalBassEvaluationComposition.lean) and
[GlobalBassEvaluationBoundary](GlobalBassEvaluationBoundary.lean) prove the
whole relative composition and chart pastings, canceling their shared Laurent
movement. [GlobalBassEvaluation](GlobalBassEvaluation.lean) then constructs
`spanEvaluation`, `coneEvaluation` and `stepEvaluation`. The source is
literally the one-step value of the existing global strict Bass functor.
Each chart retains its original evaluation track, and the cylinder retains
both independent times.

[GlobalBassEvaluationNull](GlobalBassEvaluationNull.lean) compares the strict
and raw source nulls. [GlobalBassEvaluationSeed](GlobalBassEvaluationSeed.lean)
uses the original unit pasting to compare the forward seeds.
[GlobalBassEvaluationEquivalence](GlobalBassEvaluationEquivalence.lean)
proves the same one-step maps completely weak at every level and stable in
every signed degree. These objectwise constructions require no compactness,
quasi-separatedness or supplied overlap filler.

## Scheme-arrow input and whole evaluation naturality

For `g : X ⟶ Y`, [GlobalRawBassInputMap](GlobalRawBassInputMap.lean)
constructs `GlobalRawBass.map g : step Y ⟶ step X` from the original
polynomial/Laurent squares, both chart pastings and their full overlap. It
uses `mappingConeSquareMap` followed by `parameterLoopingMap`.
`GlobalRawBassInputNull`, `GlobalRawBassInputUnit` and
[GlobalRawBassInputSeed](GlobalRawBassInputSeed.lean) give

```text
transitionInputHomotopy g :
  transition Y ≫ map g  ~  geometricPullback g ≫ transition X.
```

The source null and forward unit are those already fixed. The Laurent
inclusion, cone cylinder and independent loop coordinate remain explicit.

The whole evaluation comparison uses the actual mixed cube, beyond the
earlier homotopy restricted to the initial seed. The `InputSimplex`,
`InputChartSimplex` and native owners retain the two original Model triangles,
binary normalization and full anchored nodes. `InputDescNative` and
`InputMixedDesc` realize both selected descent surfaces, with their original
constant-path insertions. `InputChartPrism`, the parameterized span owners
and [GlobalBassEvaluationInputCube](GlobalBassEvaluationInputCube.lean)
assemble the prescribed chart, Laurent and overlap faces, including the
distinct nested cone-height seams.

[GlobalBassEvaluationInputNaturality](GlobalBassEvaluationInputNaturality.lean)
exports `InputNaturality.coneHomotopy` and `stepHomotopy`. The latter is the
whole arrowwise comparison

```text
strictBass.map g.op ≫ stepEvaluation X
  ~ stepEvaluation Y ≫ GlobalRawBass.map g.
```

`coneHomotopy_inclusion` retains the unpaused Laurent evaluation comparison.
`originalNullSquare` recovers the actual cone-cylinder values of this
homotopy. Comparison time, loop time, degree-zero input-loop time and spectrum
structure time remain independent.

## Prescribed global identity square and remaining coherence

[GlobalRawBassInputIdentityComparison](GlobalRawBassInputIdentityComparison.lean)
constructs the original comparison square at `𝟙 X`.
[GlobalRawBassInputIdentityMap](GlobalRawBassInputIdentityMap.lean) gives
`InputIdentity.coneHomotopy` and the fixed
`InputIdentity.mapHomotopy : map (𝟙 X) ~ 𝟙 (step X)`, with their original
inclusion and cylinder formulas.

[GlobalRawBassInputIdentitySeedSquare](GlobalRawBassInputIdentitySeedSquare.lean)
constructs the higher square for the already chosen
`transitionInputHomotopy (𝟙 X)`. Its `comparison` is relative to the fixed
three-side word formed by the transition followed by `mapHomotopy`, the
constant transition track, and the reversed original source identity track.
Its `square` retains those four prescribed edges. The proof recovers the
whole routes from six compatible carrier faces, descends their original
null clocks and includes the resulting positive family into that fixed
`mapHomotopy`. This transition-identity square is a constructed interface.

Several further compatibilities remain distinct. The mixed
`longRoute.RelHomotopy shortRoute` must compare the already selected seed and
input/evaluation routes. The identity square above does not export higher
coherence of the separately chosen `InputNull.originalNullComparison`.
Scheme-arrow composition, higher seed compatibility, a coherent arbitrary
raw-stage construction, comparison with the coefficient raw stage, and the
forward-transition and same-null classical bridges must retain their own
specified maps and tracks. Neither an arrowwise homotopy nor an objectwise
stable equivalence permits `strictDiagramIterate` to be applied to a raw
assignment lacking literal functor and transformation laws.

Source and validation identities are recorded in the
[evidence registry](../../../../docs/evidence/README.md#tt-source-and-validation-records).
