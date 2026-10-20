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
carrier nodes from equality of their values.

[FamilyExtension](../../../Aglib/Topology/Path/FamilyExtension.lean) curries
an actual scalar extension on a closed parameter subset with both fixed
endpoint caps into a path family, recovering each complete supplied side.
The endpoints may differ, and no separation hypothesis on the target is
required. [PathCubeExtension](../../../Topology/HELP/PathCubeExtension.lean)
uses scalar boundary extension in dimension `n+1` to extend fixed-endpoint
path families in dimension `n`; path time is coordinate zero and the old
cube coordinates remain the tail. The scalar extension input is available
for the actual full-reference isomorphism-node nerve in
`CommonReferenceNerveCubeExtension.exists_cube_extension`, by its contraction
at the identity-reference node and boundary-inclusion HEP. Thus a supplied
continuous boundary path family in that carrier extends with exact side
recovery, including the empty boundary of a zero-dimensional cube. This does not lift an
arbitrary native family into the carrier, prove its full dependent-node
attachments, or recover prescribed native values of a newly selected
interior. Those data remain part of each geometric application.

[BassProjectionFourEdgeTargetOverlapReanchor](BassProjectionFourEdgeTargetOverlapReanchor.lean)
keeps the complete 31-node H0 target overlap under a reference change
`δ : E'.functor ≅ E.functor`. `nodes_reanchor` includes the original anchors;
`overlap_reanchor` and `cell_reanchor` preserve both old times and every
specified continuous overlap clock. `overlap_reanchor_family` retains an
arbitrary external parameter family, without compactness or local compactness
of that parameter space. Its supplier
[CommonReferenceNerveFiniteParameterNaturality](../../../Waldhausen/SConstruction/Iterated/CommonReferenceNerveFiniteParameterNaturality.lean)
takes a full dependent-node square, proved here by `pair_whiskering`.
Neither equality after native evaluation nor a choice of new filler enters
these identities. [Target reanchoring](TargetReanchoring.md) describes the
subsequently constructed polynomial sectors, complete target surface and
whole target-cone action. These coefficient constructions do not identify
the separately defined integer-base global raw presentation.

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

## Mixed evaluation, input and seed routes

For every scheme arrow `g : X ⟶ Y`,
[GlobalBassEvaluationInputSeedNaturality](GlobalBassEvaluationInputSeedNaturality.lean)
constructs `InputSeedNaturality.comparison g` with the exact type
`(InputSeedWords.longRoute g).RelHomotopy (InputSeedWords.shortRoute g)`.
The long route is `inputFirst.trans (seedSecond.trans transitionThird)`;
the short route is `seedFirst.trans evaluationSecond`. These are the
previously chosen input, evaluation and seed homotopies, with the original
strict-seed endpoint transport and half/quarter clocks.

`InputSeedRoutes.surfaces` constructs the six-face
boundary from five complete native carrier surfaces and their five whole
word joins A–E. Its input, postcomposition, strict-preinput, evaluation and
transition faces retain the ordinary and shifted reference anchors and both
separate tips. The raw-post face keeps its original square and cone-cylinder
halves. The moving evaluation face keeps the binary-normalization and
source-null halves. All dependent-node and anchor equalities are proved
before native evaluation.

`long_native` and `short_native` recover both entire routes after the
actual positive-cone inclusion. The mapped-relative extension then gives
the comparison, with no caller-supplied face agreement, square or filler.
`comparison_apply` retains independent comparison, route and seed/loop
coordinates and the separate prespectrum structure time, including level
zero. This closes the prescribed initial mixed seed comparison. It is not
an all-stage naturality or a higher identity/composition law for the
separately chosen raw input-null comparison.

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

## Span composition and the remaining cone boundary

For composable `f : X ⟶ Y` and `g : Y ⟶ Z`,
[GlobalRawBassInputCompositionSpan](GlobalRawBassInputCompositionSpan.lean)
constructs `InputCompositionSpan.homotopy` between the actual maps

```text
spanMap (f ≫ g)  ~  spanMap g ≫ spanMap f.
```

The first half moves the three original vertices through their geometric
composition rectangle. The second is the reverse of the specified
five-piece span reassociation. The two chart formulas therefore retain
an explicit terminal pause. `homotopy_cylinder_lower`,
`homotopy_cylinder_upper` and `homotopy_structure` retain the complete
cylinder values and an independent structure time.

`GlobalRawBassInputCompositionPolynomial` and
`GlobalRawBassInputCompositionTransformations` provide the original
polynomial and transformation composition squares.
`GlobalRawBassInputCompositionCharts` gives both complete chart squares.
The `CarrierCharts`, `CarrierBottom`, `BottomSeams` and `CarrierTop` owners
supply the direct H0 face, two chart faces, Laurent-composition bottom and
whole span-composition top, with the proved bottom/chart joins and original
top clocks. These five faces do not form the complete cone comparison cube.

The terminal attachments and cells recover four original H1 parameter
regions. [GlobalRawBassInputCompositionTerminalColumns](GlobalRawBassInputCompositionTerminalColumns.lean)
proves `InputCompositionTerminalColumns.column_nodes`, identifying all five full nodes of the postcomposed polynomial column with
the product column. `InputCompositionTerminalRows.row_nodes` identifies the five product-row
nodes with the precomposed input row, including their anchors.
`InputCompositionTerminalSeams.plus_middle` and `minus_middle` are entire carrier edge
equalities. [GlobalRawBassInputCompositionTerminalSecond](GlobalRawBassInputCompositionTerminalSecond.lean)
uses them to glue the positive product, input surface and reversed inverse
product into the complete second H1 half. Its `face_native` keeps the
original half/quarter/quarter overlap allocation.

[GlobalRawBassInputCompositionTerminalCenter](GlobalRawBassInputCompositionTerminalCenter.lean)
and [GlobalRawBassInputCompositionTerminalMiddle](GlobalRawBassInputCompositionTerminalMiddle.lean)
retain the actual central normalization and the complete five-node middle seam.
[GlobalRawBassInputCompositionTerminalFirst](GlobalRawBassInputCompositionTerminalFirst.lean)
lifts the accepted polynomial columns to both complete outer carrier paths.
[GlobalRawBassInputCompositionCarrierTerminal](GlobalRawBassInputCompositionCarrierTerminal.lean)
then proves the entire first/second seam and glues the whole original H1 face.
Its `seam`, `face`, and `face_native` retain the original comparison half-clocks,
overlap half/quarter/quarter clock, input and independent structure coordinate.

All six whole carrier faces and their twelve complete scalar edge agreements
are constructed. [GlobalRawBassInputCompositionCarrierCube](GlobalRawBassInputCompositionCarrierCube.lean)
extends that actual compatible boundary, retaining each selected face.
[GlobalRawBassInputCompositionComparison](GlobalRawBassInputCompositionComparison.lean)
evaluates the same cube to produce the whole comparison square, including
both chart restrictions, all three overlap clocks and independent structure
time. [GlobalRawBassInputCompositionMap](GlobalRawBassInputCompositionMap.lean)
then constructs `coneHomotopy` and `mapHomotopy` between the original direct
and composite cone/step maps. No comparison square or cylinder filler is an
application hypothesis. The whole cone cylinder uses the specified moving
null square; the parameter-loop coordinate remains independent of homotopy
time. Applying this homotopy to a seed does not by itself compare it with
the separately selected seed-naturality homotopies.

## Supported raw first-stage rows

[GlobalSupportedRawGeometry](GlobalSupportedRawGeometry.lean) uses the actual
integer-base polynomial and Laurent products on
`A : Scheme.QuasiCompactOpenPairs.{u}`. This pair category requires only
compactness of the ambient scheme. Its four maps are the existing
projection, Laurent projection, positive chart and inverse chart. Their
whole underlying arrows are those of `GlobalIndex`, and the inverse-image
projection squares are proved pullbacks.

For an open immersion `j : U ⟶ X` with compact `U` and `X`, and arbitrary
`T : X.Opens`, [GlobalSupportedRawRows](GlobalSupportedRawRows.lean) forms
the three rows vanishing on `T ⊔ j.opensRange`, on `T`, and on `j ⁻¹ᵁ T`.
The pair arrows have the contravariant directions needed for support
enlargement and restriction. Polynomial and Laurent products remain in
this same pair category. No compactness of `T`, quasi-separatedness,
flatness of a scheme arrow or extra Cartesian-square premise is required
for these objects and charts.

[GlobalSupportedRawCharts](GlobalSupportedRawCharts.lean) realizes the
original supported geometric pullbacks as Model arrows. Its
`plusCompositionIso` and `minusCompositionIso` retain the pair-equality
transport, supported composition and all three original chosen-zero
normalizations. The four evaluation isomorphisms keep both evaluation
normalizations. Whole support forgetting uses faithful categorical
inclusion, rather than injectivity of a K-group map.

[SupportedRawPullbackTrack](SupportedRawPullbackTrack.lean) identifies the
realized maps with the canonically normalized exact pullbacks.
`compositionHomotopy` is the original composition track followed by binary
normalization. `compositionComparison_whole_level` compares this split
track with the total normalized transformation as a complete two-time
continuous map. Its boundary retyping uses
[RelativeHomotopyLevelsEvaluation](../../../Topology/Prespectrum/RelativeHomotopyLevelsEvaluation.lean),
which preserves that whole map after the original triangle is constructed.

[GlobalSupportedRawInputBinarySurface](GlobalSupportedRawInputBinarySurface.lean)
proves that the finite normalization simplex evaluates to the exact chosen
`compositionComparison` for every level `n`, both scalar times `r, s`, and
original input `x`. `InputBinary.relative_native_value` uses the generic
`surfaceValue` interface; `surfaceValue_eq_level` identifies its original level
evaluation. Both original comparison tracks remain its first and last faces.
This does not supply a higher relative pasting or raw prespectrum functor law.

[SupportedRawPullbackCoherence](SupportedRawPullbackCoherence.lean)
proves equality of the two supported categorical triple-pullback routes
for arbitrary three composable open-pair arrows, retaining the functor
associator and scheme-composition transport. Faithful support forgetting
reduces it to the original ambient equation. This categorical equality
is not a relative R2 pasting or a raw prespectrum functor law.

[GlobalSupportedRawSquare](GlobalSupportedRawSquare.lean) uses the reversed
positive split track followed by the forward inverse-chart split track as
its overlap. The original reduced homotopy pushout and its Laurent
comparison retain this full overlap cylinder.
[GlobalSupportedRawStep](GlobalSupportedRawStep.lean) defines
`GlobalSupportedRawBass.step A : LoopPrespectrum.{u+1}` by parameter
looping its mapping cone. `sourceNull_apply` retains the positive split
track followed by the literal cone null, each with its original half-clock.
The unit is the forward `GlobalSchemeLaurentTrack.laurentScalar` on the
actual supported pullback. `pullbackUnitIso_hom_original` recovers its
whole termwise component. The objectwise `transition` uses exactly this
unit and source null, and `transition_apply` retains the full conjugated
loop word.

[SupportedRawNormalizedCoherence](SupportedRawNormalizedCoherence.lean) proves
the two routes for the actual chosen-zero supported pullback composition,
and [SupportedRawTripleTrack](SupportedRawTripleTrack.lean) realizes the whole
relative associativity cell for the original geometric-plus-normalization
tracks. The abstract
[contravariant composition tracks](../../../Topology/Prespectrum/ContravariantCompositionTracks.lean)
produce the original chart pastings, while the
[split-square input](../../../Topology/Prespectrum/SplitSquareInput.lean),
[specified source-null](../../../Topology/Prespectrum/SplitSquareSourceNull.lean)
and [seed](../../../Topology/Prespectrum/SplitSquareSeed.lean) interfaces pass
these pastings through the double mapping cylinder, comparison cone and
parameter looping. [GlobalSupportedRawSplitSquare](GlobalSupportedRawSplitSquare.lean)
recovers the existing supported raw constructions literally. For every
morphism of quasi-compact open pairs,
[GlobalSupportedRawInputCharts](GlobalSupportedRawInputCharts.lean) supplies the
proved chart pastings and [GlobalSupportedRawInput](GlobalSupportedRawInput.lean)
constructs the actual first-stage map and whole prescribed Bass source-null
comparison. In particular, `Rows.enlargementMap` and `Rows.restrictionMap` act
on the original three localization rows. The supported unit comparison in
[GlobalSupportedRawInputUnit](GlobalSupportedRawInputUnit.lean), built from
[SupportedRawUnitCoherence](SupportedRawUnitCoherence.lean) and
[SupportedRawUnitTrack](SupportedRawUnitTrack.lean), gives
[GlobalSupportedRawInputSeed.transitionInputHomotopy](GlobalSupportedRawInputSeed.lean):
`transition B ≫ map f ~ rawMap f.hom ≫ transition A`.
This is a one-step supported raw input/seed result. The localization composite's
specified `fullNull` and its whole cone/null normalization comparison remain
separate inputs, as do strict raw input identity/composition and all-stage
successor compatibility.


The Bass `sourceNull` differs from the canonical localization `fullNull`;
its independently proved base and parameter normalization squares are described
in [geometric connecting maps](GeometricBoundary.md#canonical-weak-zero-and-homotopy-null-comparison).

For a quasi-compact open pair `A = (j : U ⟶ X)`,
[GlobalSupportedEvaluation](GlobalSupportedEvaluation.lean) constructs evaluation from
the original supported scheme-parameter first Bass stage at `Spec ℤ` to the actual raw
supported stage. [GlobalSupportedEvaluationSource](GlobalSupportedEvaluationSource.lean)
recovers that original source by a whole square isomorphism, with the original
identity-parameter base map, affine polynomial/Laurent maps, and genuine supported pair
symmetry. The recovery preserves the full-clock strict source null.
[GlobalSupportedEvaluationSourceUnit](GlobalSupportedEvaluationSourceUnit.lean) also
recovers the original forward Laurent unit and specified scheme seed. The full supported
composition and unit equations then produce
[GlobalSupportedEvaluationSeed.seedHomotopy](GlobalSupportedEvaluationSeed.lean), with
independent comparison, output-loop, and prespectrum-structure parameters. This closes
the original section-to-raw first-stage evaluation and specified forward-seed comparison
only. Compatibility with the localization composite's selected weak-zero null, the
complete localization cone/null squares, higher supported stages, and the telescope
remain separate comparisons.

## Original null-composition boundary and positive support

[GlobalRawBassInputCompositionNullRails](GlobalRawBassInputCompositionNullRails.lean)
constructs both whole null rails along the actual cone and base composition tracks.
The source rail retains the original half-clock Laurent leg and corrected cone-null
square. The target rail is the original interchange, with independent composition,
null and prespectrum structure parameters.

[GlobalRawBassInputCompositionNullPasting](GlobalRawBassInputCompositionNullPasting.lean)
pastes the two original arrowwise null comparisons into `compositeComparison`,
including its final inverse path associator. Its actual Laurent projection square
and the two rails produce `alternateComparison`, whose endpoints are exactly those
of `InputNull.originalNullComparison (f ≫ g)`. The boundary-collapse word retains
its terminal zero face. The exact chosen-null comparison below now connects these two
prescribed surfaces without changing their selected boundary data.

[GlobalRawBassInputCompositionPositiveFactor](GlobalRawBassInputCompositionPositiveFactor.lean)
constructs the positive-cone restriction of the already selected `coneHomotopy`.
`nullSquare_factor` preserves its original pause, cone-null reassociation, boundary
collapse and square conversion; `coneHomotopy_factor` holds at every positive-cone
point. The continuous `sourceRail` recovers the whole original source rail and
preserves its basepoint and independent structure coordinate. This is positive
support of the fixed native homotopy, not a presentation of its arbitrary overlap
interior or a scalar carrier lift of both chosen comparison surfaces.

## Remaining higher coherence

The initial mixed seed comparison and prescribed transition-identity square
above and the complete original cone/step composition cube are constructed.
The separately chosen `InputNull.originalNullComparison` now has the exact
composition comparison described below. Higher coherence of seed-naturality homotopies,
a same-convention raw second stage and a coherent arbitrary-stage producer still
require their specified data. Comparison with the coefficient raw
stage and the classical forward-transition and whole-null diagrams remains
separate. Neither an arrowwise homotopy nor an objectwise stable equivalence
permits `strictDiagramIterate` to be applied to a raw assignment lacking
literal functor and transformation laws.

Source and validation identities are recorded in the
[evidence registry](../../../../docs/evidence/README.md#tt-source-and-validation-records).

### Exact scalar recovery of the chosen composition source rail

`GlobalRawBassInputNullCompositionPolynomialCarrier`,
`GlobalRawBassInputNullCompositionCorrectedCarrier`, and
`GlobalRawBassInputNullCompositionCorrectedNative` construct the whole source rail in the
fixed composite cut-open carrier. The original Laurent product, paused polynomial edge,
positive chart square and ordinary cone cylinder are retained. The corrected scalar square
uses the literal boundary conversion, horizontal concatenations, three-piece associator and
quotient descent. `sourceRail_original` identifies every scalar value with the already selected
whole-cone source rail at both unchanged clocks and every native input. Its half-height seam
is a full scalar attachment, not an equality inferred from native evaluation.

This closes the scalar source-rail recovery obligation. It does not construct the remaining
composite null comparison `J1`, the three-dimensional comparison `J0 ~ Jalt`, the complete
whole-overlap chosen-cone composition family, `R2`, or a uniform successor.

### Exact transport of the first chosen null comparison

`GlobalRawBassSeedOrdinarySheet` reconstructs the entire original seed comparison on the
actual first simplicial attachment. `inclusion_pastedNull` factors the existing ordinary
`InputIdentitySeedNull.pastedNull` surface through that sheet at both unchanged clocks,
including its full rectangle, cone-boundary cancellation and five-stage word.

`GlobalRawBassSeedSurfaceTransport` descends the original positive chart homotopy followed
by the final cone cylinder through this whole ordinary sheet. The chart uses the full
polynomial nerve and the actual five-node chart path, retaining the original half-time cut.
Both seams are full dependent-node equalities with the maintained terminal product anchors.
`chartParameter_movement` identifies the complete scalar terminal product face before native
evaluation; `transport_native` recovers the actual positive cone map at every carrier point.
The typed `comparison` keeps the original source and target path associations, and
`surface_native` recovers the maintained `InputCompositionNull.firstComparison` at every
native level, input point and pair of clocks.

This supplies the first entire chosen-null comparison surface in the fixed composite
carrier. It does not identify the scalar endpoints needed to paste it with the second
comparison, construct `J1` or its six-face boundary, or prove `J0 ~ Jalt`, `R2`, or a uniform
successor. No native injectivity or already-supplied comparison filler is assumed.

## Exact scalar composite null comparison

`GlobalRawBassInputNullCompositionPrecomp` transports the entire ordinary seed sheet
under the actual normalized base premap. Its Laurent attachment is forced by the
original polynomial attachment, and `GlobalRawBassInputNullCompositionPrecompSeams`
identifies that complete anchor with `InputCompositionTerminalAttach.preAnchor`
by cancellation of an already proved full second-row node. No native injectivity,
assumed carrier lift, or new reference choice is used.

`GlobalRawBassSeedPositiveParameter` and `GlobalRawBassSeedPositiveSeam` identify the
original postcomposed K path with the precomposed D path on all three binary nodes
and at every original time. `GlobalRawBassInputNullCompositionJ1Seams` proves the
remaining whole chart-then-cylinder join: the shared polynomial corner is literal
full-node equality, and the first target cone is exactly the second source's
positive movement followed by its unchanged cone path.

`GlobalRawBassInputNullCompositionCompositeCarrier.surface` is consequently an
actual continuous scalar representative of the chosen composite comparison J1
inside the fixed two-tip carrier for the composite arrow. It retains the literal
association first comparison, then the horizontal composite of the first Laurent
path with the second comparison, then the inverse associator. In particular the
original lower half and both quarters of the upper half are unchanged.
`surface_native` recovers `InputCompositionNull.compositeComparison` for every
spectrum level, input point, comparison time, and path time.

The complete source/target rail endpoint joins and Laurent target-word joins now
combine this J1 with the direct comparison in the exact chosen-null cube below.
The J1 surface itself remains distinct from that higher comparison; neither result
supplies R2 or a uniform successor theorem.


### Complete original Laurent face and scalar boundary

`GlobalRawBassInputNullCompositionLaurentCarrier.face` places the original
18-node Laurent projection square in the fixed composite carrier. Its
`face_native` recovers the actual `InputCompositionNull.laurentSquare`, with
the original mapping-cone inclusion, at every level and all parameter values.
`GlobalRawBassInputNullCompositionLaurentSeams.face_zero` is the direct composite
Laurent path; `GlobalRawBassInputNullCompositionLaurentBoundary.face_one` is the
first postcomposed path followed by the second precomposed path, with the original
binary subdivision. `GlobalRawBassInputNullCompositionLaurentSides.face_left`
and `face_right` identify the complete scalar sides with the source and target
null rails. These identities retain full reference nodes and do not infer scalar
equality from native evaluation. Together they supply the Laurent face and all
four boundary joins required by the higher comparison; construction of that
comparison is a separate consumer.


### Exact higher comparison of the chosen null homotopies

`GlobalRawBassInputNullCompositionTypedJ1.comparison` types the entire scalar J1
without changing any of its values. `GlobalRawBassInputNullCompositionAlternateCarrier`
constructs the literal alternate word: source-square boundary, horizontal whiskering
of J1, then the inverse target-word boundary. The terminal pause and inverse
associator remain present. `alternate_native` in
`GlobalRawBassInputNullCompositionAlternateNative` recovers the originally specified
`InputCompositionNull.alternateComparison` for every input and both original times.

`CommonReferenceNerveCutOpenChosenNullExtension` glues the six actual scalar faces
and extends them in the existing contractible cut-open carrier. Its endpoint faces
retain the actual Laurent source and ordinary tip; no two-tip loop substitution or
assumed filler is used. Compact native evaluation supplies joint continuity,
the basepoint equation, and the independent prespectrum structure equation.

`GlobalRawBassInputNullCompositionChosenCube.cube` consequently joins the original
`InputNull.originalNullComparison (f ≫ g)` to the literal alternate comparison.
The other four entire faces are fixed: the original old-null word, the direct
Laurent path followed by the original new-null word, the original Laurent source,
and the ordinary terminal tip. `chosenComparison` extracts the actual continuous
relative homotopy between the two selected two-parameter level maps, relative to
all four edges and the basepoint locus. `chosenComparison_structure` retains an
independent structure coordinate. Thus this specific chosen-null composition
obligation is closed, not merely its edges or a conditional extension interface.

Compatibility of the selected seed-naturality homotopies with composition is
provided by the complete original seed-composition square below. A classical
comparison and a uniform successor remain separate obligations.


### Seed comparison under replacement of the chosen null

`GlobalRawBassInputNullCompositionSeedReplacement.seedInputComparison` propagates
the chosen-null cube into an actual relative homotopy of the direct-arrow seed
input homotopy. Its first face is exactly `transitionInputHomotopy (f ≫ g)`;
its second is `alternateSeedInputHomotopy`, obtained by replacing only
`InputNull.originalNullComparison` with the literal alternate comparison.
The original direct-arrow Laurent path, both unit paths, `InputSeed.unitPasting`,
conjugation word and source/target endpoint casts remain fixed. Joint continuity
follows the original horizontal and vertical binary clocks before output-loop
currying; comparison, seed, output-loop and structure coordinates stay independent.

This result alone closes the null-replacement consumer. Full binary seed
composition is supplied separately by the whole-route carrier construction below;
that construction does not assume an independent higher unit-pasting comparison.

### Exact composition recovery on arbitrary polynomial input

[GlobalRawBassInputCompositionPolynomialScalarCarrier](GlobalRawBassInputCompositionPolynomialScalarCarrier.lean)
constructs a chart-relative scalar carrier whose native source is the original
prespectrum of bounded flat perfect complexes on `polynomial.obj Z`. Its polynomial
reference is the actual binary normalized pullback for `polynomial.map f` and
`polynomial.map g`; the Laurent reference is the original normalized triple with
the selected chart at `X`. The actual triple composition isomorphism supplies the
attachment. Equality of the three full dependent nodes identifies the original
polynomial composition path with row `2, 3, 11` of the eighteen-node chart simplex,
including its prescribed terminal pause.

[GlobalRawBassInputCompositionPolynomialScalarCorrection](GlobalRawBassInputCompositionPolynomialScalarCorrection.lean)
and [GlobalRawBassInputCompositionPolynomialScalarNative](GlobalRawBassInputCompositionPolynomialScalarNative.lean)
retain the complete original moving chart square, polynomial cylinder, three-piece
associator, boundary conversion and square descent. `correctedSquare_native` recovers
every value of the selected composition null square for an arbitrary original
polynomial input, not merely an input obtained after the source projection.

[GlobalRawBassInputInverseSupport](GlobalRawBassInputInverseSupport.lean) and
[GlobalRawBassInputCompositionInverseFactor](GlobalRawBassInputCompositionInverseFactor.lean)
provide the separate strict inverse-chart support and its whole composition factorization.
[GlobalRawBassInputCompositionPolynomialRecovery](GlobalRawBassInputCompositionPolynomialRecovery.lean)
then proves `plus_coneHomotopy` and `minus_coneHomotopy`: both scalar chart families
recover the literal chosen `InputComposition.coneHomotopy` on every polynomial
cylinder input at the unchanged composition and height clocks. `correctedFamily`
is jointly continuous, based, and compatible with an independent structure time.
Its scalar carrier is contractible by the existing cut-open carrier theorem.

The two arbitrary-polynomial chart references remain distinct. The existing
`ProjectionReference.FourEdge.scalarCone X E` instead assumes a base reference
`E : V → Model(X)` and the induced polynomial reference `E ≫ projectionMap X`;
that factorization is not asserted for arbitrary polynomial complexes. Relating
these chart-relative carriers to the five-node projection-reference cone requires
the actual source projection and explicit full-node overlap attachments. The
original overlap-cylinder lift is provided below. Its full endpoint attachments
to these chart carriers, a higher compatible boundary, R2 closure and uniform
successor remain separate obligations. This chart result does not supply those
remaining attachments.

### Exact composition square for the original seed homotopy

[GlobalRawBassInputSeedCompositionChosenCube](GlobalRawBassInputSeedCompositionChosenCube.lean)
provides `InputSeedCompositionChosenCube.seedSquare`. Its first boundary is the
original selected `transitionInputHomotopy (f ≫ g)`; its opposite boundary is the
literal concatenation of the original seed homotopy for `g`, postcomposed by
`map f`, and the original seed homotopy for `f`, precomposed by the base map for
`g`. Its remaining boundaries are the actual `mapHomotopy f g` after the source
transition and the actual `baseCompHomotopy f g` before the target transition.
The comparison, seed, output-loop and structure coordinates remain independent.

The construction transports both complete two-tip seed carriers, preserving the
original ordinary and shifted sheets, chart/cylinder split, and distinct tips.
Corrected ordinary null rails and their shifted inclusions join the original
unit-product rails as full scalar paths. The resulting source and target seed
rails recover the chosen native map and base composition homotopies at every
point. Their endpoint words join the original transported seed surfaces without
changing any concatenation clock or inserting an assumed higher unit comparison.

The complete cut-open route surfaces give a relative comparison between the
original seed and the source-rail/composite-seed/reversed-target-rail word.
Evaluating this comparison and extracting its square yields `seedSquare` with
its exact original four boundaries. This closes full binary seed composition,
not merely replacement of its chosen null homotopy. It does not by itself assert
a whole overlap carrier construction, a classical comparison, or a uniform
successor.

### Exact original composition on every overlap-cylinder input

[GlobalRawBassInputCompositionOverlapNative](GlobalRawBassInputCompositionOverlapNative.lean)
provides `InputCompositionOverlapScalar.coneHomotopy_overlap`. For every original
base input, it recovers the literal chosen `InputComposition.coneHomotopy` on the
original span overlap cylinder inside the original cone cylinder. Composition
time, cone height, overlap height, native level and input remain independent.
`correctedFamily` is jointly continuous in all three scalar parameters, and the
whole scalar-cone evaluator retains based points and independent structure time.

The actual eighteen-node polynomial square attaches to the original binary base
path in the projection-reference four-edge tree. Its original moving stage and
reversed five-piece reassociation give `treeComposition`; both its full Laurent
attachment and its native original span value are proved independently. The
literal previously chosen `carrierCube`, including every interior point, is
reanchored into the Laurent reference and its complete top equals that attachment.
No equality is inferred from injectivity of native evaluation.

The chosen cube and actual moving tree cylinder are pasted with their original
half clocks. Currying the independent overlap coordinate gives a surface in
continuous overlap-indexed scalar-cone families. The original three-side boundary,
three-piece associator, terminal pause and boundary descent are then performed in
that function space, and uncurrying recovers every original corrected native value.
The result is the selected corrected cone-composition homotopy, not merely its
uncorrected moving-null square or its boundary faces.

This closes the overlap-cylinder pilot. A single whole arbitrary-span comparison
still requires the complete endpoint attachments to both arbitrary-polynomial
chart carriers through the actual source projection, before any higher compatible
composition boundary is claimed. R2 associativity, the same-convention second-stage
producer, classical comparison and uniform successor are not supplied here.

### Whole transport of genuine polynomial-chart carriers

[Chart-relative transport](ChartRelativeTransport.md) constructs the actual whole
positive/inverse scalar-carrier postmap for an unrestricted polynomial reference,
without a base-projection factorization. It recovers the original raw cone map
and the entire selected polynomial composition correction at unchanged clocks.
This remains separate from base-reference transport and does not complete R2.

## Original whole raw prewhiskering and compatible scalar source cells

For scheme arrows `f : X ⟶ Y`, `g : Y ⟶ Z`, and `c : Z ⟶ W`, the scalar producers retain the literal original homotopy `InputComposition.coneHomotopy f g` after precomposition by `GlobalRawBass.coneMap c`. The genuine positive and negative polynomial-source cells use their own two-tip carriers with native inputs on `polynomial.obj W`; the overlap-cylinder cell uses the original base-reference four-edge cone with native inputs on `W`. Neither domain is replaced by an assumed factorization through a projection. The lower Laurent family uses arbitrary inputs on `laurent.obj W`.

`polynomialPrewhisker` and `overlapPrewhisker` retain the original lower/upper cone-height clocks. Their half-height equations and `source_plus`/`source_minus` are full scalar equalities, before native evaluation. The source-height-zero laws retain the actual chart node-two normalization and the complete original five-node comparison path. Separate tips and the all-carrier pointed evaluation laws provide the terminal and based boundaries. The original correction interiors, reversed positive/forward negative middle word, and independent composition, height, overlap, native-level, loop, and structure coordinates are unchanged.

`rawPreFamily` is the existing `PushoutConeFamily.ofHomotopy` applied to the original raw prewhiskering. Its exact whole-cone descent and four scalar-cell recovery theorems identify these constructed scalar lifts with the original chosen family. This interface identification is not a new higher filler. In particular, the common-reference endpoint identifications between different pre- and post-whiskered occurrences in the two direct R2 projection-pasting words remain separate obligations. No complete R2 pasting, R2 functorial coherence, or arbitrary-stage successor construction is asserted here.
