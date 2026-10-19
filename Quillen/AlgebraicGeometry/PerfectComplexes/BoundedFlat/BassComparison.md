# Bounded-flat sections and Bass comparisons

Cocartesian bounded-flat sections provide strict coefficient diagrams while
retaining the original geometric evaluation maps. This guide develops their
fine finite stages, original classes, telescope and same-null localization.
[Raw evaluation](RawEvaluation.md), [geometric connecting maps](GeometricBoundary.md),
[affine graded objects](../Affine/README.md) and [scheme Bass groups](../Bass/README.md)
keep their own interfaces. The [classical comparison boundary](../Development.md)
requires the specified object, transitions and whole null diagram.

## Bass groups and geometric spectral comparisons

The generic recursion, finite-bottom groups, and telescope-identification
boundary are developed in [spectral and Bass interfaces](../../../KTheory/Bass/README.md). This section
records their perfect-K₀ seeds, geometric step/evaluation maps, and support
interfaces used by the localization comparison.

## Strict sections and one-step evaluation

`BoundedFlat.Sections` forms cocartesian sections of the actual geometric
Grothendieck construction. Identity evaluation is an exact categorical
equivalence; canonical sections have the original coefficient-pullback values.
The original global chosen-zero family is retained under evaluation and strict
coefficient reindexing. Section morphisms have universe `u+1`, versus original
bounded-flat morphisms in `u`; common-universe comparisons retain the actual
forward maps. `SectionWaldhausen`, `SectionReindexExact`,
`SectionSpectrumEquivalence`, and `SectionPrespectrum` give the pointwise
Waldhausen structure, all-level homotopy equivalence, and genuine strict
iterated-S coefficient diagram. These routes have prefix
`Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat`.

Actual coefficient evaluation, its chosen-zero normalization, and Model
composition/relative composition tracks are kept by `SectionEvaluation`,
`SectionEvaluationNormalization`, `SectionSpectrumNaturality`,
`SectionModelComposition`, `SectionModelRelativeComposition`,
`SectionModelTrackNaturality`, `SectionModelTargetTrack`, and
`SectionCoefficientComposition`. They retain original cocartesian transition
isomorphisms, Spec composition transports, associators, and whole whiskered
geometric tracks; a categorical comparison is not silently treated as strict
geometric evaluation naturality.

`Affine.SectionLaurentUnit`, `SectionLaurentPullback`, and `SectionBassSeed`
construct the original literally coefficient-natural scalar action and strict
seed `F → B(F)`, including zero-level loops and the source-null cylinder.
`Quillen.KTheory.Bass.StrictDiagram` is the actual endofunctor using the literal
Laurent square, double mapping cylinder, cone, and parameter looping.
`SectionBassDiagram` iterates it; every `SectionBassTransition` is `B^i` of
the same proved seed. No supplied seed premise or new transition unit is used.

`SectionBassEvaluation` constructs the original strict-to-raw span, cone, and
looped-step maps using the proved full comparison filler.
`SectionBassEvaluationEquivalence` proves those same maps completely weak at
every level, including zero, and stable in all integer degrees. The target is
the original raw bounded-flat step; its coefficient maps are not strictified.
`SectionBassEvaluationNull`, `SectionLaurentEvaluationHomotopy`,
`SectionBassSeedEvaluation`, and `SectionBassPerfectSeedEvaluation` retain the
actual null/unit moving squares and compare the single strict, raw, and perfect
seeds without a compatibility assumption. Full all-iterate comparison with the
original geometric tower remains a separate obligation.

## Global sections and coefficient restriction

[GlobalSectionChangeIndex](GlobalSectionChangeIndex.lean) constructs the actual global
bounded-flat section Model over `Scheme.{u}ᵒᵖ`, using the geometric
pseudofunctor, original fiber Waldhausen structures and one chosen-zero
family. Its values lie in `Model.{u+1}`. Restriction along the coefficient
base-product functor lands in the existing coefficient-first Models.
[GlobalSectionChangeIndexLaws](GlobalSectionChangeIndexLaws.lean) identifies the underlying
functor and evaluation literally and proves exactness of the categorical
inverse. The general change-index construction and its explicit universe
bounds are described in the
[fibered-category guide](../../../Aglib/CategoryTheory/FiberedCategory/README.md#change-of-index).

[GlobalSupportedModels](GlobalSupportedModels.lean) and
[GlobalSupportedRow](GlobalSupportedRow.lean) retain sections whose original
evaluated complex is acyclic on the specified open. The support inclusion,
coefficient restriction and their evaluation square use the same zero.
[GlobalOpenModels](GlobalOpenModels.lean) changes only the weak class to the
actual coarse-open class; [GlobalFullOpenModels](GlobalFullOpenModels.lean) gives the
original restriction to the fine global row on the open scheme. Exactness and
the supported/coarse categorical inverses are supplied by
[GlobalLocalizationEquivalence](GlobalLocalizationEquivalence.lean).

The ambient, supported and coarse rows retain their original forward Laurent
actions and base seeds. Their finite maps and quotient telescopes are in
[GlobalSectionTelescope](GlobalSectionTelescope.lean),
[GlobalSupportedTelescope](GlobalSupportedTelescope.lean) and
[GlobalOpenTelescope](GlobalOpenTelescope.lean). Every transition is the actual
`B^i` of that row's base seed. Restriction commutes with these transitions,
preserves every original inclusion and cylinder, and is stable at each finite
stage and on the telescope. The ambient comparison needs no compactness;
the supported and coarse comparisons retain the open-immersion hypothesis.

[GlobalSectionLocalizationNull](GlobalSectionLocalizationNull.lean) constructs the reversed
zero-to-supported-section null.
[GlobalSectionLocalizationFiniteNull](GlobalSectionLocalizationFiniteNull.lean),
[GlobalSectionLocalizationNullSeed](GlobalSectionLocalizationNullSeed.lean) and
[GlobalSectionLocalizationTelescopeNull](GlobalSectionLocalizationTelescopeNull.lean)
preserve every time slice of the same null and its actual seed-transition
equation.
[GlobalSectionCoarseFiber](GlobalSectionCoarseFiber.lean) proves the resulting global
coarse fiber lift stable in every integer degree for an open immersion
`f : P ⟶ Q` over `Spec R`, without compactness assumptions.
[GlobalSectionFullOpenFiber](GlobalSectionFullOpenFiber.lean) postcomposes with actual
full-open restriction and compares the same-null lift to the existing fine
fiber. Its stability requires compact `P.left`, compact `Q.left` and
quasi-separated `Q.left`, as well as the open immersion. The structural
restriction and whole-null equations need only the open immersion. These
compare global-section and coefficient-section constructions; constructed
fine localization was already available independently.

For an actual empty open source,
[GlobalEmptySupportedModels](GlobalEmptySupportedModels.lean) identifies the
original support-forgetful arrow as a Model isomorphism. Its exact inverse
retains the same section and chosen zero. The parameter version
[GlobalEmptySupportedParameterModels](GlobalEmptySupportedParameterModels.lean)
preserves the original products, pair pullbacks, forward Laurent unit and
whole tracks in both directions. The acyclicity input is the
[ordinary empty-scheme complex theorem](../../../Aglib/AlgebraicGeometry/Modules/Complex/Empty.lean);
it has no boundedness, flatness or perfectness hypothesis.

The auxiliary support diagram is also explicit. For an open immersion
`f : P ⟶ Q` and `T : Q.Opens`,
[ParameterAuxiliarySupportMaps](ParameterAuxiliarySupportMaps.lean) uses the
three supported Models vanishing on `T ⊔ f.opensRange`, on `T`, and on
`f ⁻¹ᵁ T`. Its original enlargement and restriction preserve the chosen zero
and the actual ambient forgetful maps. `ParameterAuxiliarySupportTrack`,
`ParameterAuxiliarySupportNull` and the finite/telescope-null owners retain
the forward Laurent tracks and every value of the original null.

At integral Spec-row coefficients,
[GlobalAuxiliaryCoefficientPairs](GlobalAuxiliaryCoefficientPairs.lean) and
the `GlobalAuxiliaryParameterCoefficient` Models/Diagrams/Rows/Unit/Track/Seed
owners compare those same three Models with their original fine coefficient
Models. The finite and telescope comparison maps are stable, preserving
every original inclusion and cylinder. The precise map and null equations
are in [GlobalAuxiliaryParameterTelescopeSquares](GlobalAuxiliaryParameterTelescopeSquares.lean)
and [GlobalAuxiliaryParameterTelescopeNull](GlobalAuxiliaryParameterTelescopeNull.lean).
Their structural comparisons do not add compactness assumptions.

The finite directed weak-zero construction retains this same canonical
localization null before any proposed raw comparison. Its marked edge,
whole normalization face and weak-first/target-isomorphism product are in
[geometric connecting maps](GeometricBoundary.md#canonical-weak-zero-and-homotopy-null-comparison).
These primitive families do not supply the full raw-row null square.

## Native current-stage full-open localization

Let `f : P ⟶ Q` be an open immersion of schemes. The parameter Models in
[GlobalOpenPairDiagram](GlobalOpenPairDiagram.lean)
use the actual integer-base products. Their supported objects are the original
global sections whose evaluated complexes are acyclic on the corresponding
open product. The supported inclusion retains its chosen zero; `fullMap`
changes the weak class and then applies the actual full-open restriction.
[ParameterLaurentTrack](ParameterLaurentTrack.lean)
gives their original forward scalar actions. The independent null and scalar
times commute in
[ParameterLaurentNull](ParameterLaurentNull.lean).

[ParameterFullCurrentNull](ParameterFullCurrentNull.lean)
transports that same selected null to the current, normalized and twisted
telescopes. In
[ParameterFullFiberComparison](ParameterFullFiberComparison.lean),
`Quillen.PerfectComplexes.ParameterFullCurrentNull.currentLift f X` is the
homotopy-fiber lift of `currentForget f` along `currentOpen f`, using
`currentNull f` at the scheme parameter `X`. Its stability is equivalent to
that of the normalized and twisted lifts through the actual three-object
comparison squares and every value of the original null.

The iterated-seed model uses the original `B^i(seed)` transitions.
[ParameterIteratedFullFiber](ParameterIteratedFullFiber.lean)
compares its same-null lift, at every integral Spec-row coefficient, to the
existing fine localization lift.
[ParameterIteratedTwistedFiber](ParameterIteratedTwistedFiber.lean)
then connects this lift to the twisted model. The telescope route is
`I → T ← N ← C`, where `I` is iterated-seed, `T` twisted-normalized,
`N` unpermuted normalized and `C` current-stage; the
[spectrum guide](../../../KTheory/Bass/README.md)
gives the generic maps. Each comparison preserves support forgetting,
full-open restriction and the whole selected null.

[ParameterCurrentFullFiber](ParameterCurrentFullFiber.lean)
proves
`Quillen.PerfectComplexes.ParameterFullCurrentNull.currentLift_integer_isStableEquivalence`:
for `[IsOpenImmersion f]`, `[CompactSpace P]`, `[CompactSpace Q]` and
`[QuasiSeparatedSpace Q]`, the actual map `currentLift f (op integerBase)`
is a stable equivalence. `currentLift_integer_signed_isIso` states the induced
isomorphism in every degree `d : ℤ`. These theorems expose no additional
equivariance or tower-coherence premise. At the integer parameter,
[GlobalParameterIdentityModels](GlobalParameterIdentityModels.lean)
identifies the ambient and supported Models by their original projection and
preserves both maps. The auxiliary lift below and the original-class
boundary comparisons use further assembled map and whole-null squares;
classical raw-stage identification retains its separate target. Source and
validation identities are in the
[global evidence registry](../../../../docs/evidence/README.md#tt-source-and-validation-records).

The auxiliary lift in
[ParameterAuxiliaryCurrentFiber](ParameterAuxiliaryCurrentFiber.lean) is
formed from the actual support enlargement, restriction and selected whole
null. Its current, normalized, twisted and iterated versions retain the
same three-object comparison squares.
[ParameterAuxiliaryCurrentLocalization](ParameterAuxiliaryCurrentLocalization.lean)
proves `currentLift_integer_isStableEquivalence` and
`currentLift_integer_signed_isIso` for the original open immersion, compact
`P`, `Q`, `T`, and quasi-separated `Q`. The Spec-row theorem keeps the same
hypotheses at every original affine coefficient parameter. Its fiber
projection is precisely the original enlargement. This constructs the
auxiliary current-stage localization as well as the basic full-open case.
Its original negative classes and positive geometric sign are described in
[geometric connecting maps](GeometricBoundary.md); identification with the
specified classical raw object remains separate.

## Finite-stage excision and bottom groups

For `f : E ⟶ F`, the canonical cone-fiber comparison is
`E ⟶ homotopyFiber (mappingConeInclusion f)`. It uses the original cone
cylinder as its full fiber path; the source is the original `E`.

The original S-level growth, chosen-point HEP, and finite double-cylinder gap
discharge cone-fiber stable excision for original S-model maps in
`Quillen.Waldhausen.SConstruction.Iterated.ConeFiberExcision`.
`Affine.SectionBassConnectivity` propagates all-point growth through every
finite Bass stage `i`: at original level `n+i+2`, degrees `k < n+2` vanish
at every point. `SectionBassConeExcision` proves the original comparison stable
for every map between actual stages `i,j`, with connectivity `2*n+2` at level
`n+max(i,j)+2`. All growth and point-HEP premises are discharged; the seed itself
is not asserted stable.

`Quillen.Topology.Prespectrum.ConeStableExactness` and `ConeStableNaturality`
transport the genuine fiber sequence through that same cone comparison. The
boundary is the signed fiber boundary followed by its inverse; exactness keeps
the original arrow and cone inclusion. `SectionBassStableSequence` specializes
the recurring signed positions. `SectionBassWholeTrackCone` and the finite-stage
pushout owners retain supplied whole tracks and discharge their row-excision
conditions. `SectionBassPushoutStableEquivalence`,
`SectionBassPushoutHomotopyStableEquivalence`, `SectionBassFunctorStableEquivalence`,
and `SectionBassIterateStableEquivalence` preserve stability of the original
maps from explicit stable corner maps. The generic
`Quillen.KTheory.Bass.StrictDiagramStableEquivalence` keeps its topology/growth
premises, while `ModelDiagramStableEquivalence` discharges them for actual
strict iterated-S Model diagrams and exact-equivalence transformations.

`BoundedFlatBassSpanStableGroups` proves the raw polynomial span generated at
degree zero by its two original inclusions, with negative vanishing and genuine
raw comparison excision. `BoundedFlatStableKZero`, `BassFirstCokernel`, and
`BassFirstStableGroup` identify existing PerfectK-based `negativeKFunctor 1`
with raw first-step degree minus one. The Laurent representative is the original
K₀ comparison, cone inclusion, and signed loop shift; its kernel is positive-chart
image minus inverse-chart image. `Quillen.KTheory.Bass.TwoChartSigns` negates
only the second polynomial summand. `BassFirstStableNaturality` uses the
unchanged raw coefficient stable maps and proves their group-functor laws;
`SectionBassFirstStableGroup` transports through the actual one-step evaluation.
A separate finite-projective-module presentation is not an input.

At stage `i`, `SectionBassStableConnectivity` proves vanishing below `-i` and
span generation in degree `-i`. `SectionBassSuccessor`,
`SectionBassSuccessorStable`, `SectionBassBottomGroups`, `SectionBassBottomCokernel`,
and `SectionBassBottomComparison` give, for every natural `i`, a natural
isomorphism from existing `negativeKFunctor i` to degree `-i` of actual finite
stage `i`. They retain the original recursive Laurent quotient, both chart signs,
coefficient maps, and stage-zero evaluation. These are diagonal bottom groups.
Their construction alone does not imply
later-stage stabilization; the fine range and telescope theorems below supply
that additional result under their stated hypotheses. Comparison with the
earlier evaluation-based first-stage isomorphism remains separate.

The native ambient extension
[`CoefficientBassOriginalNegativeComparison`](CoefficientBassOriginalNegativeComparison.lean)
identifies the original scheme Bass recursion on each coefficient fiber of a
compact `P : Over (Spec R)` with degree `-i` of its actual finite stage `i`.
It is natural in coefficient arrows, preserves the original perfect K₀
evaluation and Laurent quotient, and uses the genuine native polynomial and
Laurent products. `CoefficientBassOriginalNegativeNaturality` retains scheme
restriction between compact endpoints.

For an open immersion `f : P ⟶ Q`,
[`CoefficientSupportedNegativeBottomComparison`](CoefficientSupportedNegativeBottomComparison.lean)
gives the corresponding supported finite-bottom isomorphism. Only `Q.left`
needs to be compact for this finite comparison. The actual support-forgetting
square, including its Laurent representative, is retained by
`CoefficientSupportedNegativeForgetComparison` under that same hypothesis;
compactness of the removed open is not needed here.

`CoefficientBassNegativeMap` composes the original ambient finite comparison
with the actual stage inclusion. `CoefficientBassSchemeRestrictionTelescope`
retains the original Laurent action, seed, transitions and every telescope
cylinder under arbitrary scheme restriction.
`CoefficientBassNegativeMapNaturality` gives the original negative-class
restriction square between compact endpoints.

## Fine transition ranges and original groups in the completion

For qcqs `P.left`,
[`CoefficientBassFineConnectiveInvertibility`](CoefficientBassFineConnectiveInvertibility.lean)
transports connective invertibility of the original raw seed through the
constructed whole one-step evaluation to the unchanged fine seed. The original
signed forward-unit quotient and native chart exactness supply the raw
connective calculation in `CoefficientBassConnectiveInvertibility`.
Neither calculation requires an all-stage raw comparison.

Write `E_i(a)` for the ambient fine coefficient stage at `a : Under R`.
[`CoefficientBassFineRangeInvertibility`](CoefficientBassFineRangeInvertibility.lean)
and [`CoefficientBassFineTelescopeComparison`](CoefficientBassFineTelescopeComparison.lean)
prove that the original transition `E_i(a) → E_(i+1)(a)` and the original
inclusion `E_i(a) → E_∞(a)` induce isomorphisms in every degree `d ≥ -i`.
The negative comparison is exactly the original finite-bottom comparison
followed by this inclusion; it is coefficient-natural and preserves the
original recursive Laurent quotient. `CoefficientBassConnectiveTelescopeComparison`
likewise identifies every original connective K-group with the fine telescope
through the original evaluation and stage-zero inclusion.

For an open immersion `f : P ⟶ Q` with compact `P.left` and qcqs `Q.left`,
`CoefficientSupportedConnectiveInvertibility`,
`CoefficientSupportedNegativeMiddleExactness` and
`CoefficientSupportedBottomChartExactness` supply the supported seed and
bottom-row inputs. `CoefficientSupportedFineRangeInvertibility` proves the
same range `d ≥ -i` for every unchanged supported transition.
`CoefficientSupportedFineTelescopeComparison` and
`CoefficientSupportedConnectiveTelescopeComparison` identify the original
negative and connective supported groups with this same fine completion,
naturally on all of `Under R`. Their degree-zero forward maps agree literally.
`CoefficientSupportedNegativeTelescopeForget` preserves the original
support-forgetting maps and Laurent representatives through the actual
ambient and supported inclusions. These are identifications with the
constructed fine completion; the original raw all-stage tower and its
classical interpretation remain separate.

## Raw identity and second-stage coherence

[Original raw evaluation](RawEvaluation.md) develops the coefficient
identity/composition cubes and objectwise second seed, the remaining
coefficient overlap-cell attachment, and the integer-base raw construction
on arbitrary schemes. In the latter construction, whole one-step evaluation
naturality, the prescribed initial mixed seed comparison and the
transition-identity square are constructed. There is also a whole
polynomial-span composition law and supported raw first-step objects with
original Laurent seeds. The remaining cone/step composition, supported
row/null comparison and coherent raw iteration have their distinct
boundaries there. None is a premise of the strict/fine section-completion
results in this guide.

## Telescope, localization map, and supported self-comparison

`Affine.SectionBassTelescope` is the actual reduced telescope with original
stage inclusions, heights, and `B^i(seed)` gluings. `SectionBassStableColimit`
gives the natural canonical colimit isomorphism in every integer stable degree.
All original stages and levels have proved T1 and chosen-point HEP, including
level zero. `SectionBassTelescopeCone` and `SectionBassTelescopeExcision`
identify the actual coefficient cone with the colimit of the original finite
cones and prove genuine stable cone-fiber equivalence and recurring signed
exactness. The boundary retains its finite-stage formula and original fiber
boundary; no whole-telescope connectivity premise remains.
`SectionBassTelescopeNaturality` preserves this boundary on commuting coefficient
squares. Generic strict cone/pushout interchange keeps independent cone time
and telescope height, with no extra separation or HEP assumption; parameter-loop
interchange is stable for T1 stages.

`SectionBassNegativeMap` composes the finite-bottom isomorphism with the original
stage inclusion. Its coefficient, Laurent quotient, and next-stage seed/cylinder
formulas are proved. The fine transition-range and telescope comparisons above additionally supply bijectivity under their qcqs hypotheses. `SectionLocalizedComparison` identifies the actual evaluation
inverse in stable localization, retaining original perfect K-maps.
`SectionBassLocalizedSpectrum` gives a natural initial map from the original
localized perfect spectrum to the actual telescope; it does not assert
nonnegative-group isomorphisms. The connective spectrum's own negative stable
groups still vanish.

`SectionBassTelescopeLooping`, `SectionBassTelescopeCommutation`, and
`SectionBassTelescopeSelfMap` assemble actual interchange and tail maps into a
coefficient-natural stable map from this telescope to its Bass image in every
integer degree. Its initial face is exactly the original Laurent seed followed
by Bass of the original initial inclusion. The construction retains all original
transitions and independent cylinder/loop parameters, without assuming any
finite transition stable. This self-comparison alone does not identify classical
negative groups of the telescope.

For `j : U ⟶ Spec R` with `[IsOpenImmersion j]`,
`Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange` chooses one actual
pullback of `j` for each object of `Under R`. The projection equations and strict
coefficient laws use those same endpoints; the identity-algebra projection is
an isomorphism to `j`, rather than equality of chosen opens.
`BoundedFlat.SupportedSectionDiagram` uses the actual supported sections and
exact coefficient reindexing. `SupportedSectionComparison` normalizes evaluation
by a canonical zero-object isomorphism, and `SupportedSectionSpectrumEquivalence`
gives whole inverse homotopies, complete weakness at every level, and all-integer
stability. `SupportedSectionModelNaturality` gives an actual whole coefficient
track, rather than strict evaluation naturality.

`Affine.SupportedSectionLaurentUnit`, `SupportedSectionDiagramLaurent`, and
`SupportedSectionBassSeed` give the genuinely natural fixed-open Laurent seed
with original scalar parameters, zeros, and null cylinders. No seed/coherence
hypothesis is supplied. The separately expanded evaluated-term scalar transfer
is not a premise. `SupportedSectionForgetLaurent` and `SupportedSectionForgetSeed`
prove the actual support-inclusion scalar and strict seed squares;
`Quillen.KTheory.Bass.StrictUnderDiagram` retains restriction along `Under.forget`.
`SupportedSectionBassTower` and `SupportedSectionBassForgetTower` give the
supported finite stages, actual telescope, and maps to all ambient stages and
the ambient telescope.

`SupportedSectionBassTelescopeSelfMap` is a stable map to the supported
telescope's Bass image at every coefficient and integer degree. The original
supported Model and Bass topology discharge its T1 premises.
`SupportedSectionBassTelescopeSelfMapForget` proves the whole square with the
existing support-forgetting telescope arrow and unchanged ambient self-map;
no compatibility assumption remains. The identity algebra retains the actual
pulled-back open. These self-comparisons alone do not supply stabilization or full-open localization; the separate fine-range and localization theorems above supply those conclusions with their additional hypotheses.

## Relative-open sections and scalar cofibers

Native joint scheme/coefficient sections supply global coarse/fine/graded
Models, actual cofinality and K₀ image exactness, canonical nulls, original
Laurent seeds and whole seed/null compatibility. `CoefficientOpenBassTower`
and `CoefficientOpenBassTelescope` retain those finite stages and transitions;
the actual graded contraction makes the original coarse-to-fine completion
restriction stable in every integer degree for qcqs ambient schemes and
quasi-compact opens. `CoefficientSupportedSections` and
`CoefficientSupportedOpenModels` supply the actual auxiliary-supported Models,
with supported cofinality and completed localization supplied by the dedicated interfaces below.
`SupportedOpen.GrothendieckPullback`, `ImageQuotientPullback` and
`CoefficientSupportedOpenGrading` supply the actual supported quotient
and G_Z/q_Z, retaining original relative-image witnesses; their coefficient
action needs compact P/Q, while pointwise grading has no compactness premise.
Their cofinality, canonical null, signed cones, and completed localization are supplied by the dedicated supported interfaces below.
`CoefficientSectionEvaluationNaturality`, `CoefficientSectionEvaluationUnit`
and `CoefficientLaurentEvaluation` preserve the actual evaluation tracks and
forward units. Complete raw-iterate/telescope geometric comparison and classical Kᴮ
identification remain open; see the [classical comparison boundary](../Development.md).

`BoundedFlat.OpenConeComparison` proves the actual geometric acyclic-support
cone stably equivalent to the original coarse relative-open S-prespectrum in
every signed degree, with the original target face, null cylinder, and signed
connecting map. Its geometric fibration and S-model excision premises are
discharged. This is the coarse endpoint, retaining the genuine K₀ image
obstruction to replacement by full open perfect K-theory.

[`SupportedOpen.ConeComparison`](../SupportedOpen/ConeComparison.lean)
packages the original perfect-complex auxiliary-support coarse comparison for
arbitrary schemes and opens, with the same signed boundary.
[`SupportedOpen.ExcisionSpectrum`](../SupportedOpen/ExcisionSpectrum.lean)
realizes cover support excision by the original normalized restriction spectrum
map and retains its original K-map in every nonnegative degree, including zero.
Neither interface requires compactness or constructs a global completed theory.

`BoundedFlat.SectionOpenEquivalence` and `SectionOpenComparison` give exact
evaluation for the section coarse relative-open weak class and whole two-sided
prespectrum homotopies. The comparison is completely weak at every level and
stable in every integer degree; the fine/coarse square retains the unchanged
maps. `SupportedSectionOpenNull` reverses the actual weak zero-to-supported-section
transformation, producing the specified coherent null cylinder of forgetting
support followed by relative-open restriction. `SupportedSectionAcyclicEvaluation`
and `SupportedSectionAcyclicComparison` supply its exact source evaluation;
`SupportedSectionOpenNullNaturality` retains the entire reversed null track.
[`BoundedFlat.SupportedSectionOpenConeComparison`](SupportedSectionOpenConeComparison.lean)
then proves `boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence`
for every open immersion into an affine base, in every signed degree.
Its connecting equation keeps the original fiber lift and null cylinder.
The endpoint is the coarse relative-open section Model; replacing it by the
full open endpoint retains a further comparison.

`OpenConeFiberLoop` gives the genuine supported mapping cone and canonical
fiber loop of an open-weak perfect arrow. `Affine.PolynomialScalarCone`
specializes to the global polynomial `X`, restricting to Laurent unit `T`:
its actual termwise scalar map is weak on that open. `ScalarCofiber` identifies
the original categorical cofiber with this supported cone and transports the
relative-acyclic K₀ class equality through the unchanged canonical fiber map.
`Quillen.Aglib.CategoryTheory.Limits.Shapes.CokernelPushout` retains the displayed zero;
`Quillen.Waldhausen.SplitComplexes.FactorizationCofiber` retains the genuine
factorization extension object, quotient, and target inclusion.
`Quillen.Aglib.Algebra.Homology.MappingCone.Sign` identifies `Cone(-f)` with `Cone(f)`
by negating only the shifted source and fixing the target, and
`SplitComplexes.FactorizationSign` uses that exact sign isomorphism.

[`CofiberObjectTrack`](../../../Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean)
gives `Quillen.Waldhausen.Structure.cofiberObjectLoopTrack` for a displayed
cofibration and its zero-pushout quotient, in a category with zero morphisms.
When the cofibration is weak,
[`CofiberPrismComposition`](../../../Waldhausen/GrothendieckComparison/CofiberPrismComposition.lean)
gives `Quillen.Waldhausen.Structure.cofiberPrismCompositionLoops`. The actual
source–quotient–middle triangle and its cubes retain independent nerve,
comparison, and loop coordinates. The canonical
fiber transport retains literal left concatenation and the prescribed
identity-cofiber suffix; its normalization on the first homotopy group of the
loop space agrees with that of the standard suffix-removal path. This agreement
does not identify the full paths.

For an open immersion `j : U ⟶ X`, a global scalar `r : Γ(X, ⊤)`, a specified
unit `q : Γ(U, ⊤)ˣ` with `j.appTop r = ↑q`, and `K : Perfect X`,
[`ScalarCofiberSourcePath`](../ScalarCofiberSourcePath.lean),
`ScalarCofiberIteratedFiber`, and `ScalarCofiberPasting` compute the canonical
iterated-fiber loop of the actual supported scalar cofiber. The source scalar
need not be a unit and no qcqs assumption is added.
[`perfectScalarCofiberBoundaryOrientation`](../ScalarCofiberBoundaryOrientation.lean)
is an endpoint-relative homotopy to the parameter reversal of the original
forward weak scalar square. It remains at `K`'s original object-loop component.
[`perfectScalarCofiberFiberBoundaryPath`](../ScalarCofiberFiberBoundaryPath.lean)
keeps the prescribed path from its loop inclusion to the translated canonical
fiber point. The two original triangles and fine weak projection determine
these paths; no replacement scalar or fiber map is chosen.

[`ScalarCofiberKOneNormalization`](../ScalarCofiberKOneNormalization.lean)
uses inverse-prefix translation and a specified cancellation path to normalize
the actual object-loop component to coarse K₁, without assuming its K₀ class
vanishes. This normalization is the inverse of the existing identity-cofiber
component equivalence. The boundary class equals the inverse of the independently
normalized forward scalar square, including the literal polynomial-coordinate
specialization. Identification with the independently prescribed Laurent
automorphism class, its connecting-map formula, the zero-section pushforward
class and possible Nil terms remain separate. No blanket perfect zero-section
dévissage is asserted.

## Graded full-open coefficient diagrams

Fix an open immersion `j : U ⟶ Spec R`. At `a : Under R`, the full-open
section category is the category of actual cocartesian sections of the
bounded-flat pullback pseudofunctor over `Under a`. Original evaluation lands
on the specified pullback open `openSpace j a`; its perfect K₀ class modulo
the image of the actual relative-open restriction is the section grade.
Only weak equivalences change to endpoint-grade equality. The inherited zero,
objects, and cofibrations remain those of the full-open section category.
The Models and prespectra live in universe `u + 1`.

The pointwise original restriction is now
`boundedFlatAffineSectionFullOpenModelMap j a` in
[`BoundedFlat.FullOpenSectionRestrictionModel`](FullOpenSectionRestrictionModel.lean).
It is an exact Model morphism with literal preservation of the entire chosen
zero section, for every open `j` and coefficient `a`. Likewise
[`FullOpenGradedSectionStable`](FullOpenGradedSectionStable.lean)
proves `boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd`
for each `d : ℤ` with `d ≠ 0`, without requiring compactness of `U`.
[`Consumer.FullOpenGradedSectionStable`](../../../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean)
uses that concentration for any supplied morphism between the actual graded
Models; it does not construct a missing comparison or settle degree zero.

For the coefficient **diagrams** below, additionally assume `[CompactSpace U]`.
The coefficient category is `Under R`, with arbitrary ring coefficient arrows;
neither coefficient flatness nor affineness of `U` is assumed. Actual quotient
pullback and its original evaluation equation make reindexing exact for grade
weakness. `BoundedFlat.FullOpenGradedSectionDiagram` gives a strict Model diagram,
its iterated-S prespectrum diagram, and the natural fine-to-graded map `q`.

The geometric Laurent and Bass imports under
`Quillen.AlgebraicGeometry.PerfectComplexes.Affine` expose the following
interfaces, with declaration names in `Quillen.PerfectComplexes`:

| Module | Coefficient-compatible result |
| --- | --- |
| [`FullOpenGradedLaurentContraction`](../Affine/FullOpenGradedLaurentContraction.lean), [`FullOpenGradedLaurentContractionNaturality`](../Affine/FullOpenGradedLaurentContractionNaturality.lean) | The whole forward-`T` Laurent self-track contracts to the constant track of the same coefficient map, naturally at both independent times |
| [`FullOpenSectionBassSeedChangeWeak`](../Affine/FullOpenSectionBassSeedChangeWeak.lean) | `boundedFlatAffineFullOpenSectionBassSeed_changeWeak`: `seedFine ≫ Bass.map(q) = q ≫ seedGraded` |
| [`FullOpenGradedSectionBassSeedDiagramNull`](../Affine/FullOpenGradedSectionBassSeedDiagramNull.lean) | The original graded Bass seed has a constructed whole coefficient-natural null |
| [`FullOpenGradedSectionBassTransitionNull`](../Affine/FullOpenGradedSectionBassTransitionNull.lean) | Every unchanged transition has zero stable map for every stage `k : ℕ`, coefficient `a`, and signed degree `d : ℤ` |
| [`FullOpenGradedSectionBassTelescope`](../Affine/FullOpenGradedSectionBassTelescope.lean) | Every original stage inclusion has zero stable map, and the actual graded reduced telescope has subsingleton stable groups in every integer degree |

The Laurent contraction fixes its action endpoints and full basepoint line;
it contracts a self-track, not the underlying coefficient map to zero. Its
chosen zero endomorphism is weak by reflexivity of the endpoint grade.
The resulting seed null retains the actual strict-square source-leg cone null,
the reversed null path, and the original forward Laurent action. This null is
constructed from the contraction, rather than supplied as a hypothesis.
The telescope argument uses the original seed transitions and finite-stage
representatives, without an assumption that individual stage groups vanish.
Generic iteration and telescope machinery are described in
[spectral and Bass interfaces](../../../KTheory/Bass/README.md).

The actual fine tower/telescope and induced finite/telescope q maps are provided
by `Affine.FullOpenSectionBassTower`, `FullOpenSectionBassTelescope`,
`FullOpenSectionBassGradingTower` and `FullOpenSectionBassGradingTelescope`.
Fine constructions require only an open immersion; grading retains compact U.

[`FullOpenSectionRestrictionDiagram`](FullOpenSectionRestrictionDiagram.lean)
gives the original coefficient-natural r, and
[`FullOpenSectionGradingNull`](FullOpenSectionGradingNull.lean)
constructs its whole coefficient-natural null followed by q.
[`FullOpenSectionConeStable`](FullOpenSectionConeStable.lean)
proves the actual null descent `Cone(r) → G` stable in every signed degree.
Its zero comparison uses genuine restriction image exactness; the degree-one
kernel uses restriction K₀ injectivity. `Affine.FullOpenSectionBassRestrictionTower`
retains that same null and stable cone descent at every finite Bass stage.

[`FullOpenSectionSpectrumComparison`](FullOpenSectionSpectrumComparison.lean)
gives a pointwise stable evaluation from the actual direct section Model to the
explicitly lifted bounded-flat original prespectrum. Compact U makes the
composed perfect evaluation stable. The original K-equations and chosen-zero
normalization remain explicit; no seed or telescope evaluation is inferred.

[`FullOpenSectionRestrictionSeed`](../Affine/FullOpenSectionRestrictionSeed.lean)
proves the original r seed square, and
[`FullOpenSectionGradingNullBassSeed`](../Affine/FullOpenSectionGradingNullBassSeed.lean)
proves the canonical-null time-slice seed squares with the actual Laurent tracks.
[`FullOpenSectionBassRestrictionCofiber`](../Affine/FullOpenSectionBassRestrictionCofiber.lean)
forms the original compatible telescope null and proves r∞ stable in every
integer degree by its stable cone descent and graded vanishing.
[`FullOpenSectionBassLocalization`](../Affine/FullOpenSectionBassLocalization.lean)
then gives the supported cone and fiber comparisons to the fine completion,
with the same whole null and original signed boundary. The downstream
`Consumer.FullOpenSectionComparison` constructs the actual localized coefficient
diagram isomorphisms and their natural inverses.

For arbitrary open arrows over `Spec R`, `BoundedFlat.CoefficientOpenSections`
and `CoefficientOpenGrading` construct actual global C/F/G and coefficient-natural
r/q, using the joint native geometry and one global zero. C/F/r require no
compactness; the graded coefficient diagram requires compact source and ambient
schemes. Global cofinality, honest K₀ image exactness, canonical nulls and
original Laurent seed/tower transfer are proved. The actual native supported
cone and same-null fiber compare stably to the fine completion for qcqs
ambient schemes and compact opens, with the original signed boundary, in
`CoefficientFullOpenBassLocalization` and its Models/Seed/Tower/Telescope owners.

Auxiliary support has the actual supported cofinality, K₀ image/kernel,
coefficient-natural null and all-integer initial cone comparison in
`CoefficientSupportedOpenCofinality`, `CoefficientSupportedOpenKZeroExact`,
`CoefficientSupportedOpenNull` and `CoefficientSupportedOpenConeStable`.
Cofinality and cone stability require compact P,Q,T and quasi-separated Q;
image/kernel requires compact P,Q, and q₀ surjectivity only compact P.
`CoefficientSupportedOpenBassSeed` and `SeedCompatibility` supply the
original supported seeds and every whole-null seed square. The original
`CoefficientSupportedOpenBassTower` and `BassTelescope` retain the literal finite
stages, original telescope null, all-signed graded vanishing and stable r_Z∞,
under the same compact P,Q,T and quasi-separated Q conditions for the final
comparison. `CoefficientSupportedFiberLocalizationModels` and its
Seed/Tower/Telescope owners construct the actual union-support fiber,
literal forget/changeWeak maps and the same-joint-zero whole null.
`CoefficientSupportedFullOpenBassLocalization` supplies its same-null stable
fiber comparison to this fine supported completion and original signed
boundary. Fiber-to-coarse stability and structural identities need only the
open immersion; final fine stability requires compact P,Q,T and
quasi-separated Q. This is constructed section-completion localization.

`CoefficientSectionEvaluationSourceLeg` supplies original source-leg movement and raw-cone two-time interchange. `CoefficientSectionEvaluationTopology` supplies the actual e/V levelwise equivalences and span/cone/loop HEP/T1. `CoefficientSectionEvaluationComposition` proves normalized pasting, the relative split-track comparison, and both chart/cylinder faces, without openness, compactness, or flatness. The source-null/seed comparison is supplied by `CoefficientSectionEvaluationSeedComparison`; complete original raw iteration retains the boundary in [raw evaluation](RawEvaluation.md).

The projective-line geometric inputs have their own [source-family authority](../ProjectiveLine/README.md): determinant-normalized tensor and pullback mates, intrinsic-perfect quasicoherent/strict representatives, actual derived projection perfection, natural generation on genuine roofs, and both original K-inverse laws. Older objectwise projection or strictification criteria do not retract those later results. The [classical comparison guide](../Development.md) keeps the raw-cell and external classical Kᴮ boundaries separate from the native current-stage endpoint above.

## Finite normalization and original group interfaces

The [finite normalization and telescope guide](../../../KTheory/Bass/README.md#current-stage-and-iterated-seed-telescopes)
keeps the actual strengths, fixed loop words and stable zigzag
`I → T ← N ← C`. Original `B^i(seed)` transitions and current-stage seed
transitions remain separately defined; the comparison uses their proved
adjacent squares. The [row interfaces](../../../KTheory/Bass/RowInterfaces.md)
construct independent tensor cells, normalized forward operations, input
squares, row presentations and ordinary-colimit presentations for the stated
strict Model diagrams and tracks.

The coefficient transformations `r` and `q`, canonical null, original
Laurent units and Bass seeds use one coherent choice of coarse/fine/graded
Models and section zeros. Their two-time interchange and whole seed equation
retain those exact tracks. The initial cone comparison uses the honest K₀
image quotient, restriction K₀ injectivity in degree one, and positive
cofinality. Its null input is this constructed null before passage to a
telescope.

The finite stages `E_i = B^i(E₀)` have actual transitions
`t_i = B^i(η)`, where `η` is the original seed. The following results retain
the common-corner map and positive-minus-inverse chart difference in each
stable degree, together with these original transitions and inclusions.

| Interface | Supplied result and conditions |
| --- | --- |
| Actual spectral row | `ModelDiagramTwoChartStableSequence` and `CoefficientTwoChartStableSequence` realize the original signed span quotient and natural all-degree short exact row for the actual ambient, open, supported and auxiliary-supported finite Models under their original constructor hypotheses. Polynomial zero evaluation, finite Model excision and cone collapse supply the structural inputs. |
| Original middle exactness | `CoefficientBassMiddleIteration`, `CoefficientBassNegativeMiddleExactness` and the corresponding supported MiddleTransport/MiddleIteration/NegativeMiddleExactness owners preserve the whole common-corner/signed-difference row through independent-variable product transport and actual K₁ contractions. Ambient schemes are qcqs; the supported negative middle row additionally has compact removed open. The natural splitting and contraction transport, rather than right exactness alone, supply the induction. |
| Original connective seed | `CoefficientBassConnectiveInvertibility` identifies the original raw seed with the signed forward-unit quotient and actual fine spectral left map. `CoefficientBassFineConnectiveInvertibility` transports it through the whole one-step evaluation. `CoefficientSupportedConnectiveInvertibility` uses the original finite support-to-ambient cone square and whole-null transition naturality. Ambient is qcqs; the supported theorem also requires compact removed open. No geometric first-coordinate boundary identification is assumed. |
| Full transition range | `CoefficientBassFineRangeInvertibility` and `CoefficientSupportedFineRangeInvertibility` prove the original stage-i transition invertible for every `d ≥ -i`, including equality. The bottom chart exactness controls the endpoint of the inter-stage short-exact-row induction. |
| Canonical original legs | FineTelescopeComparison proves the original stage-i inclusion invertible in that same range. The negative comparison is the original finite-bottom map followed by that inclusion, and its Laurent quotient equation is retained. ConnectiveTelescopeComparison uses the original stage-zero evaluation and inclusion; no different colimit leg is substituted. T1 is supplied by the actual Model levels. |
| Original forget/restriction | The finite supported comparison and `CoefficientSupportedNegativeForgetComparison` need only an open immersion and compact ambient. `CoefficientSupportedNegativeTelescopeForget` uses compact removed open and qcqs ambient, retaining original quotient and inclusion faces. `CoefficientFullOpenBassRestriction` gives the literal open row/action/seed/telescope and equality of the actual localization map with original restriction on every cylinder. The latter equality needs only the open immersion; the original negative-map square needs compact endpoints. |
| Original nonpositive localization | `Bass.SupportedLocalizationExactness` and `Bass.SupportedLocalizationBoundary` use the same-null fine cone sequence and both actual identity-projection legs to give recurring exact original Bass groups for qcqs ambient and compact removed open. Current and normalized-row negative-class squares identify their own intrinsic boundary with this original negative boundary. The geometric K₁-to-supported-K₀ comparison has the explicit minus under the original stable perfect classes. |

The current/fine corrections on the original negative classes are identity
in every natural index, under the ambient qcqs and supported compact-open
hypotheses. Their proof uses the actual geometric quotient-swap sign and
loop-reversal sign separately; see
[finite Bass signs](../../../KTheory/Bass/SignComparisons.md). The auxiliary
Spec-row comparisons above preserve the original enlargement, restriction
and entire null through the finite stages and telescopes. Their independent
normalized classes and intrinsic boundary are developed in
[geometric connecting maps](GeometricBoundary.md).

These identifications concern the constructed fine/current/normalized rows.
The positive geometric boundary on every original perfect class has a single
minus with the unchanged class maps and degree cast. An unsigned geometric
square is therefore not asserted. Classical object, forward-transition and
whole-null correspondence, together with any separately required
arbitrary-pair naturality, retain their exact targets in the
[classical comparison guide](../Development.md).

## Declaration locators

These additional names use the same objects, hypotheses, and original maps as the linked construction sections. They are locators within those interfaces, not stronger comparison statements.

| Declaration / module | Construction and conditions |
| --- | --- |
| `boundedFlatAffineSectionPrespectrumFunctor`, `boundedFlatAffineSectionBassStepEvaluation` | [Strict sections and one-step evaluation](#strict-sections-and-one-step-evaluation) |
| `boundedFlatAffineSectionBassBottomComparison`, `boundedFlatBassFirstStableGroupIso` | [Finite-stage excision and bottom groups](#finite-stage-excision-and-bottom-groups) |
| `boundedFlatCoefficientAmbientNegativeKComparison` | [Finite-stage excision and bottom groups](#finite-stage-excision-and-bottom-groups) |
| `boundedFlatCoefficientAmbientBassNegativeMap`, [`Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurentSchemeNaturality`](https://github.com/kangxyz/aglib/blob/16aa08a90198d76be0bec47dd640b5c992acd9d7/Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurentSchemeNaturality.lean) | [Finite-stage excision and bottom groups](#finite-stage-excision-and-bottom-groups) |
| `boundedFlatAffineSectionBassNegativeMap`, `boundedFlatAffineSectionBassTelescope`, `boundedFlatAffineSectionBassTelescopeBassMap` | [Finite-stage excision and bottom groups](#finite-stage-excision-and-bottom-groups) |
| `boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget` | [Finite-stage excision and bottom groups](#finite-stage-excision-and-bottom-groups) |
| `boundedFlatCoefficientAmbientBassTransition_isIso_of_le` | [Fine transition ranges and original groups in the completion](#fine-transition-ranges-and-original-groups-in-the-completion) |
| `FixedWords` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `GeometricConeInterchange.permutation_equivariant`, `GeometricChiPermutation.comparison`, `wordAt_seed_square`, `SchemeIteratedSeedTransition.originalTransition_stageMap` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `modelDiagramIterateCofiberDesc_isStableEquivalence` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `strictDiagramIterateNull_transition` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `Telescope.coneDesc_isStableEquivalence` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `Algebra.Module.FiniteParametrix`, `Quillen.Module.finite_projective_parametrixKernel` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `Algebra.ModuleComplex.LaurentModuleCech` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `Affine.FullOpenSectionBassRestrictionCofiber` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `Affine.FullOpenSectionBassLocalization` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientOpenBassTower`, `BoundedFlat.CoefficientOpenBassTelescope` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientFullOpenBassLocalization` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientSupportedOpenBassTower`, `BoundedFlat.CoefficientSupportedOpenBassTelescope` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientSupportedFiberBassTelescope`, `BoundedFlat.CoefficientSupportedFullOpenBassLocalization` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientBassFineRangeInvertibility`, `boundedFlatCoefficientAmbientBassTransition_isIso_of_le` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientBassFineTelescopeComparison`, `boundedFlatCoefficientAmbientNegativeKTelescopeComparison` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientBassConnectiveTelescopeComparison`, `boundedFlatCoefficientAmbientKTelescopeComparison` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientSupportedNegativeBottomComparison`, `BoundedFlat.CoefficientSupportedNegativeForgetComparison` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientSupportedFineRangeInvertibility`, `BoundedFlat.CoefficientSupportedFineTelescopeComparison`, `BoundedFlat.CoefficientSupportedConnectiveTelescopeComparison` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientSupportedNegativeTelescopeForget` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `BoundedFlat.CoefficientFullOpenBassRestriction` | [Finite normalization and original group interfaces](#finite-normalization-and-original-group-interfaces) |
| `GlobalAuxiliaryParameterTelescopeSquares`, `GlobalAuxiliaryParameterTelescopeNull`, `ParameterAuxiliaryCurrentFiber`, `ParameterAuxiliaryCurrentLocalization` | [Global sections](#global-sections-and-coefficient-restriction) and [current-stage localization](#native-current-stage-full-open-localization) |
| `currentNegativeConnecting_eq_original`, `basicConnecting_original_negative_square`, `boundedFlatCoefficientFineConnecting_perfectClass_sign` | [Original classes and geometric connecting maps](GeometricBoundary.md) |
| `InputNaturality.stepHomotopy`, `InputIdentity.mapHomotopy`, `InputIdentitySeedSquare.square` | [Original raw evaluation](RawEvaluation.md) |
| `InputSeedNaturality.comparison`, `InputCompositionSpan.homotopy` | [Mixed seed routes and span composition](RawEvaluation.md#mixed-evaluation-input-and-seed-routes) |
| `GlobalSupportedRawBass.step`, `GlobalSupportedRawBass.transition`, `pullbackCompIso_two_routes` | [Supported raw first-stage rows](RawEvaluation.md#supported-raw-first-stage-rows) |
| `InputWeakZero.family_null`, `InputWeakZeroProduct.native`, `homotopyFiberLiftNaturalityHomotopy` | [Canonical weak-zero and full null-square interfaces](GeometricBoundary.md#canonical-weak-zero-and-homotopy-null-comparison) |

## Upstream coefficient primitives

The coefficient/base-change primitives moved to pinned Aglib owners. The assembled section, seed, whole-null and localization comparisons above remain Quillen constructions with their displayed hypotheses. These primitive imports alone do not supply those assembled comparisons.

- [Aglib/AlgebraicGeometry/BaseChange/Coefficients/Basic.lean](https://github.com/kangxyz/aglib/blob/16aa08a90198d76be0bec47dd640b5c992acd9d7/Aglib/AlgebraicGeometry/BaseChange/Coefficients/Basic.lean)
- [Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean](https://github.com/kangxyz/aglib/blob/16aa08a90198d76be0bec47dd640b5c992acd9d7/Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean)
- [Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurentSchemeNaturality.lean](https://github.com/kangxyz/aglib/blob/16aa08a90198d76be0bec47dd640b5c992acd9d7/Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurentSchemeNaturality.lean)
