# Spectra and Bass groups

The library constructs the original iterated-S Ω-spectrum and identifies its
nonnegative stable groups additively with the original Waldhausen K-groups,
including K₀. Its negative stable groups vanish. Bass negative groups are
separately defined by polynomial-to-Laurent cokernels. A strict spectral Bass
tower realizes each recursive group as the bottom stable group of its finite
stage and gives natural maps to the actual telescope. Bijectivity of these
telescope maps and identification with classical nonconnective K-theory remain
separate comparisons.

For a quasi-compact open of an affine scheme, a separate quotient-graded Bass
telescope has zero stable groups in every integer degree. Its constructed
natural Laurent-seed null supplies this vanishing. The original compatible
localization null now transfers the finite cone comparisons to the telescope,
giving constructed affine full-open section-completion localization.

This guide treats the generic spectrum interfaces and the affine spectral Bass
construction. The perfect-complex seeds, support categories, and geometric
localization comparisons belong to [PerfectComplexes.md](PerfectComplexes.md).

## Public imports

Individual modules provide the following selected interfaces. Import paths in
the table follow `Quillen.`; [the API reference](../reference/API.md) records
the larger declaration surface.

| Import | Principal interface |
| --- | --- |
| `Waldhausen.SConstruction.Iterated.StableHomotopy` | Original connective spectrum, `originalKStableEquiv`, negative vanishing |
| `Waldhausen.SConstruction.Iterated.StableFunctoriality` | Normalized exact-functor maps and original K-map naturality |
| `Waldhausen.SConstruction.Iterated.LocalizedFunctoriality` | `localizedSpectrumMap` and its strict laws |
| `Topology.Prespectrum.FiberSequence` | Actual path-space fibers and signed stable long exact sequence |
| `Topology.Prespectrum.ConeLinearExcision` | Cone-fiber excision with explicit growth and point HEP |
| `Topology.Prespectrum.DiagramNullHomotopy` | Coefficient-natural whole null tracks and original isomorphism transport |
| `Topology.Prespectrum.StrictSquareCofiberDescent` | Actual looped-cone/cofiber comparison and descent equations |
| `Topology.Prespectrum.TelescopeConeDescentStable` | Compatible null descent, stable comparison, and signed telescope boundary |
| `Topology.Prespectrum.TelescopeStableColimit` | T1 telescope stable-colimit comparison |
| `Topology.Prespectrum.LoopTailReplacementFiberEquivalence` | Ω replacement and its actual fiber comparison |
| `KTheory.Bass.StrictRingDiagram` | Bass endofunctor and transitions for a supplied strict seed |
| `KTheory.Bass.StrictDiagramIterateNull` | Bass iteration of prescribed natural null tracks on unchanged arrows |
| `AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups` | Ring-indexed cokernel recursion |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassNegativeMap` | Finite-stage bottom comparison and natural telescope class map |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeSelfMap` | Stable map from the ambient telescope to its Bass image |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTelescope` | All-integer vanishing of the actual graded `Under R` telescope for quasi-compact `U` |

The connective declaration namespace is `Quillen.Waldhausen.IteratedS`.
Generic spectral declarations use `Quillen.LoopPrespectrum`; its telescope
interfaces use the nested namespace `Telescope`. Group-level ring recursion
uses `Quillen.Bass`, strict spectral diagrams use `Quillen.KTheory.Bass`, and
the affine geometric spectrum constructions use `Quillen.PerfectComplexes`.

## The original connective S-spectrum

[`LoopPrespectrum`](../../Quillen/Topology/Prespectrum/Loop.lean) consists of
based spaces `Eₙ` and continuous based structure maps `Eₙ → ΩEₙ₊₁`.
Its morphisms retain the exact structure squares.
For `d : ℤ`, `stableHomotopyGroup E d` is the additive sequential colimit

```text
colim_n π_(d.toNat + n + 2)(E_((-d).toNat + n + 2)),  n : ℕ.
```

These degrees are at least two, so the diagram uses abelian groups throughout.
[`StableHomotopy`](../../Quillen/Topology/Prespectrum/StableHomotopy.lean)
defines the original structure-induced transitions and stage inclusions.

`originalPrespectrum W` uses the actual iterated S-construction and its original
cylinder transitions. For `W : Structure C`, where `C : Type u` and
`[Category.{v} C]`, its spaces lie in universe `max u v` through the genuine
small model. [`originalPrespectrum_isOmega`](../../Quillen/Waldhausen/SConstruction/Iterated/OmegaSpectrum.lean)
proves complete weakness of the unchanged structure maps. The additive
equivalence `originalKStableEquiv W n` identifies `Additive (W.K n)` with
`stableHomotopyGroup (originalPrespectrum W) (n : ℤ)` for every `n : ℕ`.
The degree-zero comparison retains the group law; the older
`originalZeroSpaceEquiv` is only a set equivalence.
[`originalStableHomotopyGroup_neg_subsingleton`](../../Quillen/Waldhausen/SConstruction/Iterated/StableHomotopy.lean)
gives vanishing in every negative degree.

For an arbitrary exact functor, `exactOriginalPrespectrumMap` and
`exactOriginalOmegaSpectrumMap` canonically normalize its value on the chosen
zero. `originalKStableEquiv_exact_naturality` retains the public `KMap`, without
requiring equality of the original zero image.
[`StableFunctoriality`](../../Quillen/Waldhausen/SConstruction/Iterated/StableFunctoriality.lean)
gives identity, composition, and weak-natural-transformation laws for
`exactStableKMap`. These original exact-functor statements use source and target
categories in common object universe `u` and common morphism universe `v`;
independence of `u` and `v` does not assert arbitrary cross-universe transport.

The normalized prespectrum maps have whole coherent based identity and
composition homotopies. Their composition tracks come from the genuine
transformation two-simplex, retaining all three cylinder faces.
[`PrespectrumCompositionHomotopy`](../../Quillen/Waldhausen/SConstruction/Iterated/PrespectrumCompositionHomotopy.lean)
and the normalization/pasting owners keep comparison, path or loop, and
structure parameters independent, including level-zero loops. Object tracks
also retain their original paths: [`CanonicalFiberObjectLoop`](../../Quillen/Waldhausen/Fibration/CanonicalFiberObjectLoop.lean)
records both fiber coordinates and the reversed zero-to-acyclic track.
For an exact model equivalence, [`ExactModelEquivalence`](../../Quillen/Waldhausen/SConstruction/Iterated/ExactModelEquivalence.lean)
retains a zero-preserving forward functor, normalizes its exact inverse, and
constructs whole unit/counit homotopies and levelwise homotopy equivalences.

## Stable fibers and categorical localization

`parameterLooping` transposes the loop and structure coordinates. Its signed
comparison `parameterStableHomotopyIso E d` identifies degree `d` with degree
`d+1` of `E`. The stage formula has sign `(-1)^n` and tail offset
`parameterStableOffset d`, equal to one for `d < 0` and zero otherwise.
This is the parameter-correct construction in
[`StableShift`](../../Quillen/Topology/Prespectrum/StableShift.lean); it is
distinct from `looping`.

For every map `f : E ⟶ F`, `homotopyFiber f` is an actual path-space
prespectrum. [`stableFiberLongExactSequence`](../../Quillen/Topology/Prespectrum/FiberSequence.lean)
supplies the three recurring exactness positions in

```text
π^st_(d+1)(E) → π^st_(d+1)(F) → π^st_d(Fib f) → π^st_d(E) → π^st_d(F).
```

The boundary is the inverse signed parameter-loop shift followed by the
literal loop-to-fiber inclusion. Whole coherent based squares supply fiber
maps and boundary naturality. Ω inputs give an Ω fiber, including the component
conditions. Vanishing of every integer fiber group detects stable equivalence.
For connective inputs, [`stableFiber_neg_subsingleton_of_connective`](../../Quillen/Topology/Prespectrum/FiberConnectivity.lean)
requires surjectivity of the actual degree-zero map.

In the Waldhausen fibration theorem,
[`canonicalFiberPrespectrumMap_isStableEquivalence_general`](../../Quillen/Waldhausen/Fibration/SpectrumComparison.lean)
retains coarse two-out-of-three, `ExtensionAxiom`, `RowFactorization.JointData`,
and `RowFactorization.SecondEndpointSection`. The same construction proves
the relevant original K₀ surjectivity; connectivity of the fiber is not assumed.

[`StableLocalization`](../../Quillen/Topology/Prespectrum/StableLocalization.lean)
first forms `CoherentHomotopyCategory` by quotienting whole coherent based
homotopies, then inverts maps inducing isomorphisms in every integer stable
degree. `localizedStableHomotopyFunctor` retains the original stable groups,
and `stableLocalizationLift` supplies the universal lift for a functor that
respects those homotopies and inverts stable equivalences.
`localizedSpectrumMap` has literal identity/composition laws and weak-transformation
invariance. `localizedSpectrumMapIso` requires bijectivity of every original
`KMap`, including K₀. This categorical localization does not supply a standard
stable model structure, triangulation, fullness, or continuous inverses.

## Finite HELP and cone-fiber excision

`IsHomotopyConnectedMap` uses nonempty actual fibers and vanishing homotopy
sets below the finite bound at every fiber point.
[`cube_fullHELP`](../../Quillen/Topology/HELP/Connectivity.lean) fills cubes
through that bound while retaining the entire prescribed boundary homotopy.
The independent client [`Consumer.FiniteHELP`](../../examples/downstream/Consumer/FiniteHELP.lean)
uses complete weak equivalence, full finite cube HELP, degree zero, and the
empty-source obstruction. Finite cube HELP supplies no arbitrary compact HELP.

For `p`- and `q`-connected attaching maps, the original double-cylinder gap is
`r`-connected when `r + 1 ≤ p + q`. The
[`gap_isHomotopyConnectedMap`](../../Quillen/Topology/DoubleMappingCylinder/GapConnectivity.lean)
statement includes fiber nonemptiness and every fiber point, without separation,
CW, attaching-cofibration, or connectivity-growth premises.

For `f : E ⟶ F`, the canonical comparison is
`mappingConeFiberComparison f : E ⟶ homotopyFiber (mappingConeInclusion f)`.
Its fiber path is the original cone cylinder. Cone-fiber excision means stable
equivalence of this specified map.
[`ConeLinearExcision`](../../Quillen/Topology/Prespectrum/ConeLinearExcision.lean)
requires chosen-point HEP and all-point vanishing in degrees `k < n+2` at
levels `n+c+2`, for a fixed `c : ℕ`. The original S-level growth and point HEP
discharge this comparison for original S-model maps in
[`Iterated.ConeFiberExcision`](../../Quillen/Waldhausen/SConstruction/Iterated/ConeFiberExcision.lean).

The resulting signed cone sequences retain the original inclusion and boundary.
Whole cone/pushout homotopy squares need their supplied tracks and explicit
row-excision premises; equality of stable maps alone does not supply those
tracks. Finite Bass stages below discharge their own excision hypotheses.
General stable cone excision for arbitrary prespectra remains separate, as does
any levelwise weak-equivalence criterion inferred solely from a trivial cone.

## Natural null tracks and cofiber descent

For strict diagrams `F,G,K : C ⥤ LoopPrespectrum` and transformations
`a : F ⟶ G`, `b : G ⟶ K`,
[`DiagramNullHomotopy`](../../Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean)
records whole based nullhomotopies of `a.app X ≫ b.app X` and their coefficient
naturality at the same null time. Transport through specified diagram
isomorphisms and their two commuting arrow squares retains the actual
pre/postcomposition maps and unchanged time.
`mappingConeDiagram` and `mappingConeDescTransformation` give the corresponding
strict cone diagram and natural descent. `mappingConeDesc_naturality` requires
the actual target square and equality of the supplied whole null tracks.

`StrictSquare.sourceNullHomotopy` retains the original source-leg cone cylinder.
The looped-cone/cofiber comparison and its descent equation in
[`StrictSquareCofiberDescent`](../../Quillen/Topology/Prespectrum/StrictSquareCofiberDescent.lean)
retain the four original corners and their whole zero-composite homotopy.
Stable equivalence of this comparison keeps the two cone-fiber excision
premises explicit. For individual spectra `E₀,E₁,E₂`, maps `f : E₀ ⟶ E₁`,
`g : E₁ ⟶ E₂`, and a supplied whole null of `f ≫ g`, the degree-zero criterion
[`mappingConeDesc_stable_zero_bijective`](../../Quillen/Topology/Prespectrum/ConeDescZeroComparison.lean)
requires cone-fiber excision for `f`, vanishing of `π^st_(-1)(E₀)`, exactness of
`π^st_0(E₀) → π^st_0(E₁) → π^st_0(E₂)`, and surjectivity of the latter map.
Its conclusion is bijectivity in degree zero.

Compatible stage null tracks descend through the original telescope cylinders
with null time and cylinder height independent. `Telescope.coneIso_desc`
identifies that descent with the original cone/telescope interchange.
[`TelescopeConeDescentStable`](../../Quillen/Topology/Prespectrum/TelescopeConeDescentStable.lean)
requires T1 stages and stagewise stable descents for the stable conclusion;
the signed boundary equation retains stagewise cone-fiber excision as its
hypothesis. These generic interfaces do not manufacture the geometric null or
comparison data needed to apply them.

## Telescopes and loop-tail Ω replacement

Reduced telescopes retain the original stage inclusions and cylinder coordinates.
For T1 stages, compact relative maps and whole homotopies have representatives
at common finite stages, with exact transition endpoints and eventual equality.
Their homotopy groups, including degree zero, and all integer stable groups are
the canonical sequential colimits; see
[`TelescopeRepresentability`](../../Quillen/Topology/Prespectrum/TelescopeRepresentability.lean)
and [`TelescopeStableColimit`](../../Quillen/Topology/Prespectrum/TelescopeStableColimit.lean).
The reduced telescope is T1 and its original stage inclusions are closed embeddings.

Strict and track-defined telescope maps retain their respective coefficient
squares or whole cylinders. Identity/composition homotopies fix each original
stage without a T1 premise; higher coherence between them is separate.
Stagewise stable equivalences descend under T1, while
[`TelescopeStableExactness`](../../Quillen/Topology/Prespectrum/TelescopeStableExactness.lean)
still requires the displayed stagewise exactness. Strict cone/pushout interchange
needs neither separation nor point HEP. Parameter-loop interchange is a stable
equivalence for T1 stages, retaining loop time and cylinder height.

The original stabilization `E → looping(tail E)` is an all-integer stable
equivalence. Its iterated telescope `loopTailReplacement E` is Ω under
levelwise T1, with complete weak structure maps and target-component coverage.
`loopTailReplacementFunctor` is a strict functor without T1; under source/target
T1 its natural unit is stable and it preserves and reflects stable equivalences.
[`LoopTailReplacementFiberEquivalence`](../../Quillen/Topology/Prespectrum/LoopTailReplacementFiberEquivalence.lean)
gives an actual stable fiber comparison that is completely weak at every level.
For genuine Ω-prespectra, [`isStableEquivalence_iff_levelwise_of_isOmega`](../../Quillen/Topology/Prespectrum/StableOmegaLevelDetection.lean)
requires neither T1 nor connectedness. Thus the unit is levelwise weak on Ω T1
inputs. Levelwise weakness on arbitrary inputs and cofiber preservation are
separate claims.

## Bass cokernels and the original Laurent seed

For `R : CommRingCat.{u}`, the additive Bass contraction is the cokernel of
`F(R[T]) ⊕ F(R[T]) → F(R[T,T⁻¹])`, with map `(a,b) ↦ F(plus)(a) - F(minus)(b)`.
[`contraction`](../../Quillen/KTheory/Bass/Contraction.lean) retains this
Laurent quotient, its two-chart kernel criterion, exactness, and unique descent.
`Quillen.Bass.negativeKFunctor i` starts with additive homotopical
`PerfectK (Spec R) 0`; its natural-number index `i` denotes degree `-i`.
`Quillen.PerfectComplexes.Bass.negativeKFunctor` and
`Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor` start with the scheme
and supported original K₀, respectively.
Scheme pullback uses quasi-compact schemes, and supported recursion requires
only quasi-compactness of the ambient base, with arbitrary vanishing open.
[`affineSchemeNegativeKIso`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassSchemeComparison.lean)
compares affine and scheme recursions naturally in
every nonpositive degree, with literal original K₀ at zero.
[`RightExactness`](../../Quillen/KTheory/Bass/RightExactness.lean) and
[`IterationExactness`](../../Quillen/KTheory/Bass/IterationExactness.lean)
preserve pointwise right exact sequences and cokernels through contraction
and every ring-indexed iterate. They supply no negative localization boundary.

The actual native zero section and its pair analogue now split polynomial
projection pullback in every recursive negative degree and every nonnegative
perfect K degree. `Bass.PolynomialZeroSection` and
`Bass.SupportedPolynomialZeroSection` retain the original common-corner
diagonal, its specified evaluation retraction and zero composite with the
original plus-minus chart difference. The supported open need not be compact.
Middle exactness, seed preservation and the stage-i colimit isomorphism do not
follow from this splitting alone.

The raw spectral step `affineBassStep R` is the parameter-looped cone of the
actual two-polynomial-chart comparison to the Laurent corner.
[`affineBassTransition`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassStep.lean)
uses the original Laurent-unit track and cone nullhomotopy. The bounded-flat
and perfect raw steps have the original comparison
`boundedFlatPerfectGeometricBassStepMap`, completely weak at positive levels
and stable in every integer degree.

[`PushoutIdentityFromUnitSquare`](../../Quillen/Topology/Prespectrum/PushoutIdentityFromUnitSquare.lean)
descends a supplied identical-leg unit square to a whole identity homotopy of
the actual reduced polynomial span. Both original chart tracks and every
cylinder value are preserved; constant pieces are contracted within the
relative comparison before the native three-side square descent. The native
polynomial producer supplies that square in `CoefficientPolynomialSpanUnit`.
This span identity does not supply the missing whole Bass comparison identity
or coherent raw iteration.

Cocartesian bounded-flat sections rectify coefficient pullback to the strict
diagram `boundedFlatAffineSectionPrespectrumFunctor`. Objects and morphisms
of the section category lie in universe `u+1`, although original bounded-flat
morphisms lie in `u`. Evaluation gives an all-level homotopy equivalence and
preserves original K-maps. [`SectionBassSeed`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean)
constructs the actual natural Laurent seed `F → B(F)`. The strict Bass
endofunctor retains the polynomial/Laurent square, and every transition is
`B^i` of this same seed. `boundedFlatAffineSectionBassStepEvaluation` is
completely weak at every level, including zero. Whole seed-evaluation homotopies
compare the original strict, raw bounded-flat, and perfect seeds without a
supplied compatibility premise. These comparisons do not identify the entire
original geometric tower with the strict tower.

## Finite bottom groups and telescope class maps

Write `Eᵢ(R) = (boundedFlatAffineSectionBassDiagram i).obj R` for the actual
strict finite stages. At level `n+i+2`, all homotopy sets of `Eᵢ(R)` in degrees
`k < n+2` vanish at every point. Its stable groups vanish below `-i`.
For maps between stages `i,j`, the original cone-fiber comparison is
`(2*n+2)`-connected at level `n+max(i,j)+2` and stably equivalent.
These finite bounds, point HEP, and exact filtered colimits also discharge the
signed cone sequence for the actual telescope coefficient maps; no uniform
whole-telescope connectivity is assumed.

[`boundedFlatAffineSectionBassBottomComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassBottomComparison.lean)
is a natural isomorphism from `Quillen.Bass.negativeKFunctor i` to the functor
`R ↦ π^st_(-i)(Eᵢ(R))`, for every finite `i`. It retains the recursive Laurent
quotient and negates only the second polynomial summand when comparing chart
sum with chart difference. The parameter-loop shift retains its genuine sign.
`boundedFlatBassFirstStableGroupIso` identifies the raw first-step group in
degree `-1`; evaluation transports it to the strict first stage. Equality with
the separately constructed all-stage bottom comparison at `i = 1` remains a
separate comparison.

For a compact native ambient scheme `P` over `Spec R`,
[`boundedFlatCoefficientAmbientNegativeKComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassOriginalNegativeComparison.lean)
identifies the original scheme `Bass.negativeKFunctor i` on each coefficient
fiber with degree `-i` of `boundedFlatCoefficientAmbientBassDiagram P i`.
The comparison is natural in every coefficient arrow. Its stage-zero map is
the original perfect K₀/evaluation comparison, and its successor retains the
original Laurent quotient through the genuine polynomial/Laurent product
isomorphisms.
[`CoefficientBassOriginalNegativeNaturality`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassOriginalNegativeNaturality.lean)
also preserves the original scheme pullback for every map over the fixed base
between compact endpoints. Supported comparisons and transition stabilization
remain separate.

[`boundedFlatCoefficientAmbientBassNegativeMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassNegativeMap.lean)
then sends each original native class through that comparison and the original
stage inclusion into the ambient coefficient telescope. Its Laurent quotient
equation retains the successor-stage inclusion, without a bijectivity claim.
The geometric
[`CoefficientPolynomialLaurentSchemeNaturality`](../../Quillen/AlgebraicGeometry/Scheme/CoefficientPolynomialLaurentSchemeNaturality.lean)
squares also preserve both products and both charts under arbitrary scheme-over-base
maps. The original ambient Laurent track and seed are preserved by arbitrary
scheme restriction in
[`CoefficientBassSchemeRestrictionTelescope`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassSchemeRestrictionTelescope.lean).
The resulting actual telescope map retains every original inclusion/cylinder
and its identity/composition laws.
[`CoefficientBassNegativeMapNaturality`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassNegativeMapNaturality.lean)
identifies the original negative-class restriction square with that same map
when both endpoints are compact. This proves naturality, without bijectivity
or stabilization.

[`boundedFlatAffineSectionBassNegativeMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassNegativeMap.lean)
composes the finite bottom isomorphism with the original stage inclusion into
`boundedFlatAffineSectionBassTelescope`. It is coefficient-natural and retains
the Laurent quotient and next-stage cylinder formulas, without injectivity,
surjectivity, or fixed-degree transition stabilization. The natural localized
initial map `affinePerfectBassTelescopeInitial` likewise asserts no nonnegative
group isomorphism. Bass/telescope commutation and the tail map construct
`boundedFlatAffineSectionBassTelescopeBassMap`, a stable map from this actual
telescope to its own Bass image in every integer degree. Its initial face is
the original Laurent seed followed by Bass of the original initial inclusion;
no finite seed transition is assumed stable.

For any open immersion `j : U ⟶ Spec R`, the supported section tower and
telescope are strict diagrams over `Under R`, using the actual pulled-back
open at each coefficient. Their Laurent seed and T1 premises are discharged.
[`SupportedSectionBassTelescopeSelfMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionBassTelescopeSelfMap.lean)
gives the all-integer stable map to the supported telescope's Bass image, and
`boundedFlatAffineSupportedSectionBassTelescopeBassMap_forget` retains its
whole commuting square with support-forgetting and the unchanged ambient map.
At the identity algebra the chosen open is related to `j` by its projection
isomorphism. The geometric support/localization endpoint and its remaining
Laurent-boundary obligations are described in
[PerfectComplexes.md](PerfectComplexes.md).

## The quotient-graded full-open Bass telescope

Fix `R : CommRingCat.{u}` and an open immersion `j : U ⟶ Spec R`.
The full-open section model at `a : Under R` evaluates on the specified
pullback open `openSpace j a`. Its quotient grading is the raw-perfect K₀ class
modulo the image of the original relative-open restriction. Grade equality
coarsens weak equivalences while retaining the original objects, cofibrations,
and chosen zero. These Models and their spectra lie in universe `u+1`.
The pointwise restriction Model map preserves the whole chosen zero section
literally. The geometric definitions and restriction comparison are described
in [PerfectComplexes.md](PerfectComplexes.md).

For every such open `j`, the initial graded Model has zero stable groups in
degrees `d ≠ 0`, without a compactness assumption. The independent client
[`Consumer.FullOpenGradedSectionStable`](../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean)
uses this concentration to prove that any supplied map between the actual
graded Models induces an isomorphism in nonzero degree. It constructs no
missing comparison and asserts no degree-zero isomorphism.

With `[CompactSpace U]`, the actual coefficient diagram, Laurent seed, natural
contraction, and Bass telescope are defined over `Under R`, with arbitrary
coefficient arrows. No flatness, regularity, noetherian condition, or affineness
of `U` is imposed. The original forward Laurent self-track has a whole relative
contraction to the constant track of the same coefficient map.
[`FullOpenGradedLaurentContractionNaturality`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedLaurentContractionNaturality.lean)
retains the exact Model-square transports and independent comparison, action,
and structure coordinates, including the level-zero internal loop coordinate.

Cone inclusion and conjugation by the original source-leg cone null produce
`boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull`, a constructed
coefficient-natural whole null of the actual graded seed.
[`strictDiagramIterateNull`](../../Quillen/KTheory/Bass/StrictDiagramIterateNull.lean)
transports this same null through the existing Bass action and successor
isomorphisms. `boundedFlatAffineFullOpenGradedSectionBassTransition_stableMap_eq_zero`
therefore gives zero for every original finite transition at every `a : Under R`
and every `d : ℤ`.

The actual reduced telescope is
`boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor`.
[`boundedFlatAffineFullOpenGradedSectionBassTelescope_stableGroup_subsingleton`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenGradedSectionBassTelescope.lean)
gives vanishing of its stable group for every coefficient `a` and every integer
degree `d`. Each original stage inclusion factors on stable groups through its
zero next transition, and T1 finite-stage representability accounts for every
telescope class. Initial graded concentration and individual-stage vanishing
are not premises of this argument; no seed-null premise is supplied.

Writing `seedFine` and `seedGraded` for the two actual seed transformations,
and `q` for the fine-to-graded transformation, the exact equation
`seedFine ≫ B.map(q) = q ≫ seedGraded` is already proved in
[`FullOpenSectionBassSeedChangeWeak`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/FullOpenSectionBassSeedChangeWeak.lean).
The actual fine tower and telescope, and the induced finite/telescope q maps,
are constructed in `FullOpenSectionBassTower`, `FullOpenSectionBassTelescope`,
`FullOpenSectionBassGradingTower` and `FullOpenSectionBassGradingTelescope`.
The original r coefficient transformation and canonical whole localization
null are constructed; `FullOpenSectionConeStable` proves its initial cone descent
stable in every integer degree, including the honest degree-zero image quotient.
`FullOpenSectionBassRestrictionTower` iterates the same null and stable cone
comparison through every actual finite stage.

The original r seed square and canonical-null time-slice seed squares are proved
in `FullOpenSectionRestrictionSeed` and `FullOpenSectionGradingNullBassSeed`.
`FullOpenSectionBassRestrictionCofiber` retains the actual finite nulls and their
transition equations in the telescope. Its original cone descent is stable;
graded signed vanishing and genuine finite Model excision therefore make the
same r∞ stable in every integer degree. `FullOpenSectionBassLocalization`
composes the supported coarse cone comparison with this restriction, giving
the actual fine completion endpoint, the same whole-null fiber lift and the
original signed connecting identity. Pointwise fine section evaluation is
stable with its explicit universe lift and chosen-zero normalization;
evaluation through the seeds, iterates and telescope remains separate.
See the [TT localization roadmap](../development/TTLocalization.md).

For the ambient and supported ungraded telescopes above, fixed-degree
stabilization, classical negative identification, and full all-iterate comparison
with the original raw geometric towers remain open; the ambient negative-class
maps still have no bijectivity assertion. Native global C/F/G Models now have
their original Laurent seeds, canonical nulls, actual finite/telescope maps and
graded contraction. The original coarse-to-fine completion restriction is
stable for qcqs ambient schemes and quasi-compact opens. Basic global supported
completion now has the actual cone and same-null stable fiber comparison, with
its original signed boundary. Auxiliary-supported cofinality, honest K₀
exactness and the initial signed cone are proved. Their original supported
seeds, whole null-transition equations, finite/telescope maps and stable r_Z∞
now have strict builds, independent ordinary review and matching private-origin
foundation coverage. The native auxiliary fiber-forget localization now has
its actual union-support fiber, original seed/whole-null transfer and telescope
cone/fiber comparison, including the signed boundary. Final fine stability
requires compact P,Q,T and quasi-separated Q; the structural identities and
fiber-to-coarse stability need only the open immersion. Completed geometric
evaluation and classical nonconnective Thomason–Trobaugh identification remain
open.
The connective S-spectrum comparison does not settle these questions.
The conditional `Bass.TwoChartStableSpan` and `TwoChartStableSequence` now
provide the signed span quotient, natural all-degree Bass short exact row,
and actual cycles/image right-term identification. Their original plus
retraction and cone/collapse stability inputs still need native geometric
realization; recursive chart middle exactness and the original initial seed
are not proved by this structural interface.
See [Scope.md](../reference/Scope.md) for the global frontier and
[Architecture.md](../development/Architecture.md#trust-checks) for the foundation
audit boundary. Compilation and axiom audits concern encoded proofs; they do
not identify a spectral construction with an external classical theory.
