# Spectra and Bass groups

The library constructs the original iterated-S Ω-spectrum and identifies its
nonnegative stable groups additively with the original Waldhausen K-groups,
including K₀. Its negative stable groups vanish. Bass negative groups are
separately defined by polynomial-to-Laurent cokernels. A strict spectral Bass
tower realizes each recursive group as the bottom stable group of its finite
stage. For qcqs ambient schemes, the actual fine transition and inclusion at
stage `i` are isomorphisms in every degree `d ≥ -i`. The original negative
class maps are therefore natural isomorphisms to this fine telescope; the
supported result also assumes a quasi-compact removed open. Identification
with the original raw all-stage tower and classical nonconnective K-theory
remains separate.

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

The original coefficient Bass comparison now has scalar lifts for both
complete chart pauses.
[`BassMergedBoundarySimplex`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassMergedBoundarySimplex.lean)
places those whole chart surfaces and the prescribed Laurent bottom
L(r,cylinder(t,x)) in one common 44-simplex. All six reference/full-node
equalities are proved;
[`BassMergedScalarBoundary`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassMergedScalarBoundary.lean)
retains literal shared chart/bottom edges at their original speeds, including
degree-zero loops and independent structure time.
[`BassH0Native`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassH0Native.lean)
now evaluates the entire prescribed H0 cylinder surface in a separate actual
30-simplex, retaining both projection rectangles and their five full shared
nodes. All four original scalar edges, point and independent structure
coordinates are proved at every level, including zero. The joint H0/chart/bottom
family, whole H1/M faces and genuine six-face composition cylinder remain
separate. The generic
varying-family composition theorem supplies the actual realization-product
parameter and does not supply these remaining geometric faces.

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
[`TwoChartAdditive`](../../Quillen/KTheory/Bass/TwoChartAdditive.lean) proves that
the induced cokernel map preserves sums of natural transformations. The
contraction endofunctor is therefore additive and preserves split exact
sequences, without an additive coefficient functor or surjective chart
difference as an extra premise.

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

The separate original coefficient construction now has both actual mixed
fillers and the two-chart seed comparison. Its
[`CoefficientBassSeedIteration.stepMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassSeedIteration.lean)
is the objectwise first-to-second Bass map obtained by parameter looping the
chosen comparison-cone map. It preserves the original Laurent inclusion and
has formulas on the full cylinder and each output-loop time. The raw maps
still need their second-stage coefficient compatibility and higher coherence
before the strict diagram iteration machinery applies. The
[perfect-complex guide](PerfectComplexes.md) records these geometric interfaces.

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

## Finite Bass interchange and normalized stages

Write `B` for the actual strict Bass endofunctor, `C` for its unlooped
square cone, and `Ω` for parameter looping. The forward comparisons are

```text
κ : B(ΩF) → Ω(BF),
ρ : Pushout(Bf,Bg) → B(Pushout(f,g)),
χ : C(BS) → B(CS).
```

Here `S` is an actual strict natural square, and `C(S)` uses its original
constant-overlap comparison. [LoopStrength](../../Quillen/KTheory/Bass/LoopStrength.lean) constructs
`κ` from the Bass image of the original evaluation homotopy.
[LoopFactor](../../Quillen/KTheory/Bass/LoopFactor.lean) retains its actual cone-loop factorization
and double-loop transpose. [PushoutStrength](../../Quillen/KTheory/Bass/PushoutStrength.lean) constructs
the coefficient-natural forward `ρ`, preserving both inclusions and the whole
overlap cylinder. [PushoutCofiberSquare](../../Quillen/KTheory/Bass/PushoutCofiberSquare.lean) gives its
positive-direction cofiber square. [SquareConeStrength](../../Quillen/KTheory/Bass/SquareConeStrength.lean)
constructs `χ` from that square and the forward cofiber comparison, retaining
every cone time and source-null time slice. These definitions do not choose
inverse comparison maps.

The stability owners [LoopStable](../../Quillen/KTheory/Bass/LoopStable.lean),
[PushoutStable](../../Quillen/KTheory/Bass/PushoutStable.lean) and
[SquareConeStable](../../Quillen/KTheory/Bass/SquareConeStable.lean) discharge their point HEP, T1 and
all-point linear-growth hypotheses on actual finite Model stages. The
general growth statements keep their explicit topological assumptions.
For a growth offset `c`, the homotopy set at every point of level `n+c+2`
is subsingleton in each degree `k < n+2`. The general `κ` theorem requires
this bound, levelwise T1 and chosen-point HEP on `F`; the general `ρ` theorem
requires them on all three original diagrams. The finite `χ` theorem starts
with an actual strict square of Model diagrams.
[FiniteConeTopology](../../Quillen/KTheory/Bass/FiniteConeTopology.lean) also supplies those hypotheses for
finite unlooped cones followed by finite parameter loops of Model diagrams;
looping loses one degree per loop and retains arbitrary loop components.
The resulting cones are not assumed to carry a new Model structure.
[IteratedLoopStrength](../../Quillen/KTheory/Bass/IteratedLoopStrength.lean) iterates the same `κ` in a fixed
order. [NormalizedStageMap](../../Quillen/KTheory/Bass/NormalizedStageMap.lean) constructs stable maps
`B^i F → Ω^i C^i F` for genuine Model input, with the full functor-association
equalities retained as transports. A stable map at every stage does not
supply a map of the original seed towers.

The generic point-set interchange is in [PushoutInterchange](../../Quillen/Topology/Prespectrum/PushoutInterchange.lean) and
[PushoutInterchangeIso](../../Quillen/Topology/Prespectrum/PushoutInterchangeIso.lean): four strict corner squares give the
interchange of two reduced pushouts, with its actual transpose inverse and
nine-stratum naturality. It needs no local compactness, separation or point
HEP. [StrictSquarePushout](../../Quillen/Topology/Prespectrum/StrictSquarePushout.lean) and its Naturality/Cells owners extend
this to the original square cone.
[StrictDoubleSquareCone](../../Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean) and its Naturality/Cells owners give the
two totalizations of an actual four-dimensional strict arrow diagram `E`. Their
target is `totalFunctor.obj (coneSquare (comparisonMap E))`, and all sixteen cells exchange
whole parameter blocks, retaining four independent times in the deepest cell.
The geometric target transports and point-set involution are described in
the [perfect-complex guide](PerfectComplexes.md#geometric-double-cone-permutation).

[DoubleLaurentInclusion](../../Quillen/KTheory/Bass/DoubleLaurentInclusion.lean)
compares the geometric and cone-loop constructions after the displayed
double-Laurent inclusion. One face formula uses the actual opposite scheme
swap; the other retains the coefficient point without that swap. They
quantify the original based loop and its independent time. These restricted
identities establish neither equality nor inequality of the unrestricted
comparison maps. Their required whole-map relation remains separate.

The generic `loops`, `loopDiagram`, `loopDiagram_obj` and
`loopDiagram_postcomp` declarations live in
[LoopTranspose](../../Quillen/Topology/Prespectrum/LoopTranspose.lean), in the
native namespace `Quillen.LoopPrespectrum.FiniteParameterLooping`.
Finite parameter looping has generic evaluation, cyclic and reversal words in
[FiniteLoopWords](../../Quillen/Topology/Prespectrum/FiniteLoopWords.lean). These use the original double-loop
transpose. [FiniteLoopWordSlide](../../Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean) slides a new loop through
the specified reversal for any actual diagram map `A → ΩB`, retaining its
association transport. [FiniteLoopStrengthWords](../../Quillen/KTheory/Bass/FiniteLoopStrengthWords.lean) proves
that the cyclic and reversal words commute with the fixed iterated `κ`.
The permuted tuple contains the input-loop times; the residual Bass value and
its original loop time remain independent. These are the stated words, with
no general symmetric-group or cone-permutation coherence inferred. Reversal
changes the order of loop coordinates; it does not reverse each path's time.
No arithmetic sign on stable groups is inferred from these word identities.

[WholeSeedCospan](../../Quillen/KTheory/Bass/WholeSeedCospan.lean) preserves the complete original
null/unit/null word under a strict square map and a same-time unit-track
equation. [GeometricSeedCospan](../../Quillen/KTheory/Bass/GeometricSeedCospan.lean) supplies that equation for
the specified induced `bassTrack` by cancellation of the actual inverse
index swap. [GlobalSchemeLaurentTrack](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSchemeLaurentTrack.lean) instantiates the
source track with the actual forward Laurent unit on all global scheme
sections. This gives the finite common-target seed cospan, with its original
two half clocks and independent output-loop coordinate. It does not identify
the induced `bassTrack` with a separately chosen current-stage action.

The exact adjacent-stage statement in
[SchemeCurrentStageSquare](../../Quillen/KTheory/Bass/SchemeCurrentStageSquare.lean) is
`currentTransition_stageMap`. Its `currentTransition` applies
`seed (stageTrack A i)` and the specified association cast; its
`normalizedTransition` applies `loopMap i (seed (coneTrack A i))` and its own
association cast. The theorem intertwines these two maps via `stageMap`.
It does not identify `currentTransition` with
`strictDiagramTransition`, the `B^i(seed A)` transition used by the existing
global and coefficient telescopes. That equality, the required external
Laurent-action equivariance of the geometric permutation, the required
whole-map relation of geometric and cone-loop comparisons, fixed cone-word
compatibility and the resulting all-stage/telescope comparison remain
separate obligations.

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
between compact endpoints. The supported finite comparison is supplied by
`CoefficientSupportedNegativeBottomComparison` for an open immersion with
compact ambient scheme; it does not require the removed open to be compact.
`CoefficientSupportedNegativeForgetComparison` preserves the original
support-forgetting map at every finite bottom under the same hypotheses.

[`boundedFlatCoefficientAmbientBassNegativeMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassNegativeMap.lean)
then sends each original native class through that comparison and the original
stage inclusion into the ambient coefficient telescope. Its Laurent quotient
equation retains the successor-stage inclusion. The fine comparison below
proves this same map invertible for qcqs ambient schemes.
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
when both endpoints are compact. These naturality statements retain their
weaker hypotheses independently of the qcqs stabilization theorem below.

[`boundedFlatAffineSectionBassNegativeMap`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassNegativeMap.lean)
composes the finite bottom isomorphism with the original stage inclusion into
`boundedFlatAffineSectionBassTelescope`. It is coefficient-natural and retains
the Laurent quotient and next-stage cylinder formulas. This older ring-indexed
section construction is distinct from the specified native coefficient Model
rows in the fine theorem below; no identification of their telescope maps is
asserted here. Bass/telescope commutation and the tail map construct
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

## Fine stabilization and original localization groups

The fine theorem concerns the unchanged strict coefficient Model stages,
not a replacement raw tower. For qcqs `P.left`,
[`CoefficientBassFineRangeInvertibility`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassFineRangeInvertibility.lean)
proves `boundedFlatCoefficientAmbientBassTransition_isIso_of_le`: at every
stage `i : ℕ`, coefficient `a : Under R` and signed degree `d ≥ -i`, the
original transition induces an isomorphism. The equality case `d = -i` is
included. The proof uses the original connective seed, inter-stage spectral
row, recursive middle exactness and bottom chart exactness.

[`CoefficientBassFineTelescopeComparison`](../../Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassFineTelescopeComparison.lean)
proves the same range for the actual stage inclusion. Its
`boundedFlatCoefficientAmbientNegativeKTelescopeComparison i` is exactly the
original finite-bottom comparison followed by that inclusion, and preserves
the original Laurent quotient. `CoefficientBassConnectiveTelescopeComparison`
uses the original connective evaluation and stage-zero inclusion. Both are
natural isomorphisms on the full coefficient category.

For an open immersion `f : P ⟶ Q` with compact `P.left` and qcqs `Q.left`,
`CoefficientSupportedFineRangeInvertibility`,
`CoefficientSupportedFineTelescopeComparison` and
`CoefficientSupportedConnectiveTelescopeComparison` give the same statements
for the actual supported stages and telescope. The original negative and
connective degree-zero comparison maps agree literally.
`CoefficientSupportedNegativeTelescopeForget` proves the whole original
support-forgetting square, retaining its recursive Laurent representative.

`CoefficientFullOpenBassRestriction` identifies the full-open fine Model row,
Laurent action, seed and telescope definitionally with the ambient construction
on the open scheme. For an open immersion, the constructed telescope
localization map is the original scheme restriction on every cylinder; this
identity itself needs no compactness premise.
`CoefficientNegativeLocalizationExactness` and
`CoefficientNegativeLocalizationBoundary` then transport the same-null signed
cone sequence through the original ambient/supported isomorphisms. At the
identity coefficient, `Bass.SupportedLocalizationExactness` and
`Bass.SupportedLocalizationBoundary` give the original open-pair sequence in
every nonpositive degree under compactness of the removed open and qcqs of
the ambient scheme. Restriction and support forgetting are the original maps.
The positive geometric K₁-to-supported-K₀ boundary joins this sequence by
exactness at the literal K₀ groups. Equality of that boundary with the fine
boundary and arbitrary-pair pullback naturality of the transported boundary
remain separate obligations. See [PerfectComplexes.md](PerfectComplexes.md#original-nonpositive-localization-sequence)
for the exact group row.

The fine stabilization and group identifications do not construct the original
raw all-stage geometric tower. The actual raw first stage has whole identity
and composition laws in `CoefficientBassUnitCubeConsumers` and
`MWholeCubeConsumers`. Parameterized pushout/cone descent, its whole-family
recovery, and the constructed Laurent and polynomial native cells retain
specified fillers and clocks. The complete compatible overlap four-cube,
its eight faces, their whole intersections including the original half-height
midpoint, and all quotient attachments must still be supplied before
actual second-projection pasting and coherent raw iteration. These raw
interfaces are described in [PerfectComplexes.md](PerfectComplexes.md#raw-identity-and-second-stage-coherence).

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

For the fine ambient and supported telescopes, the original-group
identifications and finite-stage ranges are now supplied under the hypotheses
above. Full all-iterate comparison with the original raw geometric towers and
classical nonconnective identification remain open. Native global C/F/G Models now have
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
retraction and cone/collapse stability inputs are realized for the actual
finite coefficient Models by `CoefficientTwoChartStableSequence`. The original
ambient and supported middle rows, connective seeds and full fine transition
ranges have their additional geometric proofs; the generic structural
interface alone does not imply them.
See [Scope.md](../reference/Scope.md) for the global frontier and
[Architecture.md](../development/Architecture.md#trust-checks) for the foundation
audit boundary. Compilation and axiom audits concern encoded proofs; they do
not identify a spectral construction with an external classical theory.
