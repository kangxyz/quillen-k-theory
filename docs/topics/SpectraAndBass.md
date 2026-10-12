# Spectra and Bass groups

The library constructs the original iterated-S Ω-spectrum and identifies its
nonnegative stable groups additively with the original Waldhausen K-groups,
including K₀. Its negative stable groups vanish. Bass negative groups are
separately defined by polynomial-to-Laurent cokernels. A strict spectral Bass
tower realizes each recursive group as the bottom stable group of its finite
stage and gives natural maps to the actual telescope. Bijectivity of these
telescope maps and identification with classical nonconnective K-theory remain
separate comparisons.

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
| `Topology.Prespectrum.TelescopeStableColimit` | T1 telescope stable-colimit comparison |
| `Topology.Prespectrum.LoopTailReplacementFiberEquivalence` | Ω replacement and its actual fiber comparison |
| `KTheory.Bass.StrictRingDiagram` | Bass endofunctor and transitions for a supplied strict seed |
| `AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups` | Ring-indexed cokernel recursion |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassNegativeMap` | Finite-stage bottom comparison and natural telescope class map |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescopeSelfMap` | Stable map from the ambient telescope to its Bass image |

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

The raw spectral step `affineBassStep R` is the parameter-looped cone of the
actual two-polynomial-chart comparison to the Laurent corner.
[`affineBassTransition`](../../Quillen/AlgebraicGeometry/PerfectComplexes/Affine/BassStep.lean)
uses the original Laurent-unit track and cone nullhomotopy. The bounded-flat
and perfect raw steps have the original comparison
`boundedFlatPerfectGeometricBassStepMap`, completely weak at positive levels
and stable in every integer degree.

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

Fixed-degree stabilization, bijectivity of the negative-class maps, classical
telescope negative identification, and full all-iterate geometric comparison
remain open. The connective S-spectrum comparison does not settle them.
See [Scope.md](../reference/Scope.md) for the global frontier and
[Architecture.md](../development/Architecture.md#trust-checks) for the foundation
audit boundary. Compilation and axiom audits concern encoded proofs; they do
not identify a spectral construction with an external classical theory.
