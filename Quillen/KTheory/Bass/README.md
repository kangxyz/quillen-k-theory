# Bass contraction, finite interchange and telescope maps

## Spectral and Bass entrypoints

| Import after `Quillen.` | Interface |
| --- | --- |
| `KTheory.Bass.StrictRingDiagram` | Strict spectral Bass endofunctor and supplied-seed transitions |
| `KTheory.Bass.TwoChartAdditive` | Additive two-chart contraction and preservation of split exact sequences |
| `KTheory.Bass.StrictLaurentSeedStable` | Transparent `Track.SeedStableFactorization` and `SeedStableFormula` for an actual track and supplied seed |

The [iterated S-spectrum guide](../../Waldhausen/SConstruction/Iterated/README.md)
owns the original connective groups. This family distinguishes recursive Bass
cokernels, finite-stage bottom groups and telescope maps. The
[perfect-complex guide](../../AlgebraicGeometry/PerfectComplexes/README.md)
owns the geometric seed and support/localization comparisons. A generic diagram
interface, finite-stage isomorphism, or stable self-comparison does not supply
an additional rectification or telescope-identification theorem.

## Global sections and finite Bass interchange

| Import after `Quillen.` | Principal interface |
| --- | --- |
| `KTheory.Bass.SectionChangeIndexStable` | `restrictionModel_iterate_isStableEquivalence` for the small finite Model interface |
| `KTheory.Bass.LoopStrength`, `LoopFactor`, `LoopStable` | Actual `κ : B(ΩF) → Ω(BF)`, its cone-loop/transpose factorization and finite Model stability |
| `KTheory.Bass.PushoutStrength`, `PushoutCofiberSquare`, `PushoutStable` | Forward `rho`, whole overlap formula, positive cofiber square and finite Model stability |
| `KTheory.Bass.SquareConeStrength`, `SquareConeStable` | Forward `chi`, cone/source-null formulas and `modelSquare_chi_isStableEquivalence` |
| `KTheory.Bass.NormalizedStageMap`, `IteratedLoopStrength` | Fixed-order iterated `κ` and stable `stageMap : B^i F → Ω^i C^i F` for Model input |
| `KTheory.Bass.FiniteLoopStrengthWords` | Fixed loop words through actual iterated strength, retaining the residual Bass loop |
| `KTheory.Bass.GeometricConeTarget`, `GeometricConeCells`, `GeometricConeInvolution` and Naturality/SchemeNaturality leaves | Actual geometric two-cone `permutation`, all sixteen cells, involution and natural isomorphisms |
| `KTheory.Bass.DoubleLaurentInclusion` | Geometric and cone-loop value equations after the displayed double inclusion, with the original swap distinction |
| `KTheory.Bass.WholeSeedCospan`, `GeometricSeedCospan` | Whole null/unit/null seed word and finite cospan for the specified induced `bassTrack` |
| `KTheory.Bass.SchemeCurrentStageSquare` | `currentTransition_stageMap` for the explicitly defined current and normalized seed transitions |
| `KTheory.Bass.GeometricConeAction`, `GeometricConeFixedWordAction`, `SchemeTwistedConjugacy` | Actual `permutation_equivariant`, finite-word equivariance, `wordAt_seed_square` and `twisted_adjacent` |
| `KTheory.Bass.GeometricChiPermutation`, `SchemeSeedRotation`, `SchemeIteratedSeedTransition` | Whole geometric chi factorization, original local seed rotation and `originalTransition_stageMap` for every `B^i(seed)` transition |
| `KTheory.Bass.SchemeCurrentStageTelescope`, `SchemeTwistedTelescope`, `SchemeIteratedSeedTelescope` | Actual stable zigzag `I → T ← N ← C`, preserving original stage inclusions and cylinders for Model input |

## Geometric double-cone permutation

[GeometricSquareInterchange](GeometricSquareInterchange.lean) uses the four actual
independent-variable swaps in the arbitrary-scheme index square.
[GeometricSquareInvertibility](GeometricSquareInvertibility.lean) identifies its original
index-induced square map as an isomorphism. The forward strength maps retain
their separate finite stable-equivalence statements. The actual two-cone target transport is in
[GeometricConeTarget](GeometricConeTarget.lean), and
[GeometricConeCells](GeometricConeCells.lean) gives all sixteen formulas for its
point-set permutation. The two whole parameter blocks are exchanged; the
coefficient point uses the specified opposite swap for its actual pair of
factors, with the literal identity on an empty factor. In the deepest
overlap/overlap cell the coefficient point is unchanged and `r,s,t,v` remain
independent, as do any loop and structure times.
[GeometricConeInvolution](GeometricConeInvolution.lean) proves involutivity, while
[GeometricConeNaturality](GeometricConeNaturality.lean) and
[GeometricConeSchemeNaturality](GeometricConeSchemeNaturality.lean) give naturality in the
spectrum diagram and scheme map on those same cells.

## Bass cokernels and the original Laurent seed

For `R : CommRingCat.{u}`, the additive Bass contraction is the cokernel of
`F(R[T]) ⊕ F(R[T]) → F(R[T,T⁻¹])`, with map `(a,b) ↦ F(plus)(a) - F(minus)(b)`.
[`contraction`](Contraction.lean) retains this
Laurent quotient, its two-chart kernel criterion, exactness, and unique descent.
`Quillen.Bass.negativeKFunctor i` starts with additive homotopical
`PerfectK (Spec R) 0`; its natural-number index `i` denotes degree `-i`.
`Quillen.PerfectComplexes.Bass.negativeKFunctor` and
`Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor` start with the scheme
and supported original K₀, respectively.
Scheme pullback uses quasi-compact schemes, and supported recursion requires
only quasi-compactness of the ambient base, with arbitrary vanishing open.
[`affineSchemeNegativeKIso`](../../AlgebraicGeometry/PerfectComplexes/Affine/BassSchemeComparison.lean)
compares affine and scheme recursions naturally in
every nonpositive degree, with literal original K₀ at zero.
[`RightExactness`](RightExactness.lean) and
[`IterationExactness`](IterationExactness.lean)
preserve pointwise right exact sequences and cokernels through contraction
and every ring-indexed iterate. They supply no negative localization boundary.
[`TwoChartAdditive`](TwoChartAdditive.lean) proves that
the induced cokernel map preserves sums of natural transformations. The
contraction endofunctor is therefore additive and preserves split exact
sequences, without an additive coefficient functor or surjective chart
difference as an extra premise.

## Finite Bass interchange and normalized stages

Write `B` for the actual strict Bass endofunctor, `C` for its unlooped
square cone, and `Ω` for parameter looping. The forward comparisons are

```text
κ : B(ΩF) → Ω(BF),
ρ : Pushout(Bf,Bg) → B(Pushout(f,g)),
χ : C(BS) → B(CS).
```

Here `S` is an actual strict natural square, and `C(S)` uses its original
constant-overlap comparison. [LoopStrength](LoopStrength.lean) constructs
`κ` from the Bass image of the original evaluation homotopy.
[LoopFactor](LoopFactor.lean) retains its actual cone-loop factorization
and double-loop transpose. [PushoutStrength](PushoutStrength.lean) constructs
the coefficient-natural forward `ρ`, preserving both inclusions and the whole
overlap cylinder. [PushoutCofiberSquare](PushoutCofiberSquare.lean) gives its
positive-direction cofiber square. [SquareConeStrength](SquareConeStrength.lean)
constructs `χ` from that square and the forward cofiber comparison, retaining
every cone time and source-null time slice. These definitions do not choose
inverse comparison maps.

The stability owners [LoopStable](LoopStable.lean),
[PushoutStable](PushoutStable.lean) and
[SquareConeStable](SquareConeStable.lean) discharge their point HEP, T1 and
all-point linear-growth hypotheses on actual finite Model stages. The
general growth statements keep their explicit topological assumptions.
For a growth offset `c`, the homotopy set at every point of level `n+c+2`
is subsingleton in each degree `k < n+2`. The general `κ` theorem requires
this bound, levelwise T1 and chosen-point HEP on `F`; the general `ρ` theorem
requires them on all three original diagrams. The finite `χ` theorem starts
with an actual strict square of Model diagrams.
[FiniteConeTopology](FiniteConeTopology.lean) also supplies those hypotheses for
finite unlooped cones followed by finite parameter loops of Model diagrams;
looping loses one degree per loop and retains arbitrary loop components.
The resulting cones are not assumed to carry a new Model structure.
[IteratedLoopStrength](IteratedLoopStrength.lean) iterates the same `κ` in a fixed
order. [NormalizedStageMap](NormalizedStageMap.lean) constructs stable maps
`B^i F → Ω^i C^i F` for genuine Model input, with the full functor-association
equalities retained as transports. A stable map at every stage does not
supply a map of the original seed towers.

The generic point-set interchange is in [PushoutInterchange](../../Topology/Prespectrum/PushoutInterchange.lean) and
[PushoutInterchangeIso](../../Topology/Prespectrum/PushoutInterchangeIso.lean): four strict corner squares give the
interchange of two reduced pushouts, with its actual transpose inverse and
nine-stratum naturality. It needs no local compactness, separation or point
HEP. [StrictSquarePushout](../../Topology/Prespectrum/StrictSquarePushout.lean) and its Naturality/Cells owners extend
this to the original square cone.
[StrictDoubleSquareCone](../../Topology/Prespectrum/StrictDoubleSquareCone.lean) and its Naturality/Cells owners give the
two totalizations of an actual four-dimensional strict arrow diagram `E`. Their
target is `totalFunctor.obj (coneSquare (comparisonMap E))`, and all sixteen cells exchange
whole parameter blocks, retaining four independent times in the deepest cell.
The geometric target transports and point-set involution are described in
the [perfect-complex guide](README.md#geometric-double-cone-permutation).

[DoubleLaurentInclusion](DoubleLaurentInclusion.lean)
compares the geometric and cone-loop constructions after the displayed
double-Laurent inclusion. One face formula uses the actual opposite scheme
swap; the other retains the coefficient point without that swap. They
quantify the original based loop and its independent time. These restricted
identities establish neither equality nor inequality of the unrestricted
comparison maps. The whole relation needed by the new iteration route is
proved separately in
[GeometricChiPermutation](GeometricChiPermutation.lean):
`GeometricChiPermutation.comparison` factors the actual `chiGeom` through
`LoopFactor.coneStrength` followed by the parameter loop of the genuine
geometric permutation.

The generic `loops`, `loopDiagram`, `loopDiagram_obj` and
`loopDiagram_postcomp` declarations live in
[LoopTranspose](../../Topology/Prespectrum/LoopTranspose.lean), in the
native namespace `Quillen.LoopPrespectrum.FiniteParameterLooping`.
Finite parameter looping has generic evaluation, cyclic and reversal words in
[FiniteLoopWords](../../Topology/Prespectrum/FiniteLoopWords.lean). These use the original double-loop
transpose. [FiniteLoopWordSlide](../../Topology/Prespectrum/FiniteLoopWordSlide.lean) slides a new loop through
the specified reversal for any actual diagram map `A → ΩB`, retaining its
association transport. [FiniteLoopStrengthWords](FiniteLoopStrengthWords.lean) proves
that the cyclic and reversal words commute with the fixed iterated `κ`.
The permuted tuple contains the input-loop times; the residual Bass value and
its original loop time remain independent. These are the stated words, with
no general symmetric-group or cone-permutation coherence inferred. Reversal
changes the order of loop coordinates; it does not reverse each path's time.
No arithmetic sign on stable groups is inferred from these word identities.

[WholeSeedCospan](WholeSeedCospan.lean) preserves the complete original
null/unit/null word under a strict square map and a same-time unit-track
equation. [GeometricSeedCospan](GeometricSeedCospan.lean) supplies that equation for
the specified induced `bassTrack` by cancellation of the actual inverse
index swap. [GlobalSchemeLaurentTrack](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSchemeLaurentTrack.lean) instantiates the
source track with the actual forward Laurent unit on all global scheme
sections. This gives the finite common-target seed cospan, with its original
two half clocks and independent output-loop coordinate. It does not identify
the induced `bassTrack` with a separately chosen current-stage action.

The exact adjacent-stage statement in
[SchemeCurrentStageSquare](SchemeCurrentStageSquare.lean) is
`currentTransition_stageMap`. Its `currentTransition` applies
`seed (stageTrack A i)` and the specified association cast; its
`normalizedTransition` applies `loopMap i (seed (coneTrack A i))` and its own
association cast. The theorem intertwines these two maps via `stageMap`.
The original `strictDiagramTransition = B^i(seed A)` has a separate
comparison to the twisted-normalized transitions below. The all-stage route
therefore retains both transition definitions rather than identifying them.

## Current-stage and iterated-seed telescopes

For a scheme-indexed Model diagram `M`, put `F = M ⋙ prespectrumFunctor`
and let `A` be its original Laurent track. Write `C`, `N`, `T` and `I` for
the following actual telescopes. These are local telescope labels; the unlooped cone functor is described in the preceding
section.

| Telescope | Objects and transitions | Comparison owner |
| --- | --- | --- |
| `C = currentTelescope A` | Original finite Bass objects with the scalar seed formed at each current stage | [SchemeCurrentStageTelescope](SchemeCurrentStageTelescope.lean) |
| `N = normalizedTelescope A` | The i-fold parameter loops of the i-fold unlooped cone, with the current cone seed and its association cast | [SchemeCurrentStageTelescope](SchemeCurrentStageTelescope.lean) |
| `T = twistedTelescope A` | The same normalized objects with the prescribed cyclic/insertion-word transitions | [SchemeTwistedTelescope](SchemeTwistedTelescope.lean) |
| `I = iteratedTelescope A` | Original finite Bass objects with `strictDiagramTransition squareFunctor (seed A)`, namely `B^i(seed A)` | [SchemeIteratedInputNull](SchemeIteratedInputNull.lean) |

The natural maps form `I → T ← N ← C`. In the native namespace
`Quillen.KTheory.Bass.SchemeNaturalSeed`, `telescopeMap` gives `C → N`
and `conjugacyTelescopeMap` gives `N → T`.
`Quillen.KTheory.Bass.SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap`
gives `I → T`. Each owner proves the actual cylinder and inclusion equations;
its `model_*_stable` theorem gives stability at every scheme parameter for
genuine Model input. Finite Model topology discharges the T1 and growth
conditions. No new Model structure on normalized cones is assumed.

The local geometric input is now explicit.
[GeometricConeAction](GeometricConeAction.lean) proves
whole scalar-action equivariance of the original two-cone permutation.
[GeometricConeFixedWords](GeometricConeFixedWords.lean)
instantiates the general
[fixed-word candidate](../../Aglib/CategoryTheory/Endofunctor/README.md),
and [GeometricConeFixedWordAction](GeometricConeFixedWordAction.lean)
proves equivariance of those specified words.
[SchemeTwistedConjugacy](SchemeTwistedConjugacy.lean)
supplies `wordAt_seed_square` and `twisted_adjacent`.
[SchemeSeedRotation](SchemeSeedRotation.lean) uses
the whole chi factorization and original seed cospan; then
`Quillen.KTheory.Bass.SchemeIteratedSeedTransition.originalTransition_stageMap`
in [SchemeIteratedSeedTransition](SchemeIteratedSeedTransition.lean)
proves every original adjacent square against the unchanged finite `stageMap`.
The rotation-only induction helper retains its conditional statement; this
geometric specialization supplies its local inputs.

[SchemeInputTelescope](SchemeInputTelescope.lean),
[SchemeTwistedInputMaps](SchemeTwistedInputMaps.lean)
and [SchemeInputNull](SchemeInputNull.lean), with
their twisted/iterated null owners, preserve actual input maps and every time
slice of a supplied equivariant whole null. The
[perfect-complex application](../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md#native-current-stage-full-open-localization)
constructs these equivariance equations for the original supported/full-open
null and proves the integer-base current-stage fiber lift stable under its
open-immersion, compactness and quasi-separatedness hypotheses. That result remains separate from classical TT identification and the older
raw O-cell route. [Recorded evidence](../../../docs/evidence/README.md#tt-source-and-validation-records)
is maintained with the global documentation.
