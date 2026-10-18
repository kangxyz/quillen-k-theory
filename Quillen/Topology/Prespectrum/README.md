# Prespectra, stable fibers and telescopes

Generic spectral declarations use `Quillen.LoopPrespectrum`, with telescope
interfaces in its nested `Telescope` namespace. The constructions below retain
original structure coordinates, whole homotopies and integer stable degrees.

The original iterated-S connective spectrum and its K-group comparisons belong
to [iterated S-construction](../../Waldhausen/SConstruction/Iterated/README.md).
[Strict spectral Bass diagrams](../../KTheory/Bass/README.md) own their ring
application; [affine perfect complexes](../../AlgebraicGeometry/PerfectComplexes/Affine/README.md)
and [geometric localization](../../AlgebraicGeometry/PerfectComplexes/Localization.md)
own the scheme and open-localization conclusions, with their qcqs and
quasi-compact-open hypotheses. Those guides retain finite-stage bounds,
negative-class maps and the distinction from classical nonconnective K-theory.

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.Prespectrum.StableLocalization`](StableLocalization.lean) | Coherent-homotopy quotient and categorical stable localization |
| [`Topology.Prespectrum.FiberSequence`](FiberSequence.lean) | Signed stable long exact sequence of actual path-space fibers; Actual path-space fibers and signed stable long exact sequence |
| [`Topology.Prespectrum.ConeLinearExcision`](ConeLinearExcision.lean) | Specified cone-fiber comparison under growth and point HEP; Cone-fiber excision with explicit growth and point HEP |
| [`Topology.Prespectrum.TelescopeStableColimit`](TelescopeStableColimit.lean) | T1 telescope stable-colimit comparison |
| [`Topology.Prespectrum.LoopTailReplacementFiberEquivalence`](LoopTailReplacementFiberEquivalence.lean) | Ω replacement and fiber comparison; Ω replacement and its actual fiber comparison |
| [`Topology.Prespectrum.PushoutConeFamily`](PushoutConeFamily.lean), [`Topology.Prespectrum.PushoutConeFamilyRecovery`](PushoutConeFamilyRecovery.lean) | Locally compact parameter descent through the original pushout and reduced cone, strict restriction/looping and recovery of entire chosen families |
| [`Topology.Prespectrum.LoopTranspose`](LoopTranspose.lean) | `Quillen.LoopPrespectrum.FiniteParameterLooping.loops`, `loopDiagram` and their object/association equations |
| [`Topology.Prespectrum.FiniteLoopWords`](FiniteLoopWords.lean), `FiniteLoopWordSlide` | Finite loop evaluation, cyclic/reversal natural isomorphisms and the new-loop slide |
| [`Topology.Prespectrum.StrictSquarePushout`](StrictSquarePushout.lean), `StrictDoubleSquareCone` and their Naturality/Cells leaves | Actual square-cone/pushout and four-dimensional double-square isomorphisms and quotient formulas |
| [`Topology.Prespectrum.NativeParameterEvaluation`](NativeParameterEvaluation.lean) | Conditional whole-value `PathLift`/`HomotopyLift` operation laws for an arbitrary evaluator |
| [`Topology.Prespectrum.DiagramNullHomotopy`](DiagramNullHomotopy.lean) | Coefficient-natural whole null tracks and original isomorphism transport |
| [`Topology.Prespectrum.StrictSquareCofiberDescent`](StrictSquareCofiberDescent.lean) | Actual looped-cone/cofiber comparison and descent equations |
| [`Topology.Prespectrum.TelescopeConeDescentStable`](TelescopeConeDescentStable.lean) | Compatible null descent, stable comparison, and signed telescope boundary |

## Remaining comparisons

- General stable cofiber excision, the remaining quotient homotopy-invariance questions, and a standard stable model structure or triangulation for the categorical localization.

## Declaration namespaces

The connective declaration namespace is `Quillen.Waldhausen.IteratedS`.
Generic spectral declarations use `Quillen.LoopPrespectrum`; its telescope
interfaces use the nested namespace `Telescope`. Group-level ring recursion
uses `Quillen.Bass`, strict spectral diagrams use `Quillen.KTheory.Bass`, and
the affine geometric spectrum constructions use `Quillen.PerfectComplexes`.

## Stable fibers and categorical localization

`parameterLooping` transposes the loop and structure coordinates. Its signed
comparison `parameterStableHomotopyIso E d` identifies degree `d` with degree
`d+1` of `E`. The stage formula has sign `(-1)^n` and tail offset
`parameterStableOffset d`, equal to one for `d < 0` and zero otherwise.
This is the parameter-correct construction in
[`StableShift`](StableShift.lean); it is
distinct from `looping`.

For every map `f : E ⟶ F`, `homotopyFiber f` is an actual path-space
prespectrum. [`stableFiberLongExactSequence`](FiberSequence.lean)
supplies the three recurring exactness positions in

```text
π^st_(d+1)(E) → π^st_(d+1)(F) → π^st_d(Fib f) → π^st_d(E) → π^st_d(F).
```

The boundary is the inverse signed parameter-loop shift followed by the
literal loop-to-fiber inclusion. Whole coherent based squares supply fiber
maps and boundary naturality. Ω inputs give an Ω fiber, including the component
conditions. Vanishing of every integer fiber group detects stable equivalence.
For connective inputs, [`stableFiber_neg_subsingleton_of_connective`](FiberConnectivity.lean)
requires surjectivity of the actual degree-zero map.

[`StableLocalization`](StableLocalization.lean)
first forms `CoherentHomotopyCategory` by quotienting whole coherent based
homotopies, then inverts maps inducing isomorphisms in every integer stable
degree. `localizedStableHomotopyFunctor` retains the original stable groups,
and `stableLocalizationLift` supplies the universal lift for a functor that
respects those homotopies and inverts stable equivalences.
`localizedSpectrumMap` has literal identity/composition laws and weak-transformation
invariance. `localizedSpectrumMapIso` requires bijectivity of every original
`KMap`, including K₀. This categorical localization does not supply a standard
stable model structure, triangulation, fullness, or continuous inverses.

## Natural null tracks and cofiber descent

For strict diagrams `F,G,K : C ⥤ LoopPrespectrum` and transformations
`a : F ⟶ G`, `b : G ⟶ K`,
[`DiagramNullHomotopy`](DiagramNullHomotopy.lean)
records whole based nullhomotopies of `a.app X ≫ b.app X` and their coefficient
naturality at the same null time. Transport through specified diagram
isomorphisms and their two commuting arrow squares retains the actual
pre/postcomposition maps and unchanged time.
`mappingConeDiagram` and `mappingConeDescTransformation` give the corresponding
strict cone diagram and natural descent. `mappingConeDesc_naturality` requires
the actual target square and equality of the supplied whole null tracks.

`StrictSquare.sourceNullHomotopy` retains the original source-leg cone cylinder.
The looped-cone/cofiber comparison and its descent equation in
[`StrictSquareCofiberDescent`](StrictSquareCofiberDescent.lean)
retain the four original corners and their whole zero-composite homotopy.
Stable equivalence of this comparison keeps the two cone-fiber excision
premises explicit. For individual spectra `E₀,E₁,E₂`, maps `f : E₀ ⟶ E₁`,
`g : E₁ ⟶ E₂`, and a supplied whole null of `f ≫ g`, the degree-zero criterion
[`mappingConeDesc_stable_zero_bijective`](ConeDescZeroComparison.lean)
requires cone-fiber excision for `f`, vanishing of `π^st_(-1)(E₀)`, exactness of
`π^st_0(E₀) → π^st_0(E₁) → π^st_0(E₂)`, and surjectivity of the latter map.
Its conclusion is bijectivity in degree zero.

Compatible stage null tracks descend through the original telescope cylinders
with null time and cylinder height independent. `Telescope.coneIso_desc`
identifies that descent with the original cone/telescope interchange.
[`TelescopeConeDescentStable`](TelescopeConeDescentStable.lean)
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
[`TelescopeRepresentability`](TelescopeRepresentability.lean)
and [`TelescopeStableColimit`](TelescopeStableColimit.lean).
The reduced telescope is T1 and its original stage inclusions are closed embeddings.

Strict and track-defined telescope maps retain their respective coefficient
squares or whole cylinders. Identity/composition homotopies fix each original
stage without a T1 premise; higher coherence between them is separate.
Stagewise stable equivalences descend under T1, while
[`TelescopeStableExactness`](TelescopeStableExactness.lean)
still requires the displayed stagewise exactness. Strict cone/pushout interchange
needs neither separation nor point HEP. Parameter-loop interchange is a stable
equivalence for T1 stages, retaining loop time and cylinder height.

The original stabilization `E → looping(tail E)` is an all-integer stable
equivalence. Its iterated telescope `loopTailReplacement E` is Ω under
levelwise T1, with complete weak structure maps and target-component coverage.
`loopTailReplacementFunctor` is a strict functor without T1; under source/target
T1 its natural unit is stable and it preserves and reflects stable equivalences.
[`LoopTailReplacementFiberEquivalence`](LoopTailReplacementFiberEquivalence.lean)
gives an actual stable fiber comparison that is completely weak at every level.
For genuine Ω-prespectra, [`isStableEquivalence_iff_levelwise_of_isOmega`](StableOmegaLevelDetection.lean)
requires neither T1 nor connectedness. Thus the unit is levelwise weak on Ω T1
inputs. Levelwise weakness on arbitrary inputs and cofiber preservation are
separate claims.

## Polynomial-span identity

[`PushoutIdentityFromUnitSquare`](PushoutIdentityFromUnitSquare.lean)
descends a supplied identical-leg unit square to a whole identity homotopy of
the actual reduced polynomial span. Both original chart tracks and every
cylinder value are preserved; constant pieces are contracted within the
relative comparison before the native three-side square descent. The native
polynomial producer supplies that square in `CoefficientPolynomialSpanUnit`.
This span identity does not supply the missing whole Bass comparison identity
or coherent raw iteration.


## Strict double-square geometry

[StrictDoubleSquareCone](StrictDoubleSquareCone.lean) constructs the strict
four-dimensional double-square totalization. Its quotient cells and inverse
naturality are point-set statements. The geometric twice-cone permutation and
finite-word action belong to the [Bass family](../../KTheory/Bass/README.md);
external-factor braid and track transport belong to the
[scheme-product guide](../../Aglib/AlgebraicGeometry/Products/README.md).
The four-dimensional permutation supplies no older raw overlap four-cube with
prescribed faces and earlier fillers; that separate route remains in the
[geometric localization guide](../../AlgebraicGeometry/PerfectComplexes/Localization.md).
